import Langlands.BruhatTits.SpecialCompact.StrictChamberPowerBasis
import Langlands.BruhatTits.SpecialCompact.StandardLeviWeakChamberTransport
import Langlands.Geometry.Building.StandardLeviStrictUniformizerProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Basis members do not depend on the compatible split component

For two compatible split components of the same standard Levi `M_J`, the cocharacters of
either component, read in the fixed maximal split torus `S`, are exactly the cocharacters of `S`
annihilating the roots in `J`. Hence the images in `G(F)` of their common-uniformizer chambers
`C_A`, `C_A^+`, `C_A^{++}` and `C_A(ε)` agree (each inclusion is proved below, and the two
components play symmetric roles), and the standard-parabolic basis-member property passes from
one component to the other.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The normalization, contraction, exhaustion, containment and cofinality clauses quantify over
the points of the chamber sets only, so they pass to smaller chamber sets. -/
theorem ContractionAndCofinality.mono {K M N Nbar : Subgroup H}
    {CA CA' CAplus CAplus' CAstrict CAstrict' : Set H} {CAeps CAeps' : ℝ → Set H}
    (h : ContractionAndCofinality K M N Nbar CA' CAplus' CAstrict' CAeps')
    (hCA : CA ⊆ CA') (hplus : CAplus ⊆ CAplus') (hstrict : CAstrict ⊆ CAstrict')
    (heps : ∀ ε, CAeps ε ⊆ CAeps' ε) :
    ContractionAndCofinality K M N Nbar CA CAplus CAstrict CAeps := by
  obtain ⟨h1, h2, h3, ⟨h4N, h4Nbar⟩, h5, ⟨h6N, h6Nbar⟩⟩ := h
  refine ⟨fun m hm => h1 m (hCA hm), fun m hm => h2 m (hplus hm),
    fun m hm => h3 m (hstrict hm), ⟨fun Γ hΓ => ?_, fun Γ hΓ => ?_⟩,
    fun m hm => h5 m (hstrict hm), ⟨fun Γ hΓ => ?_, fun Γ hΓ => ?_⟩⟩
  · obtain ⟨ε, hε, hΓε⟩ := h4N Γ hΓ
    exact ⟨ε, hε, fun m hm => hΓε m (heps ε hm)⟩
  · obtain ⟨ε, hε, hΓε⟩ := h4Nbar Γ hΓ
    exact ⟨ε, hε, fun m hm => hΓε m (heps ε hm)⟩
  · obtain ⟨ε, hε, hΓε⟩ := h6N Γ hΓ
    exact ⟨ε, hε, fun m hm => hΓε m (heps ε hm)⟩
  · obtain ⟨ε, hε, hΓε⟩ := h6Nbar Γ hΓ
    exact ⟨ε, hε, fun m hm => hΓε m (heps ε hm)⟩

end Groups

section Rational

variable {F : Type u} [Field F]
  {S A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp} {q' : A'.toGrp ⟶ S.toGrp}

/-- Every cocharacter of one compatible split component of `M_J`, read in `S`, is a cocharacter
of any other compatible split component of `M_J`, read in `S`. -/
theorem IsCompatibleStandardSplitComponent.exists_cocharacter_eq
    [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (c : cocharacterLattice A) :
    ∃ c' : cocharacterLattice A',
      cocharacterMapInt (Additive.ofMul q') c' = cocharacterMapInt (Additive.ofMul q) c :=
  hA'.exists_cocharacter_lift_of_annihilates i ν hi
    (standardCocharacter F G hG S i hi ν hν J hJ).1 _
    (fun _ hα => hA.pairing_eq_zero i ν hG hJ c hα)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [IsAffineHom G.X.hom] in
/-- The image in `G(F)` of the common-uniformizer value of a component cocharacter depends only on
that cocharacter read in `S`. -/
theorem map_comp_latticeSection_eq {c : cocharacterLattice A} {c' : cocharacterLattice A'}
    (hcc : cocharacterMapInt (Additive.ofMul q') c' = cocharacterMapInt (Additive.ofMul q) c) :
    rationalPoints.map (q' ≫ i)
        (CocharacterUniformizer.latticeSection F A' (Multiplicative.ofAdd c')) =
      rationalPoints.map (q ≫ i)
        (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)) := by
  have hcomp : ∀ {B : CommGroupScheme (Spec (CommRingCat.of F))} (r : B.toGrp ⟶ S.toGrp)
      (x : rationalPoints B.toGrp),
      rationalPoints.map (r ≫ i) x = rationalPoints.map i (rationalPoints.map r x) := by
    intro B r x
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hcomp, hcomp]
  congr 1
  have h' := CocharacterUniformizer.map_latticeSection (Additive.ofMul q') c'
  have h := CocharacterUniformizer.map_latticeSection (Additive.ofMul q) c
  change rationalPoints.map (CommGroupScheme.groupHom (Additive.ofMul q')) _ =
    rationalPoints.map (CommGroupScheme.groupHom (Additive.ofMul q)) _
  rw [h', h, hcc]

/-- The norms of the restricted characters at the common-uniformizer value of a component
cocharacter depend only on that cocharacter read in `S`. -/
theorem characterNorm_componentCharacterRestriction_eq {c : cocharacterLattice A}
    {c' : cocharacterLattice A'}
    (hcc : cocharacterMapInt (Additive.ofMul q') c' = cocharacterMapInt (Additive.ofMul q) c)
    (α : characterLattice S) :
    CocharacterUniformizer.characterNorm F A' (componentCharacterRestriction q' α)
        (CocharacterUniformizer.latticeSection F A' (Multiplicative.ofAdd c')) =
      CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α)
        (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)) := by
  rw [CocharacterUniformizer.characterNorm_latticeSection,
    CocharacterUniformizer.characterNorm_latticeSection, componentCharacterRestriction_pairing,
    componentCharacterRestriction_pairing, hcc]

/-- A chamber cut out of `C_A` by one condition on the norms of the restricted outside-`J`
simple roots, for one component, is contained in the chamber cut out by the same condition for
any other compatible component. -/
theorem image_componentChamber_subset [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (p : ℝ → Prop) :
    rationalPoints.map (q ≫ i) ''
        {a | a ∈ CocharacterUniformizer.CA F A ∧
          ∀ β ∈ standardParabolicComponentCharacters i ν J q,
            p (CocharacterUniformizer.characterNorm F A β a)} ⊆
      rationalPoints.map (q' ≫ i) ''
        {a | a ∈ CocharacterUniformizer.CA F A' ∧
          ∀ β ∈ standardParabolicComponentCharacters i ν J q',
            p (CocharacterUniformizer.characterNorm F A' β a)} := by
  rintro _ ⟨_, ⟨⟨c, rfl⟩, hc⟩, rfl⟩
  obtain ⟨c', hcc⟩ := hA.exists_cocharacter_eq i ν hA' hG hi hν hJ c.toAdd
  refine ⟨CocharacterUniformizer.latticeSection F A' (Multiplicative.ofAdd c'),
    ⟨⟨Multiplicative.ofAdd c', rfl⟩, ?_⟩, map_comp_latticeSection_eq i hcc⟩
  rintro _ ⟨α, hα, rfl⟩
  rw [characterNorm_componentCharacterRestriction_eq hcc]
  exact hc _ ⟨α, hα, rfl⟩

/-- `C_A` of one compatible component is contained in `C_A` of any other one. -/
theorem standardComponentCA_subset [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    (standardComponentCA i q : Set (rationalPoints G)) ⊆ standardComponentCA i q' := by
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  obtain ⟨c', hcc⟩ := hA.exists_cocharacter_eq i ν hA' hG hi hν hJ c.toAdd
  exact ⟨_, ⟨Multiplicative.ofAdd c', rfl⟩, map_comp_latticeSection_eq i hcc⟩

/-- **Transport of basis members between compatible split components.** If `K` is a
standard-parabolic basis member for `J` with respect to one compatible split component of `M_J`,
it is one with respect to every compatible split component of `M_J`. -/
theorem StandardParabolicBasisMember.of_compatibleComponent [LocallyOfFiniteType G.X.hom]
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q')
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K : Subgroup (rationalPoints G)}
    (hK : StandardParabolicBasisMember i ν J q' K) :
    StandardParabolicBasisMember i ν J q K := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact ⟨hK.1, hK.2.mono (standardComponentCA_subset i ν hA hA' hG hi hν hJ)
    (image_componentChamber_subset i ν hA hA' hG hi hν hJ (· ≤ 1))
    (image_componentChamber_subset i ν hA hA' hG hi hν hJ (· < 1))
    (fun ε => image_componentChamber_subset i ν hA hA' hG hi hν hJ (· < ε))⟩

end Rational

end Langlands.BruhatTits.SpecialCompact
