import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.SplitTorusFactorization

/-! # Strict elements from actual standard cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- An actual standard cocharacter factors integrally through the specified
compatible split component. -/
theorem IsCompatibleStandardSplitComponent.exists_cocharacter_lift
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    ∃ c : cocharacterLattice A,
      CommGroupScheme.groupHom c ≫ q = CommGroupScheme.groupHom zeta := by
  obtain ⟨_, M, j, a, hj, _, hM, ha, hcompat⟩ := hA
  have := hM.isAffineHom
  have := hi.isSplitSubtorus.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let t := standardLeviTorusFactor i ν J hj
  have ht : t ≫ j = i := standardLeviTorusFactor_comp i ν J hj
  obtain ⟨f, hf⟩ := ha.exists_factor isSplitTorus_gm
    (hzeta.isCentral_standardLeviTorusFactor i ν J hj)
  refine ⟨Additive.ofMul f, ?_⟩
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  have hcomp : (f ≫ q) ≫ i = CommGroupScheme.groupHom zeta ≫ i := by
    rw [Category.assoc, ← hcompat, ← Category.assoc, hf, Category.assoc, ht]
  exact congrArg (fun f => f.hom.hom) hcomp

/-- Every point of a compatible split component maps into the same actual
standard Levi. -/
theorem IsCompatibleStandardSplitComponent.map_mem_standardLeviPoints
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (x : rationalPoints A.toGrp) :
    rationalPoints.map (q ≫ i) x ∈ standardLeviPoints i ν J := by
  obtain ⟨_, M, j, a, hj, _, _, _, hcompat⟩ := hA
  rw [← hcompat]
  have hx := (hj.pointsEquiv (Over.mk (𝟙 _)) (rationalPoints.map a x)).property
  simpa only [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe,
    rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using hx

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A standard cocharacter supplies an actual strict element for the given
component, with all memberships needed by the Jacquet assembly. -/
theorem IsCompatibleStandardSplitComponent.exists_strict_element
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    ∃ g : rationalPoints G,
      g ∈ standardLeviPoints i ν J ∧
      g ∈ standardComponentCA i q ∧
      g ∈ standardComponentCAplus i ν J q ∧
      g ∈ standardComponentCAstrict i ν J q := by
  obtain ⟨c, hc⟩ := hA.exists_cocharacter_lift i ν hi hzeta
  let x := CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c)
  have hx : x ∈ CocharacterUniformizer.CA F A := ⟨Multiplicative.ofAdd c, rfl⟩
  have hstrict : ∀ α ∈ standardParabolicComponentCharacters i ν J q,
      CocharacterUniformizer.characterNorm F A α x < 1 := by
    rintro α ⟨β, hβ, rfl⟩
    apply CocharacterUniformizer.characterNorm_latticeSection_lt_one
    have hpair : latticePairing A (componentCharacterRestriction q β) c =
        latticePairing S β zeta := by
      change gmEndEquiv F (c ≫ (Additive.ofMul q ≫ β)) = _
      rw [← Category.assoc]
      have hc' : c ≫ Additive.ofMul q = zeta := congrArg Additive.ofMul hc
      rw [hc']
      rfl
    rw [hpair]
    exact hzeta.2.2 β hβ.1 hβ.2
  refine ⟨rationalPoints.map (q ≫ i) x,
    hA.map_mem_standardLeviPoints i ν x, ?_, ?_, ?_⟩
  · exact ⟨x, hx, rfl⟩
  · exact ⟨x, ⟨hx, fun α hα => (hstrict α hα).le⟩, rfl⟩
  · exact ⟨x, ⟨hx, hstrict⟩, rfl⟩

/-- A chosen actual strict element, depending only on the component and standard
cocharacter data, before any open subgroup is specified. -/
def IsCompatibleStandardSplitComponent.strictElement
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) : rationalPoints G :=
  (hA.exists_strict_element i ν hi hzeta).choose

/-- The chosen element has all four actual memberships used by the adapter. -/
theorem IsCompatibleStandardSplitComponent.strictElement_spec
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hi : IsMaximalSplitTorus i) {zeta : cocharacterLattice S}
    (hzeta : IsStandardCocharacter i ν J zeta) :
    hA.strictElement i ν hi hzeta ∈ standardLeviPoints i ν J ∧
    hA.strictElement i ν hi hzeta ∈ standardComponentCA i q ∧
    hA.strictElement i ν hi hzeta ∈ standardComponentCAplus i ν J q ∧
    hA.strictElement i ν hi hzeta ∈ standardComponentCAstrict i ν J q :=
  (hA.exists_strict_element i ν hi hzeta).choose_spec

end Langlands.BruhatTits.SpecialCompact
