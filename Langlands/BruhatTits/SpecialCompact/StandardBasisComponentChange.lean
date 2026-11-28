import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction
import Langlands.Geometry.Building.StandardLeviStrictUniformizerProof
import Langlands.Representation.Jacquet.StandardComponentScheme

/-! # A compact-open normal basis for a specified standard split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.RealTorusSpace
open Langlands.Aubert.General

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
  {A A' S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}
  {q : A.toGrp ⟶ S.toGrp} {q' : A'.toGrp ⟶ S.toGrp}

private theorem exists_torus_factor (hi : IsMaximalSplitTorus i)
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hA' : IsCompatibleStandardSplitComponent i ν J A' q') :
    ∃ f : A.toGrp ⟶ A'.toGrp, f ≫ q' = q := by
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have ha := isSplitComponent_standardComponentSchemeHom hA
  have ha' := isSplitComponent_standardComponentSchemeHom hA'
  obtain ⟨f, hf⟩ := ha'.exists_factor ha.1.1.1 ha.1.2
  refine ⟨f, ?_⟩
  have hfi : (f ≫ q') ≫ i = q ≫ i := by
    rw [Category.assoc, ← standardComponentSchemeHom_comp (ν := ν) (J := J) q',
      ← Category.assoc, hf, standardComponentSchemeHom_comp]
  apply Grp.hom_ext
  apply (cancel_mono i.hom.hom).mp
  exact congrArg (fun a => a.hom.hom) hfi

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

open CocharacterUniformizer in
private theorem standardComponentCAplus_subset_of_factor
    (f : A.toGrp ⟶ A'.toGrp) (hf : f ≫ q' = q) :
    standardComponentCAplus i ν J q ⊆ standardComponentCAplus i ν J q' := by
  rintro _ ⟨_, ⟨⟨c, rfl⟩, hc⟩, rfl⟩
  let c' : cocharacterLattice A' := cocharacterMapInt (Additive.ofMul f) c.toAdd
  refine ⟨_, ⟨⟨.ofAdd c', rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    have hcα := hc (componentCharacterRestriction q α) ⟨α, hα, rfl⟩
    change characterNorm F A (componentCharacterRestriction q α)
      (latticeSection F A (Multiplicative.ofAdd c.toAdd)) ≤ 1 at hcα
    rw [CocharacterUniformizer.characterNorm_latticeSection,
      componentCharacterRestriction_pairing] at hcα ⊢
    have hcomp : cocharacterMapInt (Additive.ofMul q') c' =
        cocharacterMapInt (Additive.ofMul q) c.toAdd := by
      change (c.toAdd ≫ Additive.ofMul f) ≫ Additive.ofMul q' =
        c.toAdd ≫ Additive.ofMul q
      rw [Category.assoc]
      exact congrArg (fun g : A.toGrp ⟶ S.toGrp => c.toAdd ≫ Additive.ofMul g) hf
    simpa only [hcomp] using hcα
  · rw [← map_latticeSection (F := F) (Additive.ofMul f) c.toAdd,
      ← RationalPointFamily.rationalPoints_map_comp_apply, ← Category.assoc]
    change rationalPoints.map ((f ≫ q') ≫ i) (latticeSection F A c) =
      rationalPoints.map (q ≫ i) (latticeSection F A c)
    rw [hf]

local instance standardBasisComponentChangeAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance standardBasisComponentChangeTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The simultaneous basis supplies a normal basis for every compatible split component
of the chosen standard Levi. -/
theorem SimultaneousStandardBasisAt.exists_basis_for_component
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hA : IsCompatibleStandardSplitComponent i ν J A q)
    {K₀ : Subgroup (rationalPoints G)} (hB : SimultaneousStandardBasisAt i ν K₀) :
    ∃ B : Set (Subgroup (rationalPoints G)), CompactOpenNormalBasis K₀ B ∧
      ∀ L ∈ B, StandardParabolicBasisMember i ν J q L := by
  obtain ⟨B, hBasis, hMembers⟩ := hB
  obtain ⟨_, A', q', hA', hMembers'⟩ := hMembers J hJ
  obtain ⟨f, hf⟩ := exists_torus_factor hi hA hA'
  have hChamber := standardComponentCAplus_subset_of_factor f hf (i := i) (ν := ν) (J := J)
  refine ⟨B, hBasis, fun L hL => ?_⟩
  have hMember := hMembers' L hL
  have hCompactOpen := hBasis.1 L hL
  refine ⟨hMember.1, hA.contractionAndCofinality_of_weak i ν hG hi hν hJ L
    hCompactOpen.2.2.1 hCompactOpen.2.2.2 ?_⟩
  exact fun a ha => hMember.2.2.1 a (hChamber ha)

/-- A standard parabolic with a specified compatible split component has a compact-open normal
basis of subgroups with the Iwahori decomposition and chamber contractions. -/
def StandardBasisForComponentStatement
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))
    (q : A.toGrp ⟶ S.toGrp) : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    J ⊆ simpleRelativeRoots i ν → IsCompatibleStandardSplitComponent i ν J A q →
      ∃ (K₀ : Subgroup (rationalPoints G)) (B : Set (Subgroup (rationalPoints G))),
        CompactOpenNormalBasis K₀ B ∧ ∀ L ∈ B, StandardParabolicBasisMember i ν J q L

/-- Obtain the simultaneous basis and use it for the specified split component. -/
theorem exists_standard_basis_for_component : StandardBasisForComponentStatement i ν J q := by
  intro hG hi hν hJ hA
  have : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  obtain ⟨D, x, _, _, _, _, _, _, hData⟩ :=
    jointSpecialCompactBasisExistence F G hG S i hi ν hν
  obtain ⟨_, _, _, _, _, _, _, _, hBasis⟩ := hData
  obtain ⟨B, hB, hMembers⟩ := hBasis.exists_basis_for_component hG hi hν hJ hA
  exact ⟨D.specialCompactSubgroup x, B, hB, hMembers⟩

end Langlands.BruhatTits.SpecialCompact
