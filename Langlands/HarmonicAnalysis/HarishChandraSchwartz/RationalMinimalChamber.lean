import Langlands.BruhatTits.Cartan.RenardLeviCones
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeights

/-! # The full minimal-torus chamber for Waldspurger VIII.3

This is the full normalized-norm chamber, before choosing a common-uniformizer
section. All membership and valuation comparisons reuse RenardLeviCones.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.Cartan Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- The image of the full closed normalized-norm chamber of the minimal torus. -/
def rationalMinimalChamber : Set (rationalPoints G) :=
  rationalPoints.map i '' RenardLeviCones.componentPlus F i ν ∅ (𝟙 S)

/-- Membership through every simple relative root, with no lattice-section restriction. -/
theorem mem_rationalMinimalChamber_iff_norm (g : rationalPoints G) :
    g ∈ rationalMinimalChamber i ν ↔ ∃ a : rationalPoints S.toGrp,
      rationalPoints.map i a = g ∧
        ∀ α ∈ simpleRelativeRoots i ν,
          CocharacterUniformizer.characterNorm F S α a ≤ 1 := by
  simp only [rationalMinimalChamber, Set.mem_image, RenardLeviCones.componentPlus,
    Set.mem_ofPred_eq, RenardLeviCones.restrictedSimpleCharacters_minimal]
  exact exists_congr fun a => and_comm

/-- The same chamber in the published positive-sign integral valuation convention. -/
theorem mem_rationalMinimalChamber_iff_order (g : rationalPoints G) :
    g ∈ rationalMinimalChamber i ν ↔ ∃ a : rationalPoints S.toGrp,
      rationalPoints.map i a = g ∧
        ∀ α ∈ simpleRelativeRoots i ν, 0 ≤ RenardLeviCones.characterOrder S α a := by
  simp only [rationalMinimalChamber, Set.mem_image,
    RenardLeviCones.mem_componentPlus_iff_order,
    RenardLeviCones.restrictedSimpleCharacters_minimal]
  exact exists_congr fun a => and_comm

/-- Comparison with the positive centralizer valuation used by source I.1.
The displayed `s` and character-restriction bijection may be those of a represented
minimal Levi; this is exactly the published restriction-of-valuation comparison. -/
theorem mem_rationalMinimalChamber_iff_dominant
    {Z : GroupScheme (Spec (CommRingCat.of F))}
    (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))
    (hS : IsSplitTorus S.toGrp) (g : rationalPoints G) :
    g ∈ rationalMinimalChamber i ν ↔ ∃ a : rationalPoints S.toGrp,
      rationalPoints.map i a = g ∧
        rationalPoints.map s a ∈ dominantCentralizer i ν s h := by
  simp only [rationalMinimalChamber, Set.mem_image]
  refine exists_congr fun a => ?_
  rw [← RenardLeviCones.leviPlus_minimal i ν s h,
    RenardLeviCones.map_mem_leviPlus_iff i ν ∅ (𝟙 S) s h hS]
  exact and_comm

/-- The torus image lies in the actual minimal parabolic, through its centralizer. -/
theorem rationalMinimalChamber_subset_minimalParabolic :
    rationalMinimalChamber i ν ⊆ (standardParabolicPoints i ν ∅ : Set (rationalPoints G)) := by
  rintro _ ⟨a, _, rfl⟩
  exact SubgroupFunctor.le_def.mp (standardLevi_le_standardParabolic i ν ∅) _
    (SubgroupFunctor.le_def.mp (torusCentralizer_le_standardLevi i ν ∅) _
      (SubgroupFunctor.le_def.mp (range_le_torusCentralizer i) _
        (SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩)))

/-- The source's full chamber intersected with the actual common character-norm kernel. -/
def rationalMinimalChamberInNormKernel : Set (rationalPoints G) :=
  rationalMinimalChamber i ν ∩ (rationalCommonNormKernel G : Set (rationalPoints G))

@[simp] theorem mem_rationalMinimalChamberInNormKernel (g : rationalPoints G) :
    g ∈ rationalMinimalChamberInNormKernel i ν ↔
      g ∈ rationalMinimalChamber i ν ∧ g ∈ rationalCommonNormKernel G := Iff.rfl

/-- A chamber point read in the actual minimal parabolic, where `δ₀` is defined. -/
def rationalMinimalChamberToParabolic (a : rationalMinimalChamberInNormKernel i ν) :
    standardParabolicPoints i ν ∅ :=
  ⟨a, rationalMinimalChamber_subset_minimalParabolic i ν a.property.1⟩

@[simp] theorem rationalMinimalChamberToParabolic_coe
    (a : rationalMinimalChamberInNormKernel i ν) :
    (rationalMinimalChamberToParabolic i ν a : rationalPoints G) = a := rfl

/-- Relative rank zero imposes no root inequalities; the whole torus image remains. -/
theorem rationalMinimalChamber_eq_range_of_simpleRoots_empty
    (h0 : simpleRelativeRoots i ν = ∅) :
    rationalMinimalChamber i ν = ((rationalPoints.map i).range : Set (rationalPoints G)) := by
  ext g
  rw [mem_rationalMinimalChamber_iff_norm]
  simp only [h0, Set.mem_empty_iff_false, false_implies, implies_true, and_true]
  rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The algebraic character-restriction map for the identity torus inclusion is identity. -/
theorem componentCharacterRestriction_id (α : characterLattice S) :
    componentCharacterRestriction (𝟙 S.toGrp) α = α := by
  simp [componentCharacterRestriction, characterRestrict_id]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The published lattice-section convention has the same simple-root characters when
the full minimal torus itself is used, with the identity algebraic inclusion. -/
theorem standardParabolicComponentCharacters_minimal_id :
    standardParabolicComponentCharacters i ν ∅ (𝟙 S.toGrp) = simpleRelativeRoots i ν := by
  simp only [standardParabolicComponentCharacters, Set.sdiff_empty]
  ext α
  simp only [Set.mem_image, componentCharacterRestriction_id, exists_eq_right]

/-- The identity-torus version of the existing section is precisely the image of the
common-uniformizer lattice cut of the full chamber, rather than the full chamber itself. -/
theorem standardComponentCAplus_minimal_id_eq_latticeCut :
    standardComponentCAplus i ν ∅ (𝟙 S.toGrp) = rationalPoints.map i ''
      ((CocharacterUniformizer.CA F S : Set (rationalPoints S.toGrp)) ∩
        RenardLeviCones.componentPlus F i ν ∅ (𝟙 S)) := by
  rw [standardComponentCAplus, Category.id_comp,
    standardParabolicComponentCharacters_minimal_id,
    ← RenardLeviCones.restrictedSimpleCharacters_minimal i ν]
  rfl

/-- In particular this published common-uniformizer section is contained in the full
ambient chamber; no equality of the section and full chamber is claimed. -/
theorem standardComponentCAplus_minimal_id_subset :
    standardComponentCAplus i ν ∅ (𝟙 S.toGrp) ⊆ rationalMinimalChamber i ν := by
  rw [standardComponentCAplus_minimal_id_eq_latticeCut]
  exact Set.image_mono Set.inter_subset_right

end Langlands.HarishChandraSchwartz
