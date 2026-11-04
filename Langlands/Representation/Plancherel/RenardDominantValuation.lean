import Langlands.Representation.Plancherel.RenardDominantComparisonStatement
import Langlands.Geometry.Building.CocharacterUniformizerEvaluation

/-! # Normalization and chamber transport for Renard's centralizer valuation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise TensorProduct

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}
  (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))

/-- The actual uniformizer section followed by the real centralizer valuation. -/
def uniformizerRealValuation :
    cocharacterLattice S →+ RealTorusSpace.V S where
  toFun c := (centralizerValuation s h
    (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))).toAdd
  map_zero' := by simp
  map_add' c d := by simp

/-- The actual uniformizer section has positive unit cocharacter valuation. -/
theorem centralizerValuation_uniformizerSection (c : cocharacterLattice S) :
    (centralizerValuation s h
      (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))).toAdd =
        (1 : ℝ) ⊗ₜ[ℤ] c := by
  symm
  apply (eq_centralizerValuation_iff s h _ _).mpr
  intro χ
  rw [RealTorusSpace.eval_tmul, one_mul,
    ← rationalCharacterValuation_characterRestrict]
  congr 1
  simpa only [uniformizerSection, characterRestriction, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    AddEquiv.symm_apply_apply] using
    (CocharacterUniformizer.rationalCharacterValuation_latticeSection F S
      (characterRestriction s χ) c).symm

/-- Equality in the integer valuation image implies equality of real valuations. -/
theorem centralizerValuation_eq_of_characterValuation_eq
    {z w : rationalPoints Z}
    (hzw : rationalCharacterValuation Z z = rationalCharacterValuation Z w) :
    centralizerValuation s h z = centralizerValuation s h w := by
  apply Multiplicative.toAdd.injective
  apply h.injective
  apply AddMonoidHom.ext
  intro χ
  change RealTorusSpace.eval S (characterRestriction s χ)
    (centralizerValuation s h z).toAdd =
      RealTorusSpace.eval S (characterRestriction s χ)
        (centralizerValuation s h w).toAdd
  rw [centralizerValuation_spec s h z χ, centralizerValuation_spec s h w χ, hzw]

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Dominance of a uniformizer value is exactly nonnegativity of its pairings. -/
theorem uniformizerSection_mem_dominant_iff (c : cocharacterLattice S) :
    rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)) ∈
        dominantCentralizer i ν s h ↔
      ∀ α ∈ positiveRelativeRoots i ν, 0 ≤ latticePairing S α c := by
  change (∀ α ∈ positiveRelativeRoots i ν,
    0 ≤ RealTorusSpace.eval S α
      (centralizerValuation s h
        (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd c)))).toAdd) ↔ _
  rw [centralizerValuation_uniformizerSection]
  simp only [RealTorusSpace.eval_tmul, one_mul]
  constructor
  · intro hc α hα
    exact_mod_cast hc α hα
  · intro hc α hα
    exact_mod_cast hc α hα

/-- The positive uniformizer set is precisely the chamber cut of `C0`. -/
theorem C0Plus_eq_inter_dominant :
    C0Plus S s (positiveRelativeRoots i ν) =
      (C0 S s : Set (rationalPoints Z)) ∩ dominantCentralizer i ν s h := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(mem_C0 S s _).mpr ⟨c, rfl⟩,
      (uniformizerSection_mem_dominant_iff s h i ν c).mpr hc⟩
  · rintro ⟨hz, hzD⟩
    obtain ⟨c, rfl⟩ := (mem_C0 S s z).mp hz
    exact ⟨c, (uniformizerSection_mem_dominant_iff s h i ν c).mp hzD, rfl⟩

/-- Dominance depends only on the integer character valuation. -/
theorem dominantCentralizer_mem_iff_of_characterValuation_eq
    {z w : rationalPoints Z}
    (hzw : rationalCharacterValuation Z z = rationalCharacterValuation Z w) :
    z ∈ dominantCentralizer i ν s h ↔ w ∈ dominantCentralizer i ν s h := by
  change (∀ α ∈ positiveRelativeRoots i ν,
    0 ≤ RealTorusSpace.eval S α (centralizerValuation s h z).toAdd) ↔
      ∀ α ∈ positiveRelativeRoots i ν,
        0 ≤ RealTorusSpace.eval S α (centralizerValuation s h w).toAdd
  rw [centralizerValuation_eq_of_characterValuation_eq s h hzw]

/-- The canonical image equivalence identifies the two actual chamber images. -/
theorem centralizerValuationImageEquiv_image_dominant :
    centralizerValuationImageEquiv s h '' dominantValuationImage i ν s h =
      (rationalCharacterValuation Z).rangeRestrict '' dominantCentralizer i ν s h := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨z, hz⟩ := w.property
    have hwz : w = ⟨centralizerValuation s h z, z, rfl⟩ := Subtype.ext hz.symm
    subst w
    exact ⟨z, hw, (centralizerValuationImageEquiv_apply s h z).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨centralizerValuation s h z, z, rfl⟩, hz,
      centralizerValuationImageEquiv_apply s h z⟩

/-- Cutting a full valuation section by the chamber gives a dominant section. -/
theorem isDominantValuationSection_inter {A : Set (rationalPoints Z)}
    (hA : IsValuationSection A) :
    IsDominantValuationSection (dominantCentralizer i ν s h)
      (A ∩ dominantCentralizer i ν s h) := by
  refine ⟨Set.inter_subset_right, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨z, hz.2, rfl⟩
  · intro z hz w hw hzw
    exact congrArg Subtype.val (hA.injective (a₁ := ⟨z, hz.1⟩)
      (a₂ := ⟨w, hw.1⟩) hzw)
  · rintro v ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := hA.surjective ((rationalCharacterValuation Z).rangeRestrict z)
    have hav : rationalCharacterValuation Z a.val = rationalCharacterValuation Z z :=
      congrArg Subtype.val ha
    exact ⟨a.val, ⟨a.property,
      (dominantCentralizer_mem_iff_of_characterValuation_eq s h i ν hav).mpr hz⟩, ha⟩

/-- A dominant integer-valuation section is also a section for the actual real image. -/
theorem isDominantValuationSection_bijOn_centralizerValuation
    {A : Set (rationalPoints Z)}
    (hA : IsDominantValuationSection (dominantCentralizer i ν s h) A) :
    Set.BijOn (centralizerValuation s h).rangeRestrict A
      (dominantValuationImage i ν s h) := by
  refine ⟨fun z hz => hA.1 hz, ?_, ?_⟩
  · intro z hz w hw hzw
    apply hA.2.injOn hz hw
    have hv := congrArg (centralizerValuationImageEquiv s h) hzw
    change centralizerValuationImageEquiv s h
      ⟨centralizerValuation s h z, z, rfl⟩ =
        centralizerValuationImageEquiv s h
          ⟨centralizerValuation s h w, w, rfl⟩ at hv
    exact (centralizerValuationImageEquiv_apply s h z).symm.trans
      (hv.trans (centralizerValuationImageEquiv_apply s h w))
  · intro v hv
    obtain ⟨z, hz⟩ := v.property
    have hvz : v = ⟨centralizerValuation s h z, z, rfl⟩ := Subtype.ext hz.symm
    subst v
    obtain ⟨a, ha, hav⟩ := hA.2.surjOn ⟨z, hv, rfl⟩
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    exact centralizerValuation_eq_of_characterValuation_eq s h (congrArg Subtype.val hav)

end Langlands.Plancherel.RenardCartan
