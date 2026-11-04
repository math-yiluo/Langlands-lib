import Langlands.Representation.Plancherel.RenardDominantValuation
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.GroupTheory.Index

/-! # Finite positive covers of the actual dominant valuation image -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.BruhatTits.Cartan
open scoped CategoryTheory.MonObj Pointwise TensorProduct

namespace Langlands.Plancherel.RenardCartan

/-- Dickson's lemma supplies finitely many lower representatives of any set of
finite natural-coordinate vectors. -/
theorem exists_finite_lower_coordinates {J : Type v} [Finite J]
    (A : Set (J → ℕ)) :
    ∃ B : Set (J → ℕ), B.Finite ∧ B ⊆ A ∧
      ∀ a ∈ A, ∃ b ∈ B, b ≤ a := by
  let B := {b | Minimal (· ∈ A) b}
  have hanti : IsAntichain (· ≤ ·) B := by
    intro b hb c hc hne hle
    exact hne (hc.eq_of_le hb.1 hle)
  refine ⟨B, hanti.finite_of_wellQuasiOrdered wellQuasiOrdered_le,
    fun _ hb => hb.1, ?_⟩
  intro a ha
  obtain ⟨b, hba, hb⟩ := (Set.isPWO_of_wellQuasiOrderedLE A).exists_le_minimal ha
  exact ⟨b, hb, hba⟩

/-- A finite natural-coordinate test has finitely many lower representatives
inside any supplied set. -/
theorem exists_finite_coordinate_representatives {X : Type u}
    {J : Type v} [Finite J] (A : Set X) (coord : X → J → ℕ) :
    ∃ B : Set X, B.Finite ∧ B ⊆ A ∧
      ∀ a ∈ A, ∃ b ∈ B, coord b ≤ coord a := by
  classical
  obtain ⟨M, hMfin, hMA, hM⟩ := exists_finite_lower_coordinates (coord '' A)
  have hrep : ∀ m : M, ∃ x : X, x ∈ A ∧ coord x = m.val := by
    intro m
    exact hMA m.property
  choose rep hrepA hrepcoord using hrep
  let : Finite M := hMfin.to_subtype
  refine ⟨Set.range rep, Set.finite_range rep, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact hrepA m
  · intro a ha
    obtain ⟨m, hmM, hma⟩ := hM (coord a) ⟨a, ha, rfl⟩
    exact ⟨rep ⟨m, hmM⟩, ⟨⟨m, hmM⟩, rfl⟩, by
      rw [hrepcoord]
      exact hma⟩

/-- With finitely many residue classes, finitely many actual representatives
dominate from below in each class. -/
theorem exists_finite_residue_coordinate_representatives {X : Type u}
    {J : Type v} [Finite J] {Q : Type w} [Finite Q]
    (A : Set X) (residue : X → Q) (coord : X → J → ℕ) :
    ∃ B : Set X, B.Finite ∧ B ⊆ A ∧
      ∀ a ∈ A, ∃ b ∈ B, residue b = residue a ∧ coord b ≤ coord a := by
  classical
  have hq (q : Q) := exists_finite_coordinate_representatives
    {a ∈ A | residue a = q} coord
  choose B hBfin hBsub hB using hq
  refine ⟨⋃ q, B q, Set.finite_iUnion hBfin, ?_, ?_⟩
  · intro b hb
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hb
    exact (hBsub q hq).1
  · intro a ha
    obtain ⟨b, hb, hba⟩ := hB (residue a) a ⟨ha, rfl⟩
    exact ⟨b, Set.mem_iUnion.mpr ⟨residue a, hb⟩, (hBsub _ hb).2, hba⟩

/-- An integral difference between nonnegative reals has the sign of the
difference of their natural floors. -/
theorem nonneg_int_of_natFloor_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {n : ℤ} (hn : a = b + (n : ℝ)) (hfloor : ⌊b⌋₊ ≤ ⌊a⌋₊) : 0 ≤ n := by
  have hfloor' : ⌊b⌋ ≤ ⌊a⌋ := by
    rw [← Int.natCast_floor_eq_floor hb, ← Int.natCast_floor_eq_floor ha]
    exact_mod_cast hfloor
  rw [hn, Int.floor_add_intCast] at hfloor'
  omega

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}
  (s : S.toGrp ⟶ Z) (h : Function.Bijective (restrictionEvaluation s))
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Natural floors of the actual positive-root orders on the real valuation. -/
def dominantFloorCoordinates (z : rationalPoints Z) :
    positiveRelativeRoots i ν → ℕ :=
  fun α => ⌊RealTorusSpace.eval S α.val (centralizerValuation s h z).toAdd⌋₊

/-- The actual dominant set is closed under multiplication. -/
theorem dominantCentralizer_mul_mem {z w : rationalPoints Z}
    (hz : z ∈ dominantCentralizer i ν s h)
    (hw : w ∈ dominantCentralizer i ν s h) :
    z * w ∈ dominantCentralizer i ν s h := by
  intro α hα
  change 0 ≤ RealTorusSpace.eval S α (centralizerValuation s h (z * w)).toAdd
  rw [map_mul, toAdd_mul, map_add]
  exact add_nonneg (hz α hα) (hw α hα)

/-- Finite root support and a finite-index split image give a finite positive
product cover. Only surjectivity on the actual uniformizer subgroup is used. -/
theorem exists_finite_positiveProductCover
    (hroots : (positiveRelativeRoots i ν).Finite)
    (hindex : (splitValuationImage s).FiniteIndex)
    (hsurj : Set.SurjOn (rationalCharacterValuation Z).rangeRestrict
      (C0 S s : Set (rationalPoints Z))
      (splitValuationImage s : Set (rationalCharacterValuationImage Z))) :
    ∃ B : Set (rationalPoints Z),
      IsFinitePositiveProductCover s (positiveRelativeRoots i ν)
        (dominantCentralizer i ν s h) B := by
  classical
  let : Finite (positiveRelativeRoots i ν) := hroots.to_subtype
  let : (splitValuationImage s).FiniteIndex := hindex
  obtain ⟨B, hBfin, hBD, hB⟩ := exists_finite_residue_coordinate_representatives
    (dominantCentralizer i ν s h) (latticeResidue s)
    (dominantFloorCoordinates s h i ν)
  refine ⟨B, hBfin, hBD, ?_, ?_⟩
  · rintro _ ⟨c, hc, f, hf, rfl⟩
    exact dominantCentralizer_mul_mem s h i ν
      ((C0Plus_eq_inter_dominant s h i ν ▸ hc).2) (hBD hf)
  · rintro v ⟨z, hz, rfl⟩
    obtain ⟨f, hf, hres, hfloor⟩ := hB z hz
    have hdiff : (rationalCharacterValuation Z).rangeRestrict z /
        (rationalCharacterValuation Z).rangeRestrict f ∈ splitValuationImage s :=
      (QuotientGroup.eq_iff_div_mem (N := splitValuationImage s)).mp hres.symm
    obtain ⟨c, hc, hcv⟩ := hsurj hdiff
    have hmulval : (rationalCharacterValuation Z).rangeRestrict (c * f) =
        (rationalCharacterValuation Z).rangeRestrict z := by
      rw [map_mul, hcv, div_mul_cancel]
    have hreal := centralizerValuation_eq_of_characterValuation_eq s h
      (congrArg Subtype.val hmulval)
    obtain ⟨n, hn⟩ := (mem_C0 S s c).mp hc
    have hcpos : c ∈ C0Plus S s (positiveRelativeRoots i ν) := by
      refine ⟨n, ?_, hn⟩
      intro α hα
      have horder : RealTorusSpace.eval S α (centralizerValuation s h z).toAdd =
          RealTorusSpace.eval S α (centralizerValuation s h f).toAdd +
            (latticePairing S α n : ℝ) := by
        rw [← hreal, map_mul, toAdd_mul, map_add, ← hn,
          centralizerValuation_uniformizerSection, RealTorusSpace.eval_tmul, one_mul]
        exact add_comm _ _
      exact nonneg_int_of_natFloor_le (hz α hα) (hBD hf α hα) horder
        (hfloor ⟨α, hα⟩)
    exact ⟨c * f, Set.mem_mul.mpr ⟨c, hcpos, f, hf, rfl⟩, hmulval⟩

end Langlands.Plancherel.RenardCartan
