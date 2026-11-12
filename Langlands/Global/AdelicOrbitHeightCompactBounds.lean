import Langlands.Global.AdelicOrbitHeightMinimum
import Langlands.Global.AdelicRepresentationHeightExhaustion

/-! # Compact-factor comparison for actual primitive-vector heights -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.MatrixInverseHeight

variable {R : Type u} [CommRing R] {K : Type v} [NormedField K]
  (f : R →+* K) {n : ℕ}

/-- The dimension factor occurs only at the archimedean places. -/
theorem localMaximum_mulVec_le (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin n → R) :
    ‖fun i => f ((g.val *ᵥ x) i)‖ ≤
      (n : ℝ) * localMaximum f g * ‖fun i => f (x i)‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg f g))
      (norm_nonneg _))).mpr
  intro i
  change ‖f (∑ j, g i j * x j)‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ j, ‖f (g i j * x j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, localMaximum f g * ‖fun i => f (x i)‖ :=
      Finset.sum_le_sum fun j _ => by
        rw [map_mul, norm_mul]
        exact mul_le_mul (entry_le_localMaximum f g i j)
          (norm_le_pi_norm (fun i => f (x i)) j) (norm_nonneg _)
          (localMaximum_nonneg f g)
    _ = _ := by simp; ring

/-- No dimension factor is needed for an ultrametric local norm. -/
theorem localMaximum_mulVec_le_ultra [IsUltrametricDist K]
    (g : Matrix.GeneralLinearGroup (Fin n) R) (x : Fin n → R) :
    ‖fun i => f ((g.val *ᵥ x) i)‖ ≤
      localMaximum f g * ‖fun i => f (x i)‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (localMaximum_nonneg f g) (norm_nonneg _))).mpr
  intro i
  change ‖f (∑ j, g i j * x j)‖ ≤ _
  rw [map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (localMaximum_nonneg f g) (norm_nonneg _))
  intro j _
  rw [map_mul, norm_mul]
  exact mul_le_mul (entry_le_localMaximum f g i j)
    (norm_le_pi_norm (fun i => f (x i)) j) (norm_nonneg _)
    (localMaximum_nonneg f g)

end Langlands.Global.MatrixInverseHeight

namespace Langlands.Global.PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

theorem finiteNorm_mulVec_le_matrixHeight (g : AdelicGL F n) (x : Vector F n)
    (v : FinitePlace F) :
    finiteNorm F n (g.val *ᵥ x) v ≤
      AdelicMatrixHeight.finiteLocal F n g v * finiteNorm F n x v :=
  MatrixInverseHeight.localMaximum_mulVec_le_ultra (finiteProjection F v) g x

theorem infiniteNorm_mulVec_le_matrixHeight (g : AdelicGL F n) (x : Vector F n)
    (v : InfinitePlace F) :
    infiniteNorm F n (g.val *ᵥ x) v ≤
      ((n : ℝ) * AdelicMatrixHeight.infiniteLocal F n g v) * infiniteNorm F n x v :=
  MatrixInverseHeight.localMaximum_mulVec_le (infiniteProjection F v) g x

/-- The dimension-scaled normalized matrix height bounds its action on every
actual primitive vector, with matching place normalizations. -/
theorem height_mulVec_le_matrixHeight (hn : 0 < n) {x : Vector F n} (hx : IsPrimitive F n x)
    (g : AdelicGL F n) :
    height F n (g.val *ᵥ x) ≤ AdelicMatrixHeight.height F n g * height F n x := by
  have hgx := hx.mulVec F n g
  have hfin :
      (∏ᶠ v : FinitePlace F, finiteNorm F n (g.val *ᵥ x) v) ≤
        (∏ᶠ v : FinitePlace F, AdelicMatrixHeight.finiteLocal F n g v) *
          ∏ᶠ v : FinitePlace F, finiteNorm F n x v := by
    rw [← finprod_mul_distrib
      (AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal F n hn g)
      (hx.hasFiniteMulSupport F n)]
    exact finprod_le_finprod₀ (hgx.hasFiniteMulSupport F n)
      (fun _ => norm_nonneg _)
      ((AdelicMatrixHeight.hasFiniteMulSupport_finiteLocal F n hn g).mul
        (hx.hasFiniteMulSupport F n))
      (finiteNorm_mulVec_le_matrixHeight F n g x)
  have hprod :
      (∏ v : InfinitePlace F, infiniteNorm F n (g.val *ᵥ x) v ^ v.mult) ≤
        (∏ v : InfinitePlace F,
          ((n : ℝ) * AdelicMatrixHeight.infiniteLocal F n g v) ^ v.mult) *
          ∏ v : InfinitePlace F, infiniteNorm F n x v ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro _ _
      exact pow_nonneg (norm_nonneg _) _
    · intro v _
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (infiniteNorm_mulVec_le_matrixHeight F n g x v) _
  change _ ≤
    ((∏ v : InfinitePlace F,
        ((n : ℝ) * AdelicMatrixHeight.infiniteLocal F n g v) ^ v.mult) *
      ∏ᶠ v : FinitePlace F, AdelicMatrixHeight.finiteLocal F n g v) *
    ((∏ v : InfinitePlace F, infiniteNorm F n x v ^ v.mult) *
      ∏ᶠ v : FinitePlace F, finiteNorm F n x v)
  calc
    _ ≤ _ := mul_le_mul hprod hfin (finprod_nonneg fun _ => norm_nonneg _)
      (mul_nonneg
        (Finset.prod_nonneg fun _ _ =>
          pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (MatrixInverseHeight.localMaximum_nonneg _ _)) _)
        (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _))
    _ = _ := by ring

/-- A two-sided multiplicative comparison on the whole primitive-vector locus. -/
def IsHeightDistortionBound (g : AdelicGL F n) (B : ℝ) : Prop :=
  ∀ x : Vector F n, IsPrimitive F n x →
    height F n (g.val *ᵥ x) ≤ B * height F n x ∧
      height F n x ≤ B * height F n (g.val *ᵥ x)

/-- The same full matrix-and-inverse height controls both inequalities. -/
theorem isHeightDistortionBound_height (hn : 0 < n) (g : AdelicGL F n) :
    IsHeightDistortionBound F n g (AdelicMatrixHeight.height F n g) := by
  intro x hx
  refine ⟨height_mulVec_le_matrixHeight F n hn hx g, ?_⟩
  have h := height_mulVec_le_matrixHeight F n hn (hx.mulVec F n g) g⁻¹
  simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mulVec, AdelicMatrixHeight.height_inv] using h

/-- Every compact set of actual adelic matrices has one positive distortion
bound, uniform over all primitive vectors. -/
theorem exists_pos_isHeightDistortionBound_of_isCompact (hn : 0 < n)
    {C : Set (AdelicGL F n)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ C, IsHeightDistortionBound F n g B := by
  obtain ⟨A, hA⟩ := hC.bddAbove_image
    (AdelicMatrixHeight.continuous_height F hn).continuousOn
  refine ⟨max A 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro g hg x hx
  have hgB : AdelicMatrixHeight.height F n g ≤ max A 1 :=
    (hA ⟨g, hg, rfl⟩).trans (le_max_left _ _)
  obtain ⟨hup, hlo⟩ := isHeightDistortionBound_height F n hn g x hx
  exact ⟨hup.trans (mul_le_mul_of_nonneg_right hgB (hx.height_pos F n).le),
    hlo.trans (mul_le_mul_of_nonneg_right hgB ((hx.mulVec F n g).height_pos F n).le)⟩

end Langlands.Global.PrimitiveAdelicHeight

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {n : ℕ}

/-- A compact factor on the left changes every actual representation-vector
height by uniformly bounded factors, independently of the point and vector. -/
theorem exists_pos_orbitHeight_bounds_of_isCompact
    (ρ : MatrixRepresentation G (Fin n)) (hn : 0 < n)
    {C : Set (AdelicGroupPoints F G)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ k ∈ C, ∀ (g : AdelicGroupPoints F G)
      (v : Fin n → F), v ≠ 0 →
        orbitHeight F G ρ v (k * g) ≤ B * orbitHeight F G ρ v g ∧
          orbitHeight F G ρ v g ≤ B * orbitHeight F G ρ v (k * g) := by
  obtain ⟨B, hB, hb⟩ :=
    PrimitiveAdelicHeight.exists_pos_isHeightDistortionBound_of_isCompact F n hn
      (hC.image (adelicMatrix F G ρ).continuous)
  refine ⟨B, hB, ?_⟩
  intro k hk g v hv
  have hx : PrimitiveAdelicHeight.IsPrimitive F n
      ((adelicMatrix F G ρ g).val *ᵥ PrimitiveAdelicHeight.rational F n v) :=
    ⟨adelicMatrix F G ρ g, v, hv, rfl⟩
  have h := hb (adelicMatrix F G ρ k) ⟨k, hk, rfl⟩ _ hx
  simpa only [orbitHeight, PrimitiveAdelicHeight.rationalHeight, map_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec] using h

end Langlands.Global.RepresentationGrowth
