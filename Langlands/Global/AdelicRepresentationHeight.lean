import Langlands.Global.RepresentationGrowth
import Langlands.Global.PrimitiveAdelicHeight

/-! # Full adelic matrix-and-inverse heights -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global

namespace MatrixInverseHeight

variable {R : Type u} [CommRing R] {K : Type v} [NormedField K]
  (f : R →+* K) {n : ℕ}

/-- The entry maximum of a matrix and its inverse, before place normalization. -/
def localMaximum (g : Matrix.GeneralLinearGroup (Fin n) R) : ℝ :=
  max ‖fun i j : Fin n => f (g i j)‖ ‖fun i j : Fin n => f (g⁻¹ i j)‖

theorem localMaximum_nonneg (g : Matrix.GeneralLinearGroup (Fin n) R) :
    0 ≤ localMaximum f g := (norm_nonneg _).trans (le_max_left _ _)

theorem entry_le_localMaximum (g : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    ‖f (g i j)‖ ≤ localMaximum f g := by
  have h₁ := norm_le_pi_norm (fun k : Fin n => f (g i k)) j
  have h₂ := norm_le_pi_norm (fun k l : Fin n => f (g k l)) i
  exact (h₁.trans h₂).trans (le_max_left _ _)

/-- The local matrix used in the doubled source embedding. -/
def doubledMatrix (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks (g.val.map f) 0 0 ((g⁻¹).val.map f).transpose

/-- The maximum is exactly the entry norm of the doubled matrix, including its transpose. -/
theorem localMaximum_eq_norm_doubledMatrix (g : Matrix.GeneralLinearGroup (Fin n) R) :
    localMaximum f g = ‖fun a b => doubledMatrix f g a b‖ := by
  apply le_antisymm
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      have h₁ := norm_le_pi_norm (fun b => doubledMatrix f g (Sum.inl i) b) (Sum.inl j)
      have h₂ := norm_le_pi_norm (fun a b => doubledMatrix f g a b) (Sum.inl i)
      exact h₁.trans h₂
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      have h₁ := norm_le_pi_norm (fun b => doubledMatrix f g (Sum.inr j) b) (Sum.inr i)
      have h₂ := norm_le_pi_norm (fun a b => doubledMatrix f g a b) (Sum.inr j)
      exact h₁.trans h₂
  · apply (pi_norm_le_iff_of_nonneg (localMaximum_nonneg f g)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (localMaximum_nonneg f g)).mpr
    intro b
    cases a with
    | inl i =>
      cases b with
      | inl j => exact entry_le_localMaximum f g i j
      | inr j =>
        change ‖(0 : K)‖ ≤ localMaximum f g
        rw [norm_zero]
        exact localMaximum_nonneg f g
    | inr i =>
      cases b with
      | inl j =>
        change ‖(0 : K)‖ ≤ localMaximum f g
        rw [norm_zero]
        exact localMaximum_nonneg f g
      | inr j =>
        change ‖f (g⁻¹ j i)‖ ≤ localMaximum f g
        simpa only [localMaximum, inv_inv, max_comm] using entry_le_localMaximum f g⁻¹ j i

@[simp]
theorem localMaximum_inv (g : Matrix.GeneralLinearGroup (Fin n) R) :
    localMaximum f g⁻¹ = localMaximum f g := by
  simp only [localMaximum, inv_inv, max_comm]

private theorem matrixNorm_mul_le (A B : Matrix (Fin n) (Fin n) R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖f (A i j)‖ ≤ a) (hB : ∀ i j, ‖f (B i j)‖ ≤ b) :
    ‖fun i j : Fin n => f ((A * B) i j)‖ ≤ n * (a * b) := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha hb))).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ha hb))).mpr
  intro j
  rw [Matrix.mul_apply, map_sum]
  calc
    ‖∑ k, f (A i k * B k j)‖ ≤ ∑ k, ‖f (A i k * B k j)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
      rw [map_mul, norm_mul]
      exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
    _ = n * (a * b) := by simp

private theorem matrixNorm_mul_le_ultra [IsUltrametricDist K]
    (A B : Matrix (Fin n) (Fin n) R)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖f (A i j)‖ ≤ a) (hB : ∀ i j, ‖f (B i j)‖ ≤ b) :
    ‖fun i j : Fin n => f ((A * B) i j)‖ ≤ a * b := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg ha hb)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg ha hb)).mpr
  intro j
  rw [Matrix.mul_apply, map_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
  intro k _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

theorem localMaximum_mul_le (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    localMaximum f (g * h) ≤ n * (localMaximum f g * localMaximum f h) := by
  apply max_le
  · exact matrixNorm_mul_le f g.val h.val (localMaximum_nonneg f g)
      (localMaximum_nonneg f h) (entry_le_localMaximum f g) (entry_le_localMaximum f h)
  · have hh := matrixNorm_mul_le f (h⁻¹).val (g⁻¹).val
      (localMaximum_nonneg f h⁻¹) (localMaximum_nonneg f g⁻¹)
      (entry_le_localMaximum f h⁻¹) (entry_le_localMaximum f g⁻¹)
    simpa only [mul_inv_rev, Units.val_mul, localMaximum_inv, mul_comm] using hh

theorem localMaximum_mul_le_ultra [IsUltrametricDist K]
    (g h : Matrix.GeneralLinearGroup (Fin n) R) :
    localMaximum f (g * h) ≤ localMaximum f g * localMaximum f h := by
  apply max_le
  · exact matrixNorm_mul_le_ultra f g.val h.val (localMaximum_nonneg f g)
      (localMaximum_nonneg f h) (entry_le_localMaximum f g) (entry_le_localMaximum f h)
  · have hh := matrixNorm_mul_le_ultra f (h⁻¹).val (g⁻¹).val
      (localMaximum_nonneg f h⁻¹) (localMaximum_nonneg f g⁻¹)
      (entry_le_localMaximum f h⁻¹) (entry_le_localMaximum f g⁻¹)
    simpa only [mul_inv_rev, Units.val_mul, localMaximum_inv, mul_comm] using hh

variable (hn : 0 < n)

include hn in
theorem one_le_nat_mul_localMaximum (g : Matrix.GeneralLinearGroup (Fin n) R) :
    1 ≤ (n : ℝ) * localMaximum f g := by
  let i : Fin n := ⟨0, hn⟩
  have h1 : (1 : ℝ) ≤ n * (localMaximum f g * localMaximum f g) := by
    calc
      1 = ‖f ((g.val * (g⁻¹).val) i i)‖ := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        simp
      _ ≤ ‖fun i j : Fin n => f ((g.val * (g⁻¹).val) i j)‖ :=
        (norm_le_pi_norm (fun j : Fin n => f ((g.val * (g⁻¹).val) i j)) i).trans
          (norm_le_pi_norm (fun k j : Fin n => f ((g.val * (g⁻¹).val) k j)) i)
      _ ≤ n * (localMaximum f g * localMaximum f g) := by
        simpa only [localMaximum_inv] using matrixNorm_mul_le f g.val (g⁻¹).val
          (localMaximum_nonneg f g) (localMaximum_nonneg f g⁻¹)
          (entry_le_localMaximum f g) (entry_le_localMaximum f g⁻¹)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn
  by_cases hg : 1 ≤ localMaximum f g
  · exact one_le_mul_of_one_le_of_one_le hn1 hg
  · exact h1.trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (localMaximum_nonneg f g) (le_of_not_ge hg))
      (Nat.cast_nonneg _))

include hn in
theorem one_le_localMaximum_ultra [IsUltrametricDist K]
    (g : Matrix.GeneralLinearGroup (Fin n) R) : 1 ≤ localMaximum f g := by
  let i : Fin n := ⟨0, hn⟩
  have h1 : (1 : ℝ) ≤ localMaximum f g * localMaximum f g := by
    calc
      1 = ‖f ((g.val * (g⁻¹).val) i i)‖ := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        simp
      _ ≤ ‖fun i j : Fin n => f ((g.val * (g⁻¹).val) i j)‖ :=
        (norm_le_pi_norm (fun j : Fin n => f ((g.val * (g⁻¹).val) i j)) i).trans
          (norm_le_pi_norm (fun k j : Fin n => f ((g.val * (g⁻¹).val) k j)) i)
      _ ≤ localMaximum f g * localMaximum f g := by
        simpa only [localMaximum_inv] using matrixNorm_mul_le_ultra f g.val (g⁻¹).val
          (localMaximum_nonneg f g) (localMaximum_nonneg f g⁻¹)
          (entry_le_localMaximum f g) (entry_le_localMaximum f g⁻¹)
  have h0 := localMaximum_nonneg f g
  nlinarith

end MatrixInverseHeight

namespace AdelicMatrixHeight

open MatrixInverseHeight

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- The finite-place maximum for the actual full adelic matrix and inverse. -/
def finiteLocal (g : AdelicGL F n) (v : FinitePlace F) : ℝ :=
  localMaximum (finiteProjection F v) g

/-- The unnormalized infinite-place maximum; the exponent `v.mult` is applied in the product. -/
def infiniteLocal (g : AdelicGL F n) (v : InfinitePlace F) : ℝ :=
  localMaximum (infiniteProjection F v) g

variable (hn : 0 < n)

include hn in
theorem one_le_finiteLocal (g : AdelicGL F n) (v : FinitePlace F) :
    1 ≤ finiteLocal F n g v :=
  one_le_localMaximum_ultra _ hn g

include hn in
theorem eventually_finiteLocal_eq_one (g : AdelicGL F n) :
    ∀ᶠ v : FinitePlace F in Filter.cofinite, finiteLocal F n g v = 1 := by
  have hval : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i j : Fin n, (g i j).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (g i j).2.property
  have hinv : ∀ᶠ v : FinitePlace F in Filter.cofinite,
      ∀ i j : Fin n, (g⁻¹ i j).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (g⁻¹ i j).2.property
  filter_upwards [hval, hinv] with v hv hi
  apply le_antisymm _ (one_le_finiteLocal F n hn g v)
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    change ‖(g i j).2 v‖ ≤ 1
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hv i j
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    change ‖(g⁻¹ i j).2 v‖ ≤ 1
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hi i j

include hn in
theorem hasFiniteMulSupport_finiteLocal (g : AdelicGL F n) :
    (finiteLocal F n g).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (eventually_finiteLocal_eq_one F n hn g)

/-- The actual normalized product of local matrix-and-inverse maxima. -/
def sourceNorm (g : AdelicGL F n) : ℝ :=
  (∏ v : InfinitePlace F, infiniteLocal F n g v ^ v.mult) *
    ∏ᶠ v : FinitePlace F, finiteLocal F n g v

/-- Dimension scaling makes each archimedean local factor at least one. -/
def height (g : AdelicGL F n) : ℝ :=
  (∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g v) ^ v.mult) *
    ∏ᶠ v : FinitePlace F, finiteLocal F n g v

theorem height_eq_scalar_mul_sourceNorm (g : AdelicGL F n) :
    height F n g =
      (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * sourceNorm F n g := by
  simp only [height, sourceNorm, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

include hn in
theorem one_le_height (g : AdelicGL F n) : 1 ≤ height F n g := by
  apply one_le_mul_of_one_le_of_one_le
  · exact Finset.one_le_prod₀ fun v _ =>
      one_le_pow₀ (one_le_nat_mul_localMaximum (infiniteProjection F v) hn g)
  · exact one_le_finprod (one_le_finiteLocal F n hn g)

@[simp]
theorem height_inv (g : AdelicGL F n) : height F n g⁻¹ = height F n g := by
  simp only [height, finiteLocal, infiniteLocal, localMaximum_inv]

include hn in
theorem height_mul_le (g h : AdelicGL F n) :
    height F n (g * h) ≤ height F n g * height F n h := by
  have harch : ∀ v : InfinitePlace F,
      (n : ℝ) * infiniteLocal F n (g * h) v ≤
        ((n : ℝ) * infiniteLocal F n g v) * ((n : ℝ) * infiniteLocal F n h v) := by
    intro v
    have h := mul_le_mul_of_nonneg_left
      (localMaximum_mul_le (infiniteProjection F v) g h) (Nat.cast_nonneg n)
    dsimp only [infiniteLocal]
    convert h using 1
    ring
  have hfin :
      (∏ᶠ v : FinitePlace F, finiteLocal F n (g * h) v) ≤
        (∏ᶠ v : FinitePlace F, finiteLocal F n g v) *
          ∏ᶠ v : FinitePlace F, finiteLocal F n h v := by
    rw [← finprod_mul_distrib (hasFiniteMulSupport_finiteLocal F n hn g)
      (hasFiniteMulSupport_finiteLocal F n hn h)]
    apply finprod_le_finprod₀ (hasFiniteMulSupport_finiteLocal F n hn (g * h))
      (fun v => (one_le_finiteLocal F n hn (g * h) v).trans' zero_le_one)
      ((hasFiniteMulSupport_finiteLocal F n hn g).mul
        (hasFiniteMulSupport_finiteLocal F n hn h))
    exact fun v => localMaximum_mul_le_ultra (finiteProjection F v) g h
  have hprod :
      (∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n (g * h) v) ^ v.mult) ≤
        (∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g v) ^ v.mult) *
          ∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n h v) ^ v.mult := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _
    · intro v _
      rw [← mul_pow]
      exact pow_le_pow_left₀
        (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) (harch v) _
  change _ ≤
    ((∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n g v) ^ v.mult) *
      ∏ᶠ v : FinitePlace F, finiteLocal F n g v) *
    ((∏ v : InfinitePlace F, ((n : ℝ) * infiniteLocal F n h v) ^ v.mult) *
      ∏ᶠ v : FinitePlace F, finiteLocal F n h v)
  calc
    _ ≤ _ := mul_le_mul hprod hfin (finprod_nonneg fun v => localMaximum_nonneg _ _)
      (mul_nonneg
        (Finset.prod_nonneg fun v _ =>
          pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _)
        (Finset.prod_nonneg fun v _ =>
          pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (localMaximum_nonneg _ _)) _))
    _ = _ := by ring

include hn in
theorem sourceNorm_pos (g : AdelicGL F n) : 0 < sourceNorm F n g := by
  have hscalar : 0 < (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) :=
    pow_pos (by exact_mod_cast hn) _
  have hh := one_le_height F n hn g
  rw [height_eq_scalar_mul_sourceNorm] at hh
  by_contra h
  have hprod := mul_nonpos_of_nonneg_of_nonpos hscalar.le (le_of_not_gt h)
  linarith

end AdelicMatrixHeight

namespace RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {N : ℕ}
  (rho : GroupScheme.MatrixRepresentation G (Fin N))

/-- The specified algebraic representation on actual full adelic points. -/
def adelicMatrix : AdelicGroupPoints F G →ₜ* AdelicGL F N where
  toMonoidHom := (GeneralLinearGroupPoints.adelicHomeomorph F N).toMonoidHom.comp
    (G.affinePointsTarget rho (CommAlgCat.of F (AdeleRing (𝓞 F) F)))
  continuous_toFun := (GeneralLinearGroupPoints.adelicHomeomorph F N).continuous.comp
    (G.continuous_affinePointsTarget _ rho)

/-- Exact normalized matrix-and-inverse local product for the specified representation. -/
def adelicSourceNorm (g : AdelicGroupPoints F G) : ℝ :=
  AdelicMatrixHeight.sourceNorm F N (adelicMatrix F G rho g)

/-- The fixed scalar multiple of the exact source norm with submultiplicative bounds. -/
def adelicHeight (g : AdelicGroupPoints F G) : ℝ :=
  AdelicMatrixHeight.height F N (adelicMatrix F G rho g)

theorem adelicHeight_eq_scalar_mul_sourceNorm (g : AdelicGroupPoints F G) :
    adelicHeight F G rho g =
      (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * adelicSourceNorm F G rho g :=
  AdelicMatrixHeight.height_eq_scalar_mul_sourceNorm F N _

theorem one_le_adelicHeight (hN : 0 < N) (g : AdelicGroupPoints F G) :
    1 ≤ adelicHeight F G rho g := AdelicMatrixHeight.one_le_height F N hN _

theorem adelicSourceNorm_pos (hN : 0 < N) (g : AdelicGroupPoints F G) :
    0 < adelicSourceNorm F G rho g := AdelicMatrixHeight.sourceNorm_pos F N hN _

@[simp]
theorem adelicHeight_inv (g : AdelicGroupPoints F G) :
    adelicHeight F G rho g⁻¹ = adelicHeight F G rho g := by
  simp only [adelicHeight, map_inv, AdelicMatrixHeight.height_inv]

theorem adelicHeight_mul_le (hN : 0 < N) (g h : AdelicGroupPoints F G) :
    adelicHeight F G rho (g * h) ≤ adelicHeight F G rho g * adelicHeight F G rho h := by
  simpa only [adelicHeight, map_mul] using
    AdelicMatrixHeight.height_mul_le F N hN (adelicMatrix F G rho g) (adelicMatrix F G rho h)

section GeneralLinearComparison

variable (n : ℕ)

local notation "GLG" =>
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
local notation "std" => GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)

/-- The standard full adelic representation is exactly the original actual matrix map. -/
@[simp]
theorem adelicMatrix_standard (g : AdelicGroupPoints F GLG) :
    adelicMatrix F GLG std g = GeneralLinearGroupPoints.adelicHomeomorph F n g := by
  change GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of F)
    (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (g ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

@[simp]
theorem adelicSourceNorm_standard (g : AdelicGroupPoints F GLG) :
    adelicSourceNorm F GLG std g =
      AdelicMatrixHeight.sourceNorm F n (GeneralLinearGroupPoints.adelicHomeomorph F n g) := by
  simp only [adelicSourceNorm, adelicMatrix_standard]

@[simp]
theorem adelicHeight_standard (g : AdelicGroupPoints F GLG) :
    adelicHeight F GLG std g =
      AdelicMatrixHeight.height F n (GeneralLinearGroupPoints.adelicHomeomorph F n g) := by
  simp only [adelicHeight, adelicMatrix_standard]

end GeneralLinearComparison

end RepresentationGrowth

end Langlands.Global
