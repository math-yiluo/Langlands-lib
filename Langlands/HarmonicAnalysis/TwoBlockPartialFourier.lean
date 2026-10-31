import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Langlands.HarmonicAnalysis.SelfDualSigmaFiniteProof
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Two-block partial Fourier identity

For a Schwartz–Bruhat function `Φ` on `N × N` matrices split into blocks of sizes
`n0` and `n1`, integrating the full plus-sign Fourier transform of `Φ` over the
lower-left block gives the block Fourier transform of the upper partial integral
`(A, D) ↦ ∫ B, Φ [[A, B], [0, D]] dB`. The proof uses finite entrywise tensor
decompositions; see the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

section Blocks

variable {K : Type uK} {n0 n1 N : ℕ}

/-- The `N × N` matrix with blocks `[[A, B], [C, D]]`, where the coordinates
`Fin n0 ⊕ Fin n1` are identified with `Fin N` by `e`. -/
def blockMatrix (e : Fin n0 ⊕ Fin n1 ≃ Fin N) (A : Matrix (Fin n0) (Fin n0) K)
    (B : Matrix (Fin n0) (Fin n1) K) (C : Matrix (Fin n1) (Fin n0) K)
    (D : Matrix (Fin n1) (Fin n1) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.reindex e e (Matrix.fromBlocks A B C D)

theorem blockMatrix_apply (e : Fin n0 ⊕ Fin n1 ≃ Fin N) (A : Matrix (Fin n0) (Fin n0) K)
    (B : Matrix (Fin n0) (Fin n1) K) (C : Matrix (Fin n1) (Fin n0) K)
    (D : Matrix (Fin n1) (Fin n1) K) (p q : Fin N) :
    blockMatrix e A B C D p q = Matrix.fromBlocks A B C D (e.symm p) (e.symm q) := rfl

/-- An entrywise product over a block matrix splits into the four block products. -/
theorem prod_blockMatrix {M : Type*} [CommMonoid M] (e : Fin n0 ⊕ Fin n1 ≃ Fin N)
    (h : Fin N → Fin N → K → M) (A : Matrix (Fin n0) (Fin n0) K)
    (B : Matrix (Fin n0) (Fin n1) K) (C : Matrix (Fin n1) (Fin n0) K)
    (D : Matrix (Fin n1) (Fin n1) K) :
    ∏ p, ∏ q, h p q (blockMatrix e A B C D p q) =
      ((∏ i, ∏ j, h (e (.inl i)) (e (.inl j)) (A i j)) *
        ∏ i, ∏ j, h (e (.inl i)) (e (.inr j)) (B i j)) *
      ((∏ i, ∏ j, h (e (.inr i)) (e (.inl j)) (C i j)) *
        ∏ i, ∏ j, h (e (.inr i)) (e (.inr j)) (D i j)) := by
  have hrow : ∀ p, ∏ q, h p q (blockMatrix e A B C D p q) =
      ∏ v, h p (e v) (Matrix.fromBlocks A B C D (e.symm p) v) := by
    intro p
    rw [← e.prod_comp]
    simp only [blockMatrix_apply, Equiv.symm_apply_apply]
  simp_rw [hrow]
  rw [← e.prod_comp]
  simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

end Blocks

section EntryProducts

variable {K : Type uK} [AddGroup K] [TopologicalSpace K] [MeasurableSpace K]
  (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure] {r s : ℕ}

/-- Fubini for entrywise products against the nested product measure. -/
theorem integral_rectangularMeasure_entryProduct (f : Fin r → Fin s → K → ℂ) :
    ∫ X, ∏ i, ∏ j, f i j (X i j) ∂RankinSelberg.rectangularMeasure μ r s =
      ∏ i, ∏ j, ∫ t, f i j t ∂μ.measure := by
  unfold RankinSelberg.rectangularMeasure
  exact (integral_fintype_prod_eq_prod (fun i (x : Fin s → K) => ∏ j, f i j (x j))).trans
    (Finset.prod_congr rfl fun i _ => integral_fintype_prod_eq_prod (fun j => f i j))

/-- An entrywise product of integrable scalar functions is integrable. -/
theorem integrable_rectangularMeasure_entryProduct {f : Fin r → Fin s → K → ℂ}
    (hf : ∀ i j, Integrable (f i j) μ.measure) :
    Integrable (fun X : Matrix (Fin r) (Fin s) K => ∏ i, ∏ j, f i j (X i j))
      (RankinSelberg.rectangularMeasure μ r s) := by
  unfold RankinSelberg.rectangularMeasure
  exact Integrable.fintype_prod (f := fun i (x : Fin s → K) => ∏ j, f i j (x j))
    fun i => Integrable.fintype_prod fun j => hf i j

end EntryProducts

section Tensor

variable {K : Type uK} [TopologicalSpace K] {r s : ℕ}

/-- Entry coordinates of a rectangular matrix, indexed through `finProdFinEquiv`. -/
private def entryHomeomorph : (Fin (r * s) → K) ≃ₜ Matrix (Fin r) (Fin s) K where
  toFun y i j := y (finProdFinEquiv (i, j))
  invFun X t := X (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  left_inv y := by
    funext t
    change y (finProdFinEquiv ((finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2)) = y t
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv X := by
    funext i j
    simp
  continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply _
  continuous_invFun := continuous_pi fun t => (continuous_apply _).comp (continuous_apply _)

private theorem entryHomeomorph_symm_apply (X : Matrix (Fin r) (Fin s) K) (i : Fin r)
    (j : Fin s) : (entryHomeomorph (K := K)).symm X (finProdFinEquiv (i, j)) = X i j := by
  change X (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = X i j
  simp

private theorem isLocallyConstant_finsetProd {X ι : Type*} [TopologicalSpace X]
    (S : Finset ι) {F : ι → X → ℂ} (hF : ∀ i, IsLocallyConstant (F i)) :
    IsLocallyConstant (fun x => ∏ i ∈ S, F i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact IsLocallyConstant.const 1
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hF i).comp₂ ih (· * ·)

variable [T2Space K]

/-- The entrywise product `X ↦ ∏ i, ∏ j, g i j (X i j)` of scalar test functions. -/
def entryProductTest (g : Fin r → Fin s → SchwartzBruhat K) :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) := by
  refine ⟨fun X => ∏ i, ∏ j, g i j (X i j), ?_, ?_⟩
  · exact isLocallyConstant_finsetProd _ fun i =>
      isLocallyConstant_finsetProd _ fun j =>
        (g i j).locallyConstant.comp_continuous
          ((continuous_apply j).comp (continuous_apply i))
  · apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ_pi fun i => isCompact_univ_pi fun j => (g i j).hasCompactSupport)
    intro X hX
    simp only [Set.mem_univ_pi]
    intro i j
    apply subset_tsupport (g i j)
    intro hij
    exact hX (Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_univ j) hij))

@[simp] theorem entryProductTest_apply (g : Fin r → Fin s → SchwartzBruhat K)
    (X : Matrix (Fin r) (Fin s) K) :
    entryProductTest g X = ∏ i, ∏ j, g i j (X i j) := rfl

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]

/-- Every rectangular Schwartz–Bruhat function is a finite linear combination of
entrywise products of scalar Schwartz–Bruhat functions. -/
theorem matrixTensorDecomposition (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) :
    ∃ (M : ℕ) (c : Fin M → ℂ) (g : Fin M → Fin r → Fin s → SchwartzBruhat K),
      ∀ X, Φ X = ∑ k, c k * ∏ i, ∏ j, g k i j (X i j) := by
  obtain ⟨M, c, g, hg⟩ :=
    rowTensorDecomposition K (r * s) (Hecke.TestFunction.pullback entryHomeomorph Φ)
  refine ⟨M, c, fun k i j => g k (finProdFinEquiv (i, j)), fun X => ?_⟩
  have h := hg (entryHomeomorph.symm X)
  rw [Hecke.TestFunction.pullback_apply, Homeomorph.apply_symm_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp only [entryHomeomorph_symm_apply]

end Tensor

section Fourier

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) {r s : ℕ}

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
private theorem complex_finsetSum {ι : Type*} (S : Finset ι) (a : ι → K) :
    ψ.complex (∑ i ∈ S, a i) = ∏ i ∈ S, ψ.complex (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K] in
/-- The Fourier kernel of an entrywise product is an entrywise product. -/
theorem entryProduct_mul_character (g : Fin r → Fin s → K → ℂ)
    (a b : Matrix (Fin r) (Fin s) K) :
    (∏ i, ∏ j, g i j (a i j)) * ψ.complex (rectangularPairing a b) =
      ∏ i, ∏ j, (ψ.complex (a i j * b i j) * g i j (a i j)) := by
  rw [rectangularPairing, complex_finsetSum]
  simp_rw [complex_finsetSum]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => mul_comm _ _

omit [IsTopologicalRing K] [BorelSpace K] in
/-- The scalar Fourier integral at zero is the plain integral. -/
theorem fourierIntegral_zero (f : K → ℂ) :
    fourierIntegral ψ μ f 0 = ∫ x, f x ∂μ.measure := by
  simp [fourierIntegral]

variable [SigmaFinite μ.measure]

omit [IsTopologicalRing K] [BorelSpace K] in
/-- The rectangular Fourier integral of an entrywise product is the entrywise
product of scalar Fourier integrals. -/
theorem rectangularFourierIntegral_entryProduct (g : Fin r → Fin s → K → ℂ)
    (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ (fun a => ∏ i, ∏ j, g i j (a i j)) b =
      ∏ i, ∏ j, fourierIntegral ψ μ (g i j) (b i j) := by
  unfold rectangularFourierIntegral
  simp_rw [entryProduct_mul_character]
  exact integral_rectangularMeasure_entryProduct μ
    (fun i j t => ψ.complex (t * b i j) * g i j t)

omit [IsTopologicalRing K] [BorelSpace K] [SigmaFinite μ.measure] in
/-- Scalars pull out of the raw rectangular Fourier integral. -/
theorem rectangularFourierIntegral_const_mul (κ : ℂ) (f : Matrix (Fin r) (Fin s) K → ℂ)
    (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierIntegral ψ μ (fun a => κ * f a) b =
      κ * rectangularFourierIntegral ψ μ f b := by
  unfold rectangularFourierIntegral
  simp_rw [mul_assoc]
  exact integral_const_mul κ _

/-- Fourier integrands of entrywise products of test functions are integrable. -/
theorem integrable_entryProduct_mul_character (g : Fin r → Fin s → SchwartzBruhat K)
    (b : Matrix (Fin r) (Fin s) K) :
    Integrable (fun a : Matrix (Fin r) (Fin s) K =>
      (∏ i, ∏ j, g i j (a i j)) * ψ.complex (rectangularPairing a b))
      (RankinSelberg.rectangularMeasure μ r s) := by
  simp_rw [entryProduct_mul_character]
  exact integrable_rectangularMeasure_entryProduct μ
    (f := fun i j t => ψ.complex (t * b i j) * g i j t)
    fun i j => fourierIntegrand_integrable ψ μ (g i j) (b i j)

end Fourier

section Iterated

/-- Iterated integrals of finite sums of separated products. -/
theorem integral_integral_finsetSum_mul {α β ι : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μa : Measure α} {μb : Measure β} (S : Finset ι)
    (u : ι → α → ℂ) (v : ι → β → ℂ) (hu : ∀ k ∈ S, Integrable (u k) μa)
    (hv : ∀ k ∈ S, Integrable (v k) μb) :
    ∫ a, ∫ b, ∑ k ∈ S, u k a * v k b ∂μb ∂μa =
      ∑ k ∈ S, (∫ a, u k a ∂μa) * ∫ b, v k b ∂μb := by
  have hin : ∀ a, ∫ b, ∑ k ∈ S, u k a * v k b ∂μb = ∑ k ∈ S, u k a * ∫ b, v k b ∂μb := by
    intro a
    rw [integral_finsetSum S fun k hk => (hv k hk).const_mul (u k a)]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  simp_rw [hin]
  rw [integral_finsetSum S fun k hk => (hu k hk).mul_const _]
  exact Finset.sum_congr rfl fun k _ => integral_mul_const _ _

end Iterated

section TwoBlock

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  {n0 n1 N : ℕ} (e : Fin n0 ⊕ Fin n1 ≃ Fin N)

omit [IsTopologicalRing K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
/-- The upper partial integral of one entrywise product. -/
private theorem upper_entryProduct [SigmaFinite μ.measure]
    (g : Fin N → Fin N → SchwartzBruhat K) (A : Matrix (Fin n0) (Fin n0) K)
    (D : Matrix (Fin n1) (Fin n1) K) :
    Integrable (fun B => ∏ p, ∏ q, g p q (blockMatrix e A B 0 D p q))
        (RankinSelberg.rectangularMeasure μ n0 n1) ∧
      ∫ B, ∏ p, ∏ q, g p q (blockMatrix e A B 0 D p q)
          ∂RankinSelberg.rectangularMeasure μ n0 n1 =
        ((∏ i, ∏ j, g (e (.inl i)) (e (.inl j)) (A i j)) *
          ∏ i, ∏ j, ∫ t, g (e (.inl i)) (e (.inr j)) t ∂μ.measure) *
        ((∏ i, ∏ j, g (e (.inr i)) (e (.inl j)) 0) *
          ∏ i, ∏ j, g (e (.inr i)) (e (.inr j)) (D i j)) := by
  simp_rw [prod_blockMatrix e (fun p q t => g p q t)]
  simp only [Matrix.zero_apply]
  refine ⟨((integrable_rectangularMeasure_entryProduct μ fun i j =>
    ((g (e (.inl i)) (e (.inr j))).continuous.integrable_of_hasCompactSupport
      (g (e (.inl i)) (e (.inr j))).hasCompactSupport)).const_mul _).mul_const _, ?_⟩
  rw [integral_mul_const, integral_const_mul, integral_rectangularMeasure_entryProduct]

/-- The lower-left integral of the Fourier transform of one entrywise product. -/
private theorem lower_entryProduct (hsd : IsSelfDual ψ μ)
    (g : Fin N → Fin N → SchwartzBruhat K) (x : Matrix (Fin n0) (Fin n0) K)
    (y : Matrix (Fin n1) (Fin n1) K) :
    Integrable (fun C => ∏ p, ∏ q, fourierIntegral ψ μ (g p q) (blockMatrix e x 0 C y p q))
        (RankinSelberg.rectangularMeasure μ n1 n0) ∧
      ∫ C, ∏ p, ∏ q, fourierIntegral ψ μ (g p q) (blockMatrix e x 0 C y p q)
          ∂RankinSelberg.rectangularMeasure μ n1 n0 =
        ((∏ i, ∏ j, fourierIntegral ψ μ (g (e (.inl i)) (e (.inl j))) (x i j)) *
          ∏ i, ∏ j, ∫ t, g (e (.inl i)) (e (.inr j)) t ∂μ.measure) *
        ((∏ i, ∏ j, g (e (.inr i)) (e (.inl j)) 0) *
          ∏ i, ∏ j, fourierIntegral ψ μ (g (e (.inr i)) (e (.inr j))) (y i j)) := by
  have := selfDualSigmaFinite K ψ μ hsd
  have hint : ∀ f : SchwartzBruhat K, Integrable (fourierIntegral ψ μ f) μ.measure := by
    intro f
    have h := (hsd f).1 0
    simp only [mul_zero, AddChar.map_zero_eq_one, one_mul] at h
    exact h
  have hzero : ∀ f : SchwartzBruhat K, ∫ t, fourierIntegral ψ μ f t ∂μ.measure = f 0 := by
    intro f
    have h := (hsd f).2 0
    rw [neg_zero] at h
    rw [← h, fourierIntegral_zero]
    rfl
  simp_rw [prod_blockMatrix e (fun p q t => fourierIntegral ψ μ (g p q) t)]
  simp only [Matrix.zero_apply, fourierIntegral_zero]
  refine ⟨((integrable_rectangularMeasure_entryProduct μ fun i j =>
    hint (g (e (.inr i)) (e (.inl j)))).mul_const _).const_mul _, ?_⟩
  rw [integral_const_mul, integral_mul_const, integral_rectangularMeasure_entryProduct]
  simp only [hzero]

omit [IsTopologicalRing K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
/-- Block Fourier transforms of finite sums of separated products: the iterated
integral of `(∑ k, a k A * d k D) ψ(⟨A, x⟩) ψ(⟨D, y⟩)` is the corresponding sum of
products of rectangular Fourier integrals. -/
theorem integral_integral_finsetSum_mul_character {ι : Type*} (S : Finset ι)
    (a : ι → Matrix (Fin n0) (Fin n0) K → ℂ) (d : ι → Matrix (Fin n1) (Fin n1) K → ℂ)
    (x : Matrix (Fin n0) (Fin n0) K) (y : Matrix (Fin n1) (Fin n1) K)
    (ha : ∀ k ∈ S, Integrable (fun A => a k A * ψ.complex (rectangularPairing A x))
      (RankinSelberg.rectangularMeasure μ n0 n0))
    (hd : ∀ k ∈ S, Integrable (fun D => d k D * ψ.complex (rectangularPairing D y))
      (RankinSelberg.rectangularMeasure μ n1 n1)) :
    ∫ A, ∫ D, (∑ k ∈ S, a k A * d k D) * ψ.complex (rectangularPairing A x) *
          ψ.complex (rectangularPairing D y)
        ∂RankinSelberg.rectangularMeasure μ n1 n1 ∂RankinSelberg.rectangularMeasure μ n0 n0 =
      ∑ k ∈ S, rectangularFourierIntegral ψ μ (a k) x *
        rectangularFourierIntegral ψ μ (d k) y := by
  have hsplit : ∀ A D, (∑ k ∈ S, a k A * d k D) * ψ.complex (rectangularPairing A x) *
      ψ.complex (rectangularPairing D y) = ∑ k ∈ S,
        (a k A * ψ.complex (rectangularPairing A x)) *
          (d k D * ψ.complex (rectangularPairing D y)) := by
    intro A D
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hsplit]
  exact integral_integral_finsetSum_mul S _ _ ha hd

/-- **Two-block partial Fourier identity.** For a Schwartz–Bruhat function `Φ` on
`N × N` matrices, the integral over the lower-left block `C` of its full plus-sign
Fourier transform at `[[x, 0], [C, y]]` equals the iterated block Fourier integral,
at `(x, y)`, of the upper partial integral `(A, D) ↦ ∫ B, Φ [[A, B], [0, D]] dB`.
All matrix spaces carry the nested product measure of the one scalar measure `μ`,
which is self-dual for `ψ`. -/
theorem integral_rectangularFourierIntegral_blockMatrix_lowerLeft (hsd : IsSelfDual ψ μ)
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)) (x : Matrix (Fin n0) (Fin n0) K)
    (y : Matrix (Fin n1) (Fin n1) K) :
    ∫ C, rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y)
        ∂RankinSelberg.rectangularMeasure μ n1 n0 =
      ∫ A, ∫ D, (∫ B, Φ (blockMatrix e A B 0 D) ∂RankinSelberg.rectangularMeasure μ n0 n1) *
          ψ.complex (rectangularPairing A x) * ψ.complex (rectangularPairing D y)
        ∂RankinSelberg.rectangularMeasure μ n1 n1 ∂RankinSelberg.rectangularMeasure μ n0 n0 := by
  have := selfDualSigmaFinite K ψ μ hsd
  obtain ⟨M, c, g, hΦ⟩ := matrixTensorDecomposition Φ
  have hF : ∀ Y, rectangularFourierIntegral ψ μ Φ Y =
      ∑ k, c k * ∏ p, ∏ q, fourierIntegral ψ μ (g k p q) (Y p q) := by
    intro Y
    have hcongr : (fun a => Φ a * ψ.complex (rectangularPairing a Y)) =
        fun a => ∑ k, c k * ((∏ p, ∏ q, g k p q (a p q)) *
          ψ.complex (rectangularPairing a Y)) := by
      funext a
      rw [hΦ a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
    unfold rectangularFourierIntegral
    rw [hcongr, integral_finsetSum _ fun k _ =>
      (integrable_entryProduct_mul_character ψ μ (g k) Y).const_mul (c k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    exact rectangularFourierIntegral_entryProduct ψ μ (fun p q => g k p q) Y
  -- the coefficient of the `k`-th tensor coming from the `B` and `C` blocks
  set κ : Fin M → ℂ := fun k => c k *
    ((∏ i, ∏ j, ∫ t, g k (e (.inl i)) (e (.inr j)) t ∂μ.measure) *
      ∏ i, ∏ j, g k (e (.inr i)) (e (.inl j)) 0) with hκ
  have hL : ∫ C, rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y)
      ∂RankinSelberg.rectangularMeasure μ n1 n0 =
        ∑ k, κ k * ((∏ i, ∏ j, fourierIntegral ψ μ (g k (e (.inl i)) (e (.inl j))) (x i j)) *
          ∏ i, ∏ j, fourierIntegral ψ μ (g k (e (.inr i)) (e (.inr j))) (y i j)) := by
    simp_rw [hF]
    rw [integral_finsetSum _ fun k _ =>
      ((lower_entryProduct ψ μ e hsd (g k) x y).1).const_mul (c k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (lower_entryProduct ψ μ e hsd (g k) x y).2, hκ]
    ring
  have hP : ∀ A D, ∫ B, Φ (blockMatrix e A B 0 D) ∂RankinSelberg.rectangularMeasure μ n0 n1 =
      ∑ k, (κ k * ∏ i, ∏ j, g k (e (.inl i)) (e (.inl j)) (A i j)) *
        ∏ i, ∏ j, g k (e (.inr i)) (e (.inr j)) (D i j) := by
    intro A D
    simp_rw [hΦ]
    rw [integral_finsetSum _ fun k _ =>
      ((upper_entryProduct μ e (g k) A D).1).const_mul (c k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (upper_entryProduct μ e (g k) A D).2, hκ]
    ring
  simp_rw [hP]
  rw [integral_integral_finsetSum_mul_character ψ μ Finset.univ
    (fun k A => κ k * ∏ i, ∏ j, g k (e (.inl i)) (e (.inl j)) (A i j))
    (fun k D => ∏ i, ∏ j, g k (e (.inr i)) (e (.inr j)) (D i j)) x y
    (fun k _ => by
      simp_rw [mul_assoc]
      exact (integrable_entryProduct_mul_character ψ μ
        (fun i j => g k (e (.inl i)) (e (.inl j))) x).const_mul (κ k))
    (fun k _ => integrable_entryProduct_mul_character ψ μ
        (fun i j => g k (e (.inr i)) (e (.inr j))) y), hL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rectangularFourierIntegral_const_mul, rectangularFourierIntegral_entryProduct,
    rectangularFourierIntegral_entryProduct]
  simp only [hκ]
  ring

/-- The lower-left integrand of the two-block partial Fourier identity is integrable. -/
theorem integrable_rectangularFourierIntegral_blockMatrix_lowerLeft (hsd : IsSelfDual ψ μ)
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)) (x : Matrix (Fin n0) (Fin n0) K)
    (y : Matrix (Fin n1) (Fin n1) K) :
    Integrable (fun C => rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y))
      (RankinSelberg.rectangularMeasure μ n1 n0) := by
  have := selfDualSigmaFinite K ψ μ hsd
  obtain ⟨M, c, g, hΦ⟩ := matrixTensorDecomposition Φ
  have hF : ∀ Y, rectangularFourierIntegral ψ μ Φ Y =
      ∑ k, c k * ∏ p, ∏ q, fourierIntegral ψ μ (g k p q) (Y p q) := by
    intro Y
    have hcongr : (fun a => Φ a * ψ.complex (rectangularPairing a Y)) =
        fun a => ∑ k, c k * ((∏ p, ∏ q, g k p q (a p q)) *
          ψ.complex (rectangularPairing a Y)) := by
      funext a
      rw [hΦ a, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
    unfold rectangularFourierIntegral
    rw [hcongr, integral_finsetSum _ fun k _ =>
      (integrable_entryProduct_mul_character ψ μ (g k) Y).const_mul (c k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    exact rectangularFourierIntegral_entryProduct ψ μ (fun p q => g k p q) Y
  simp_rw [hF]
  exact integrable_finsetSum _ fun k _ =>
    ((lower_entryProduct ψ μ e hsd (g k) x y).1).const_mul (c k)

/-- Tensor form of the two-block partial Fourier identity: if the upper partial
integral of `Φ` is the finite sum `∑ k, Ψ0 k A * Ψ1 k D`, then the lower-left integral
of the full Fourier transform of `Φ` is `∑ k, Ψ0^(x) Ψ1^(y)`, with the plus-sign
rectangular Fourier integrals on the two diagonal blocks. -/
theorem integral_rectangularFourierIntegral_blockMatrix_lowerLeft_of_tensor
    (hsd : IsSelfDual ψ μ) (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)) {ι : Type*}
    (S : Finset ι) (Ψ0 : ι → SchwartzBruhat (Matrix (Fin n0) (Fin n0) K))
    (Ψ1 : ι → SchwartzBruhat (Matrix (Fin n1) (Fin n1) K))
    (hP : ∀ A D, ∫ B, Φ (blockMatrix e A B 0 D) ∂RankinSelberg.rectangularMeasure μ n0 n1 =
      ∑ k ∈ S, Ψ0 k A * Ψ1 k D)
    (x : Matrix (Fin n0) (Fin n0) K) (y : Matrix (Fin n1) (Fin n1) K) :
    ∫ C, rectangularFourierIntegral ψ μ Φ (blockMatrix e x 0 C y)
        ∂RankinSelberg.rectangularMeasure μ n1 n0 =
      ∑ k ∈ S, rectangularFourierIntegral ψ μ (Ψ0 k) x *
        rectangularFourierIntegral ψ μ (Ψ1 k) y := by
  rw [integral_rectangularFourierIntegral_blockMatrix_lowerLeft ψ μ e hsd Φ x y]
  simp_rw [hP]
  exact integral_integral_finsetSum_mul_character ψ μ S (fun k => Ψ0 k) (fun k => Ψ1 k) x y
    (fun k _ => rectangularFourierEquiv_integrable ψ μ n0 n0 hsd (Ψ0 k) x)
    (fun k _ => rectangularFourierEquiv_integrable ψ μ n1 n1 hsd (Ψ1 k) y)

omit [IsTopologicalRing K] in
/-- The upper partial integral `(A, D) ↦ ∫ B, Φ [[A, B], [0, D]] dB` of a
Schwartz–Bruhat function is a finite sum of products of Schwartz–Bruhat functions
of `A` and of `D`. -/
theorem exists_upperPartialIntegral_tensor [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Matrix (Fin N) (Fin N) K)) :
    ∃ (M : ℕ) (Ψ0 : Fin M → SchwartzBruhat (Matrix (Fin n0) (Fin n0) K))
      (Ψ1 : Fin M → SchwartzBruhat (Matrix (Fin n1) (Fin n1) K)),
      ∀ A D, ∫ B, Φ (blockMatrix e A B 0 D) ∂RankinSelberg.rectangularMeasure μ n0 n1 =
        ∑ k, Ψ0 k A * Ψ1 k D := by
  obtain ⟨M, c, g, hΦ⟩ := matrixTensorDecomposition Φ
  refine ⟨M, fun k => (c k *
      ((∏ i, ∏ j, ∫ t, g k (e (.inl i)) (e (.inr j)) t ∂μ.measure) *
        ∏ i, ∏ j, g k (e (.inr i)) (e (.inl j)) 0)) •
      entryProductTest (fun i j => g k (e (.inl i)) (e (.inl j))),
    fun k => entryProductTest (fun i j => g k (e (.inr i)) (e (.inr j))), fun A D => ?_⟩
  simp_rw [hΦ]
  rw [integral_finsetSum _ fun k _ =>
    ((upper_entryProduct μ e (g k) A D).1).const_mul (c k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, (upper_entryProduct μ e (g k) A D).2]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, entryProductTest_apply]
  ring

end TwoBlock

end Langlands.HarmonicAnalysis
