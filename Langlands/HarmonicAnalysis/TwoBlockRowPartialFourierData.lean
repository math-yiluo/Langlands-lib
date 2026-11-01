import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# The split-row partial Fourier integral (JPSS 1983, Section 4.7)

JPSS 1983, Section 4.7, printed page 413, sets
`Φ~(ξ, v) = ∫_{F^{t_1}} Φ[(w, v)] ψ(ξ ᵗw) dw` for `ξ, w ∈ F^{t_1}` and `v ∈ F^{t_2}`.
This module constructs that raw integral for an arbitrary placement
`e : Fin a ⊕ Fin b ≃ Fin N` of the two blocks of a row, together with the coordinate
packaging, the Schwartz–Bruhat slices, integrability, the complex-linear map into all
functions, the joined tensor formula and the first-block translation and shear laws.

It asserts no Schwartz–Bruhat closure, inversion or Mellin identity.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

universe uR uK

/-! ### Block coordinates of a row -/

section Coordinates

variable {R : Type uR} {a b N : ℕ} (e : Fin a ⊕ Fin b ≃ Fin N)

/-- The row whose coordinate `e (inl i)` is `w i` and whose coordinate `e (inr j)` is `v j`. -/
def join (w : Fin a → R) (v : Fin b → R) : Fin N → R :=
  fun j => Sum.elim w v (e.symm j)

/-- The first block `i ↦ z (e (inl i))` of a row. -/
def first (z : Fin N → R) : Fin a → R :=
  fun i => z (e (Sum.inl i))

/-- The second block `j ↦ z (e (inr j))` of a row. -/
def second (z : Fin N → R) : Fin b → R :=
  fun j => z (e (Sum.inr j))

theorem join_apply (w : Fin a → R) (v : Fin b → R) (j : Fin N) :
    join e w v j = Sum.elim w v (e.symm j) := rfl

@[simp] theorem first_apply (z : Fin N → R) (i : Fin a) : first e z i = z (e (Sum.inl i)) :=
  rfl

@[simp] theorem second_apply (z : Fin N → R) (j : Fin b) : second e z j = z (e (Sum.inr j)) :=
  rfl

@[simp] theorem join_inl (w : Fin a → R) (v : Fin b → R) (i : Fin a) :
    join e w v (e (Sum.inl i)) = w i := by
  simp [join]

@[simp] theorem join_inr (w : Fin a → R) (v : Fin b → R) (j : Fin b) :
    join e w v (e (Sum.inr j)) = v j := by
  simp [join]

@[simp] theorem first_join (w : Fin a → R) (v : Fin b → R) : first e (join e w v) = w := by
  funext i
  simp

@[simp] theorem second_join (w : Fin a → R) (v : Fin b → R) : second e (join e w v) = v := by
  funext j
  simp

@[simp] theorem join_first_second (z : Fin N → R) : join e (first e z) (second e z) = z := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  cases s <;> simp

theorem join_add [Add R] (w w' : Fin a → R) (v v' : Fin b → R) :
    join e (w + w') (v + v') = join e w v + join e w' v' := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  cases s <;> simp

theorem join_smul {S : Type*} [SMul S R] (c : S) (w : Fin a → R) (v : Fin b → R) :
    join e (c • w) (c • v) = c • join e w v := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  cases s <;> simp

section Topology

variable [TopologicalSpace R]

theorem continuous_join :
    Continuous (fun p : (Fin a → R) × (Fin b → R) => join e p.1 p.2) := by
  refine continuous_pi fun j => ?_
  rcases h : e.symm j with i | k
  · simp only [join_apply, h, Sum.elim_inl]
    exact (continuous_apply i).comp continuous_fst
  · simp only [join_apply, h, Sum.elim_inr]
    exact (continuous_apply k).comp continuous_snd

theorem continuous_first : Continuous (first e : (Fin N → R) → Fin a → R) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_second : Continuous (second e : (Fin N → R) → Fin b → R) :=
  continuous_pi fun _ => continuous_apply _

end Topology

variable (R) in
/-- The block decomposition `(w, v) ↦ join e w v` of a row, as a continuous linear
equivalence; its inverse is `z ↦ (first e z, second e z)`. -/
def joinEquiv [Semiring R] [TopologicalSpace R] :
    ((Fin a → R) × (Fin b → R)) ≃L[R] (Fin N → R) where
  toFun p := join e p.1 p.2
  invFun z := (first e z, second e z)
  map_add' p q := join_add e p.1 q.1 p.2 q.2
  map_smul' c p := join_smul e c p.1 p.2
  left_inv p := by simp
  right_inv z := by simp
  continuous_toFun := continuous_join e
  continuous_invFun := (continuous_first e).prodMk (continuous_second e)

@[simp] theorem joinEquiv_apply [Semiring R] [TopologicalSpace R]
    (p : (Fin a → R) × (Fin b → R)) : joinEquiv R e p = join e p.1 p.2 := rfl

@[simp] theorem joinEquiv_symm_apply [Semiring R] [TopologicalSpace R] (z : Fin N → R) :
    (joinEquiv R e).symm z = (first e z, second e z) := rfl

/-- The explicit row shear `z ↦ join e (first e z + second e z ⬝ X) (second e z)`, for
`X : Matrix (Fin b) (Fin a) R`. It changes only the first block. -/
def shear [Semiring R] (X : Matrix (Fin b) (Fin a) R) (z : Fin N → R) : Fin N → R :=
  join e (first e z + Matrix.vecMul (second e z) X) (second e z)

section Shear

variable [Semiring R]

@[simp] theorem first_shear (X : Matrix (Fin b) (Fin a) R) (z : Fin N → R) :
    first e (shear e X z) = first e z + Matrix.vecMul (second e z) X := by
  simp [shear]

@[simp] theorem second_shear (X : Matrix (Fin b) (Fin a) R) (z : Fin N → R) :
    second e (shear e X z) = second e z := by
  simp [shear]

@[simp] theorem shear_join (X : Matrix (Fin b) (Fin a) R) (w : Fin a → R) (v : Fin b → R) :
    shear e X (join e w v) = join e (w + Matrix.vecMul v X) v := by
  simp [shear]

@[simp] theorem shear_zero (z : Fin N → R) : shear e 0 z = z := by
  simp [shear]

theorem shear_add (X Y : Matrix (Fin b) (Fin a) R) (z : Fin N → R) :
    shear e (X + Y) z = shear e X (shear e Y z) := by
  simp only [shear, first_join, second_join, Matrix.vecMul_add]
  congr 1
  abel

end Shear

theorem shear_neg_shear [Ring R] (X : Matrix (Fin b) (Fin a) R) (z : Fin N → R) :
    shear e (-X) (shear e X z) = z := by
  rw [← shear_add, neg_add_cancel, shear_zero]

theorem shear_shear_neg [Ring R] (X : Matrix (Fin b) (Fin a) R) (z : Fin N → R) :
    shear e X (shear e (-X) z) = z := by
  rw [← shear_add, add_neg_cancel, shear_zero]

end Coordinates

/-! ### The contiguous placement -/

section Contiguous

variable {R : Type uR} {a b N : ℕ} (hab : a + b = N)

/-- The placement of the first block in the first `a` coordinates and of the second block
in the last `b` coordinates. -/
def contiguousEquiv : Fin a ⊕ Fin b ≃ Fin N :=
  finSumFinEquiv.trans (finCongr hab)

@[simp] theorem contiguousEquiv_inl (i : Fin a) :
    contiguousEquiv hab (Sum.inl i) = Fin.cast hab (Fin.castAdd b i) := rfl

@[simp] theorem contiguousEquiv_inr (j : Fin b) :
    contiguousEquiv hab (Sum.inr j) = Fin.cast hab (Fin.natAdd a j) := rfl

theorem first_contiguousEquiv (z : Fin N → R) (i : Fin a) :
    first (contiguousEquiv hab) z i = z (Fin.cast hab (Fin.castAdd b i)) := rfl

theorem second_contiguousEquiv (z : Fin N → R) (j : Fin b) :
    second (contiguousEquiv hab) z j = z (Fin.cast hab (Fin.natAdd a j)) := rfl

theorem join_contiguousEquiv_castAdd (w : Fin a → R) (v : Fin b → R) (i : Fin a) :
    join (contiguousEquiv hab) w v (Fin.cast hab (Fin.castAdd b i)) = w i := by
  rw [← contiguousEquiv_inl, join_inl]

theorem join_contiguousEquiv_natAdd (w : Fin a → R) (v : Fin b → R) (j : Fin b) :
    join (contiguousEquiv hab) w v (Fin.cast hab (Fin.natAdd a j)) = v j := by
  rw [← contiguousEquiv_inr, join_inr]

theorem join_contiguousEquiv (w : Fin a → R) (v : Fin b → R) :
    join (contiguousEquiv hab) w v = fun j => Fin.append w v (Fin.cast hab.symm j) := by
  funext j
  obtain ⟨s, rfl⟩ := (contiguousEquiv hab).surjective j
  cases s <;> simp [join_contiguousEquiv_castAdd, join_contiguousEquiv_natAdd]

end Contiguous

/-! ### The row pairing over the two blocks -/

section Pairing

variable {K : Type uK} [Field K] {a b N d : ℕ}

theorem rowPairing_add_left (x y z : Fin d → K) :
    rowPairing (x + y) z = rowPairing x z + rowPairing y z := by
  simp [rowPairing, add_mul, Finset.sum_add_distrib]

theorem rowPairing_neg_left (x z : Fin d → K) : rowPairing (-x) z = -rowPairing x z := by
  simp [rowPairing, Finset.sum_neg_distrib]

/-- The row pairing is additive over the two blocks of any placement. -/
theorem rowPairing_join (e : Fin a ⊕ Fin b ≃ Fin N) (w ξ : Fin a → K) (v η : Fin b → K) :
    rowPairing (join e w v) (join e ξ η) = rowPairing w ξ + rowPairing v η := by
  unfold rowPairing
  rw [← Equiv.sum_comp e (fun j => join e w v j * join e ξ η j), Fintype.sum_sum_type]
  simp

/-- The character of the row pairing is the product of the coordinate characters. -/
theorem complex_rowPairing [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K)
    (x y : Fin d → K) : ψ.complex (rowPairing x y) = ∏ i, ψ.complex (x i * y i) := by
  classical
  unfold rowPairing
  induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

variable (e : Fin a ⊕ Fin b ≃ Fin N)

/-- The first-block translate `z ↦ f (join e (first e z + c) (second e z))`. -/
def firstTranslate (c : Fin a → K) (f : (Fin N → K) → ℂ) : (Fin N → K) → ℂ :=
  fun z => f (join e (first e z + c) (second e z))

@[simp] theorem firstTranslate_join (c : Fin a → K) (f : (Fin N → K) → ℂ) (w : Fin a → K)
    (v : Fin b → K) : firstTranslate e c f (join e w v) = f (join e (w + c) v) := by
  simp [firstTranslate]

end Pairing

/-! ### The partial Fourier integral -/

section Fourier

variable {K : Type uK} [Field K] [TopologicalSpace K] [MeasurableSpace K] {a b N : ℕ}

/-- JPSS 1983, printed page 413: the plus-sign Fourier integral in the first block of a row,
with the second block `v` held fixed:
`∫ w, ψ(⟨w, ξ⟩) f (join e w v) d(rowMeasure μ a)`. -/
def rowPartialFourierIntegral (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    (e : Fin a ⊕ Fin b ≃ Fin N) (f : (Fin N → K) → ℂ) (ξ : Fin a → K) (v : Fin b → K) : ℂ :=
  ∫ w, ψ.complex (rowPairing w ξ) * f (join e w v) ∂rowMeasure μ a

section Evaluation

variable (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  (e : Fin a ⊕ Fin b ≃ Fin N)

theorem rowPartialFourierIntegral_apply (f : (Fin N → K) → ℂ) (ξ : Fin a → K)
    (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e f ξ v =
      ∫ w, ψ.complex (rowPairing w ξ) * f (join e w v) ∂rowMeasure μ a := rfl

/-- The partial integral is the row Fourier integral of the first-block slice. -/
theorem rowPartialFourierIntegral_eq_rowFourierIntegral (f : (Fin N → K) → ℂ)
    (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e f ξ v =
      rowFourierIntegral ψ μ a (fun w => f (join e w v)) ξ := rfl

end Evaluation

variable [IsTopologicalRing K] [BorelSpace K]

/-- Translation invariance of the product row measure. -/
instance rowMeasure_isAddRightInvariant (μ : AdditiveHaarMeasure K) [SigmaFinite μ.measure]
    (d : ℕ) : (rowMeasure μ d).IsAddRightInvariant :=
  inferInstanceAs (Measure.pi fun _ : Fin d => μ.measure).IsAddRightInvariant

variable (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  (e : Fin a ⊕ Fin b ≃ Fin N)

/-- Translating the first block by `c` before integrating multiplies by `ψ(-⟨c, ξ⟩)`.
This holds for every function, with no integrability hypothesis. -/
theorem integral_join_add [SigmaFinite μ.measure] (f : (Fin N → K) → ℂ) (c ξ : Fin a → K)
    (v : Fin b → K) :
    ∫ w, ψ.complex (rowPairing w ξ) * f (join e (w + c) v) ∂rowMeasure μ a =
      ψ.complex (-rowPairing c ξ) * rowPartialFourierIntegral ψ μ e f ξ v := by
  have h := integral_add_right_eq_self (μ := rowMeasure μ a)
    (fun w => ψ.complex (rowPairing (w - c) ξ) * f (join e w v)) c
  simp only [add_sub_cancel_right] at h
  rw [h, rowPartialFourierIntegral, ← integral_const_mul]
  congr 1
  funext w
  rw [sub_eq_add_neg, rowPairing_add_left, rowPairing_neg_left, AddChar.map_add_eq_mul]
  ring

/-- The first-block translation law, for every function `f`. -/
theorem rowPartialFourierIntegral_firstTranslate [SigmaFinite μ.measure]
    (f : (Fin N → K) → ℂ) (c ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e (firstTranslate e c f) ξ v =
      ψ.complex (-rowPairing c ξ) * rowPartialFourierIntegral ψ μ e f ξ v := by
  rw [← integral_join_add]
  simp only [rowPartialFourierIntegral, firstTranslate_join]

/-- The inverse-phase covariance of the partial integral under the row shear, for every
function `f`. -/
theorem rowPartialFourierIntegral_comp_shear [SigmaFinite μ.measure] (f : (Fin N → K) → ℂ)
    (X : Matrix (Fin b) (Fin a) K) (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e (f ∘ shear e X) ξ v =
      ψ.complex (-rowPairing (Matrix.vecMul v X) ξ) * rowPartialFourierIntegral ψ μ e f ξ v := by
  rw [← integral_join_add]
  simp only [rowPartialFourierIntegral, Function.comp_apply, shear_join]

end Fourier

/-! ### Schwartz–Bruhat slices and joined tensors -/

section SchwartzBruhatCoordinates

variable {K : Type uK} [TopologicalSpace K] [T2Space K] {a b N : ℕ}
  (e : Fin a ⊕ Fin b ≃ Fin N)

/-- The first-block slice `w ↦ Φ (join e w v)` of a full-row Schwartz–Bruhat function. -/
def slice (Φ : SchwartzBruhat (Fin N → K)) (v : Fin b → K) : SchwartzBruhat (Fin a → K) :=
  SchwartzBruhat.compLeftInverse Φ (fun w => join e w v) (first e)
    ((continuous_join e).comp (continuous_id.prodMk continuous_const)) (continuous_first e)
    (fun w => first_join e w v)

@[simp] theorem slice_apply (Φ : SchwartzBruhat (Fin N → K)) (v : Fin b → K) (w : Fin a → K) :
    slice e Φ v w = Φ (join e w v) := rfl

/-- The coordinate transport of a full-row function to the product of the two block spaces. -/
def blockTransport (Φ : SchwartzBruhat (Fin N → K)) :
    SchwartzBruhat ((Fin a → K) × (Fin b → K)) :=
  SchwartzBruhat.compLeftInverse Φ (fun p => join e p.1 p.2) (fun z => (first e z, second e z))
    (continuous_join e) ((continuous_first e).prodMk (continuous_second e)) (fun p => by simp)

@[simp] theorem blockTransport_apply (Φ : SchwartzBruhat (Fin N → K))
    (p : (Fin a → K) × (Fin b → K)) : blockTransport e Φ p = Φ (join e p.1 p.2) := rfl

/-- The joined pure tensor `z ↦ α (first e z) * β (second e z)`. -/
def joinedTensor (α : SchwartzBruhat (Fin a → K)) (β : SchwartzBruhat (Fin b → K)) :
    SchwartzBruhat (Fin N → K) :=
  SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor α β) (fun z => (first e z, second e z))
    (fun p => join e p.1 p.2) ((continuous_first e).prodMk (continuous_second e))
    (continuous_join e) (fun z => join_first_second e z)

@[simp] theorem joinedTensor_apply (α : SchwartzBruhat (Fin a → K))
    (β : SchwartzBruhat (Fin b → K)) (z : Fin N → K) :
    joinedTensor e α β z = α (first e z) * β (second e z) := rfl

@[simp] theorem joinedTensor_join (α : SchwartzBruhat (Fin a → K))
    (β : SchwartzBruhat (Fin b → K)) (w : Fin a → K) (v : Fin b → K) :
    joinedTensor e α β (join e w v) = α w * β v := by
  simp

/-- Every full-row Schwartz–Bruhat function is a finite sum of joined tensors. -/
theorem exists_joinedTensor_expansion (Φ : SchwartzBruhat (Fin N → K)) :
    ∃ (M : ℕ) (α : Fin M → SchwartzBruhat (Fin a → K)) (β : Fin M → SchwartzBruhat (Fin b → K)),
      Φ = ∑ j, joinedTensor e (α j) (β j) := by
  obtain ⟨M, α, β, h⟩ := SchwartzBruhat.exists_tensor_expansion (blockTransport e Φ)
  refine ⟨M, α, β, ?_⟩
  apply Subtype.ext
  funext z
  have hz := h (first e z) (second e z)
  simp only [blockTransport_apply, join_first_second] at hz
  rw [hz, Submodule.coe_sum, Finset.sum_apply]
  rfl

end SchwartzBruhatCoordinates

/-! ### The partial Fourier integral of Schwartz–Bruhat functions -/

section SchwartzBruhatFourier

variable {K : Type uK} [Field K] [TopologicalSpace K] [T2Space K] [MeasurableSpace K]
  {a b N d : ℕ} (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  (e : Fin a ⊕ Fin b ≃ Fin N)

/-- The partial integral of `Φ` is the row Fourier integral of its slice. -/
theorem rowPartialFourierIntegral_eq_rowFourierIntegral_slice (Φ : SchwartzBruhat (Fin N → K))
    (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e Φ ξ v = rowFourierIntegral ψ μ a (slice e Φ v) ξ := rfl

/-- The tensor formula `(α ⊗ β)~(ξ, v) = α^(ξ) β(v)`. -/
theorem rowPartialFourierIntegral_joinedTensor (α : SchwartzBruhat (Fin a → K))
    (β : SchwartzBruhat (Fin b → K)) (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e (joinedTensor e α β) ξ v =
      rowFourierIntegral ψ μ a α ξ * β v := by
  simp only [rowPartialFourierIntegral, joinedTensor_join, rowFourierIntegral, ← mul_assoc]
  exact integral_mul_const _ _

variable [IsTopologicalRing K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K]

/-- The Fourier integrand of a row Schwartz–Bruhat function is integrable for the product
row measure. -/
theorem schwartz_rowFourierIntegrand_integrable [SigmaFinite μ.measure]
    (f : SchwartzBruhat (Fin d → K)) (ξ : Fin d → K) :
    Integrable (fun w => ψ.complex (rowPairing w ξ) * f w) (rowMeasure μ d) := by
  obtain ⟨M, c, g, hg⟩ := rowTensorDecomposition K d f
  have he : (fun w => ψ.complex (rowPairing w ξ) * f w) =
      fun w => ∑ j : Fin M, c j * ∏ i : Fin d, (ψ.complex (w i * ξ i) * g j i (w i)) := by
    funext w
    rw [hg, complex_rowPairing, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [he]
  refine integrable_finsetSum _ fun j _ => Integrable.const_mul ?_ (c j)
  exact Integrable.fintype_prod (μ := fun _ : Fin d => μ.measure)
    (f := fun i x => ψ.complex (x * ξ i) * g j i x)
    fun i => fourierIntegrand_integrable ψ μ (g j i) (ξ i)

/-- The integrand of the partial Fourier integral of a full-row Schwartz–Bruhat function is
integrable for every `ξ` and `v`. -/
theorem rowPartialFourierIntegrand_integrable [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Fin N → K)) (ξ : Fin a → K) (v : Fin b → K) :
    Integrable (fun w => ψ.complex (rowPairing w ξ) * Φ (join e w v)) (rowMeasure μ a) :=
  schwartz_rowFourierIntegrand_integrable ψ μ (slice e Φ v) ξ

/-- The complex-linear map `Φ ↦ ((ξ, v) ↦ Φ~(ξ, v))` into all functions. Its image is not
asserted to consist of Schwartz–Bruhat functions. -/
def rowPartialFourierTransform [SigmaFinite μ.measure] :
    SchwartzBruhat (Fin N → K) →ₗ[ℂ] ((Fin a → K) × (Fin b → K) → ℂ) where
  toFun Φ p := rowPartialFourierIntegral ψ μ e Φ p.1 p.2
  map_add' Φ Φ' := by
    funext p
    change (∫ w, ψ.complex (rowPairing w p.1) * (Φ (join e w p.2) + Φ' (join e w p.2))
        ∂rowMeasure μ a) =
      (∫ w, ψ.complex (rowPairing w p.1) * Φ (join e w p.2) ∂rowMeasure μ a) +
      ∫ w, ψ.complex (rowPairing w p.1) * Φ' (join e w p.2) ∂rowMeasure μ a
    simp_rw [mul_add]
    exact integral_add (rowPartialFourierIntegrand_integrable ψ μ e Φ p.1 p.2)
      (rowPartialFourierIntegrand_integrable ψ μ e Φ' p.1 p.2)
  map_smul' c Φ := by
    funext p
    change (∫ w, ψ.complex (rowPairing w p.1) * (c * Φ (join e w p.2)) ∂rowMeasure μ a) =
      c * ∫ w, ψ.complex (rowPairing w p.1) * Φ (join e w p.2) ∂rowMeasure μ a
    simp_rw [mul_left_comm (ψ.complex _) c]
    exact integral_const_mul c _

@[simp] theorem rowPartialFourierTransform_apply [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Fin N → K)) (p : (Fin a → K) × (Fin b → K)) :
    rowPartialFourierTransform ψ μ e Φ p = rowPartialFourierIntegral ψ μ e Φ p.1 p.2 := rfl

/-- The partial integral of a finite sum of joined tensors. -/
theorem rowPartialFourierIntegral_sum_joinedTensor [SigmaFinite μ.measure] {M : ℕ}
    (α : Fin M → SchwartzBruhat (Fin a → K)) (β : Fin M → SchwartzBruhat (Fin b → K))
    (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e (∑ j, joinedTensor e (α j) (β j) : SchwartzBruhat _) ξ v =
      ∑ j, rowFourierIntegral ψ μ a (α j) ξ * β j v := by
  have h := congrFun (map_sum (rowPartialFourierTransform ψ μ e)
    (fun j => joinedTensor e (α j) (β j)) Finset.univ) (ξ, v)
  simpa [Finset.sum_apply, rowPartialFourierIntegral_joinedTensor] using h

/-- Every full-row Schwartz–Bruhat function has a joined-tensor expansion, and its partial
Fourier integral is the corresponding finite sum. -/
theorem exists_rowPartialFourierIntegral_expansion [SigmaFinite μ.measure]
    (Φ : SchwartzBruhat (Fin N → K)) :
    ∃ (M : ℕ) (α : Fin M → SchwartzBruhat (Fin a → K)) (β : Fin M → SchwartzBruhat (Fin b → K)),
      Φ = ∑ j, joinedTensor e (α j) (β j) ∧
      ∀ ξ v, rowPartialFourierIntegral ψ μ e Φ ξ v =
        ∑ j, rowFourierIntegral ψ μ a (α j) ξ * β j v := by
  obtain ⟨M, α, β, h⟩ := exists_joinedTensor_expansion e Φ
  refine ⟨M, α, β, h, fun ξ v => ?_⟩
  rw [h]
  exact rowPartialFourierIntegral_sum_joinedTensor ψ μ e α β ξ v

end SchwartzBruhatFourier

end Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
