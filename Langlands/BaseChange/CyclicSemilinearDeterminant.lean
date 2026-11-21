import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.Algebra.SeparableTensorProof
import Langlands.Algebra.WeightedCyclicDeterminant
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Determinant of a cyclic semilinear defect -/

namespace Langlands.BaseChange

open scoped Matrix TensorProduct

universe u v w

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l : ℕ}

/-- Apply a field automorphism to each coordinate, as a base-field linear map. -/
def coordinateFieldAut (σ : E ≃ₐ[F] E) (ι : Type w) : Module.End F (ι → E) :=
  LinearMap.pi fun i => σ.toLinearMap.comp (LinearMap.proj i)

@[simp]
theorem coordinateFieldAut_apply (σ : E ≃ₐ[F] E) {ι : Type w} (x : ι → E) (i : ι) :
    coordinateFieldAut σ ι x i = σ (x i) := rfl

private noncomputable def cyclicPowerEquiv (h : IsCyclicAlgebra σ l) :
    Fin l ≃ (E ≃ₐ[F] E) := by
  classical
  let : FiniteDimensional F E := h.1
  let : IsGalois F E := h.isGalois
  let f : Fin l → E ≃ₐ[F] E := fun i => σ ^ (i : ℕ)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ) _ _ hij
    · simp [h.2.2.2.1, i.isLt]
    · simp [h.2.2.2.1, j.isLt]
  have hcard : Fintype.card (Fin l) = Fintype.card (E ≃ₐ[F] E) := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, h.2.1]
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

private noncomputable def cyclicTensorCoordinates (h : IsCyclicAlgebra σ l)
    (ι : Type w) [Fintype ι] [DecidableEq ι] : (E ⊗[F] (ι → E)) ≃ₗ[E] (Fin l → ι → E) := by
  let : FiniteDimensional F E := h.1
  let : IsGalois F E := h.isGalois
  let e := AlgEquiv.ofBijective (Algebra.SeparableTensor.embeddingEvaluation F E E)
    (Algebra.SeparableTensor.embeddingEvaluationStatement F E E
      (Normal.splits (inferInstance : Normal F E)))
  let t := (cyclicPowerEquiv h).trans (Algebra.IsAlgebraic.algEquivEquivAlgHom F E).toEquiv
  let reindex : (ι → (E →ₐ[F] E) → E) ≃ₗ[E] (Fin l → ι → E) :=
    { toFun := fun x i j => x j (t i)
      invFun := fun x j a => x (t.symm a) j
      left_inv := fun x => by funext j a; simp only [t.apply_symm_apply]
      right_inv := fun x => by funext i j; simp only [t.symm_apply_apply]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (TensorProduct.piRight F E E (fun _ : ι => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : ι => e.toLinearEquiv)).trans reindex)

private theorem cyclicTensorCoordinates_tmul (h : IsCyclicAlgebra σ l)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (c : E) (x : ι → E) (i : Fin l) (j : ι) :
    cyclicTensorCoordinates h ι (c ⊗ₜ x) i j = c * (σ ^ (i : ℕ)) (x j) := rfl

private theorem pow_finRotate_apply {d : ℕ} (h : IsCyclicAlgebra σ (d + 1))
    (i : Fin (d + 1)) (x : E) :
    (σ ^ ((finRotate (d + 1) i) : ℕ)) x = (σ ^ (i : ℕ)) (σ x) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [finRotate_last]
    change (σ ^ 0) x = (σ ^ d) (σ x)
    rw [← AlgEquiv.mul_apply, ← pow_succ, h.pow_eq_one, pow_zero]
  · rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j), pow_succ, AlgEquiv.mul_apply]

/-- The determinant of `1 - A ∘ σ` over the base field, viewed in the extension, is the
matrix determinant of `1 - A σ(A) ⋯ σ^(l-1)(A)`. The weights act on column vectors,
and the displayed list product is ordered from exponent zero to `l - 1`. -/
theorem IsCyclicAlgebra.det_cyclicSemilinearDefect (h : IsCyclicAlgebra σ l)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) :
    algebraMap F E (LinearMap.det (1 - (Matrix.toLinAlgEquiv' A).restrictScalars F *
      coordinateFieldAut σ ι)) =
    Matrix.det (1 - ((List.range l).map fun i => A.map (σ ^ i : E ≃ₐ[F] E)).prod) := by
  let : FiniteDimensional F E := h.1
  let : FiniteDimensional F (ι → E) := FiniteDimensional.trans F E (ι → E)
  cases l with
  | zero => exact (Nat.not_lt_zero _ h.pos).elim
  | succ d =>
    let D : Module.End F (ι → E) :=
      1 - (Matrix.toLinAlgEquiv' A).restrictScalars F * coordinateFieldAut σ ι
    let e := cyclicTensorCoordinates h ι
    let W : Fin (d + 1) → Module.End E (ι → E) :=
      fun i => Matrix.toLinAlgEquiv' (A.map (σ ^ (i : ℕ) : E ≃ₐ[F] E))
    have hD : e.toLinearMap.comp (D.baseChange E) =
        (Algebra.weightedCycleDefect W).comp e.toLinearMap := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul c x =>
        funext i j
        simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, e,
          LinearEquiv.coe_coe, cyclicTensorCoordinates_tmul, Algebra.weightedCycleDefect_apply]
        change c * (σ ^ (i : ℕ)) (x j - (A *ᵥ fun k => σ (x k)) j) =
          c * (σ ^ (i : ℕ)) (x j) -
            ((A.map (σ ^ (i : ℕ) : E ≃ₐ[F] E)) *ᵥ fun k =>
              c * (σ ^ ((finRotate (d + 1) i) : ℕ)) (x k)) j
        simp only [map_sub, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
          pow_finRotate_apply h, mul_sub, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
    have hc : e.toLinearMap.comp ((D.baseChange E).comp e.symm.toLinearMap) =
        Algebra.weightedCycleDefect W := by
      apply LinearMap.ext
      intro z
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
        DFunLike.congr_fun hD (e.symm z)
    let L := (List.range (d + 1)).map fun i => A.map (σ ^ i : E ≃ₐ[F] E)
    have hp : (List.ofFn W).prod = Matrix.toLinAlgEquiv' L.prod := by
      rw [map_list_prod]
      congr 1
      have hrange : (List.finRange (d + 1)).map (fun i : Fin (d + 1) => (i : ℕ)) =
          List.range (d + 1) := by simp
      simp only [L, ← hrange, List.map_map, List.ofFn_eq_map, W]
      rfl
    change algebraMap F E D.det = Matrix.det (1 - L.prod)
    calc
      _ = (D.baseChange E).det := (LinearMap.det_baseChange D).symm
      _ = (Algebra.weightedCycleDefect W).det := by rw [← hc, LinearMap.det_conj]
      _ = Matrix.det (1 - L.prod) := by
        rw [Algebra.det_weightedCycleDefect, hp, ← map_one Matrix.toLinAlgEquiv', ← map_sub]
        exact LinearMap.det_toLin' (1 - L.prod)

end Langlands.BaseChange
