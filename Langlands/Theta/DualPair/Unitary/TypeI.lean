import Langlands.Theta.DualPair.TypeI
import Langlands.Group.Unitary.Classical
import Langlands.Theta.DualPair.Unitary.Pair
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The unitary dual pair on `W ⊗ V`

GKT §10.5.2 (**Theorem 10.28**, p. 288) in Case `3₊` with `W` split: the symplectic space
`𝕎 = M_{α×2ν}(E) = M_{α×ν}(E)²` of `Langlands.Theta.DualPair.Unitary.Form` and
`Langlands.Theta.DualPair.Unitary.LeraySplitting`, with the action of `U(ν, ν)` by `w ↦ w g⁻¹` and
of `U(Q)` by `w ↦ h w`, is the tensor product construction of `Langlands.Theta.DualPair.TypeI` for
the hyperbolic skew-Hermitian space `W = E^{ν ⊕ ν}` and the Hermitian space `V = (E^α, Q)` of
`Langlands.Group.Unitary.Classical`.

* `unitaryTensorEquiv F α ν : W ⊗[E] V ≃ₗ[F] M_{α×ν}(E) × M_{α×ν}(E)`, `w ⊗ v ↦ v w` (the matrix
  `(vᵢ wⱼ)`, split into its first and last `ν` columns);
* `polarizedForm_unitaryTensorEquiv`: it carries the book's form `tensorForm`
  (`⟪w ⊗ v, w' ⊗ v'⟫ = tr_{E/F}(⟨w, w'⟩ (v, v')_Q)`, here `unitaryTensorForm`) to
  `polarizedForm (hermitianTracePairing c Q)`. The proof passes through the Library's form
  `hermitianSymplecticForm` (`½ tr_{E/F}`) by `hermitianSymplecticForm_fromCols` and
  `hermitianTracePairing = 2 • hermitianPairing`;
* `toTraceIsometry_unitaryTensorEquiv`: `toTraceIsometry g` is `g ⊗ 1` for the isometry
  `toIsometryGroup g` of `W`; `toTraceIsometryOfForm_unitaryTensorEquiv`: `toTraceIsometryOfForm h`
  is `1 ⊗ h`; `pairToTraceIsometry_unitaryTensorEquiv`: the pair acts by `g ⊗ h`.
-/

noncomputable section

open Matrix TensorProduct

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
  (hc : Function.Involutive c) {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν]
  [DecidableEq ν] {Q : Matrix α α E}

theorem _root_.Langlands.UnitaryGroup.conj_ringInvo_algebraMap (a : F) :
    RingInvo.conj (ringInvo c hc) (algebraMap F E a) = algebraMap F E a :=
  c.commutes a

variable (α ν E) in
/-- The first and last `ν` columns: `(α → ν ⊕ ν → E) ≃ M_{α×ν}(E) × M_{α×ν}(E)`. -/
def matrixColsEquiv : (α → ν ⊕ ν → E) ≃ₗ[E] Matrix α ν E × Matrix α ν E where
  toFun m := (Matrix.of fun i j => m i (.inl j), Matrix.of fun i j => m i (.inr j))
  invFun p i := Sum.elim (p.1 i) (p.2 i)
  map_add' m m' := rfl
  map_smul' a m := rfl
  left_inv m := by funext i k; rcases k with k | k <;> rfl
  right_inv p := rfl

variable (F α ν) in
/-- **`W ⊗ V = M_{α×2ν}(E)`**: the `F`-linear isomorphism `w ⊗ v ↦ v w`
(`(w ⊗ v)ᵢⱼ = vᵢ wⱼ`), from the tensor product of the row vectors `W = E^{ν ⊕ ν}` and the column
vectors `V = E^α` to `M_{α×ν}(E) × M_{α×ν}(E)` (first and last `ν` columns). -/
def unitaryTensorEquiv :
    (ν ⊕ ν → E) ⊗[E] (α → E) ≃ₗ[F] Matrix α ν E × Matrix α ν E :=
  ((TensorProduct.piScalarRight E E (ν ⊕ ν → E) α).trans (matrixColsEquiv E α ν)).restrictScalars F

omit [Fintype ν] [DecidableEq ν] in
theorem unitaryTensorEquiv_tmul (w : ν ⊕ ν → E) (v : α → E) :
    unitaryTensorEquiv F α ν (w ⊗ₜ v) =
      (Matrix.of fun i j => v i * w (.inl j), Matrix.of fun i j => v i * w (.inr j)) := by
  rfl

omit [Fintype ν] [DecidableEq ν] in
theorem fromCols_unitaryTensorEquiv_tmul (w : ν ⊕ ν → E) (v : α → E) :
    fromCols (unitaryTensorEquiv F α ν (w ⊗ₜ v)).1 (unitaryTensorEquiv F α ν (w ⊗ₜ v)).2 =
      Matrix.of fun i j => v i * w j := by
  ext i (j | j) <;> rfl

omit [DecidableEq α] in
/-- `hermitianTensor` of two pure tensors `v w`, `v' w'` is the product of the forms. -/
theorem hermitianTensor_of_mul (w w' : ν ⊕ ν → E) (v v' : α → E) :
    hermitianTensor c Q (hyperbolicForm ν E) (Matrix.of fun i j => v i * w j)
        (Matrix.of fun i j => v' i * w' j) =
      (w ⬝ᵥ (hyperbolicForm ν E *ᵥ fun j => c (w' j))) * (v ⬝ᵥ (Q *ᵥ fun j => c (v' j))) := by
  simp only [hermitianTensor, of_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum,
    map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

variable (ν) in
/-- The book's symplectic form `tr_{E/F}(⟨w, w'⟩ (v, v')_Q)` on `W ⊗ V` for the hyperbolic
skew-Hermitian `W = E^{ν ⊕ ν}` and the Hermitian `V = (E^α, Q)` (`tensorForm`). -/
abbrev unitaryTensorForm (hQ : Matrix.IsHermitianFor c Q) :
    LinearMap.BilinForm F ((ν ⊕ ν → E) ⊗[E] (α → E)) :=
  tensorForm (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
    (hermitianFormOf c hc Q hQ)


/-- **The book's form on `W ⊗ V` is the polarized form of `hermitianTracePairing`** (GKT Theorem
10.28 in Case `3₊`): under `unitaryTensorEquiv`, `tensorForm` (`tr_{E/F}(⟨w, w'⟩ (v, v')_Q)`) is
`polarizedForm (hermitianTracePairing c Q)`; equivalently twice the Library's form
`hermitianSymplecticForm` (`½ tr_{E/F}`). -/
theorem polarizedForm_unitaryTensorEquiv [NeZero (2 : F)] (hQ : Matrix.IsHermitianFor c Q)
    (x y : (ν ⊕ ν → E) ⊗[E] (α → E)) :
    polarizedForm (hermitianTracePairing c Q) (unitaryTensorEquiv F α ν x)
        (unitaryTensorEquiv F α ν y) =
      unitaryTensorForm hc ν hQ x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul w v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul w' v' =>
      rw [polarizedForm_eq_mul (2 : F) (hermitianTracePairing_eq_mul c Q),
        ← hermitianSymplecticForm_fromCols c hc hQ, fromCols_unitaryTensorEquiv_tmul,
        fromCols_unitaryTensorEquiv_tmul, hermitianSymplecticForm, hermitianTensor_of_mul,
        ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, tensorForm_tmul]
      rfl

/-- **`U(ν, ν)` acts on `W ⊗ V` by `g ⊗ 1`**: under `unitaryTensorEquiv`, the Library's
`toTraceIsometry g` (`w ↦ w g⁻¹` on `M_{α×2ν}(E)`) is `g ⊗ 1` for the isometry `toIsometryGroup g`
of `W` (`tensorIsometryLeft`). -/
theorem toTraceIsometry_unitaryTensorEquiv (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) (x : (ν ⊕ ν → E) ⊗[E] (α → E)) :
    (toTraceIsometry hc hQ g : (Matrix α ν E × Matrix α ν E) ≃ₗ[F] Matrix α ν E × Matrix α ν E)
        (unitaryTensorEquiv F α ν x) =
      unitaryTensorEquiv F α ν
        ((tensorIsometryLeft (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
          (hermitianFormOf c hc Q hQ) (toIsometryGroup c hc g) :
            isometryGroup (unitaryTensorForm hc ν hQ)).1 x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul w v =>
    rw [tensorIsometryLeft_apply_tmul, toTraceIsometry_apply, rightMulInvEquiv_apply,
      toIsometryGroup_apply, fromCols_unitaryTensorEquiv_tmul, unitaryTensorEquiv_tmul]
    refine Prod.ext ?_ ?_ <;> ext i j <;>
      simp [mul_apply, vecMul, dotProduct, mul_add, Finset.mul_sum, mul_assoc]

/-- **`U(Q)` acts on `W ⊗ V` by `1 ⊗ h`**: under `unitaryTensorEquiv`, the Library's
`toTraceIsometryOfForm h` (left multiplication by `h`) is `1 ⊗ h` for the isometry
`toIsometryGroupOfForm h` of `V` (`tensorIsometryRight`). -/
theorem toTraceIsometryOfForm_unitaryTensorEquiv (hQ : Matrix.IsHermitianFor c Q)
    (h : ofForm c Q) (x : (ν ⊕ ν → E) ⊗[E] (α → E)) :
    (toTraceIsometryOfForm ν h :
        (Matrix α ν E × Matrix α ν E) ≃ₗ[F] Matrix α ν E × Matrix α ν E)
        (unitaryTensorEquiv F α ν x) =
      unitaryTensorEquiv F α ν
        ((tensorIsometryRight (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
          (hermitianFormOf c hc Q hQ) (toIsometryGroupOfForm c hc hQ h) :
            isometryGroup (unitaryTensorForm hc ν hQ)).1 x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul w v =>
    rw [tensorIsometryRight_apply_tmul, toTraceIsometryOfForm_apply, leftMulEquiv_apply,
      toIsometryGroupOfForm_apply, unitaryTensorEquiv_tmul, unitaryTensorEquiv_tmul]
    refine Prod.ext ?_ ?_ <;> ext i j <;>
      simp [mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

/-- **The dual pair `(U(ν, ν), U(Q))` acts on `W ⊗ V` by `g ⊗ h`** (GKT Theorem 10.28 in Case
`3₊`): under `unitaryTensorEquiv`, the Library's `pairToTraceIsometry (g, h)` (`w ↦ h w g⁻¹`) is
`tensorIsometry (g, h)`. -/
theorem pairToTraceIsometry_unitaryTensorEquiv (hQ : Matrix.IsHermitianFor c Q)
    (gh : ofForm c (hyperbolicForm ν E) × ofForm c Q) (x : (ν ⊕ ν → E) ⊗[E] (α → E)) :
    (pairToTraceIsometry hc hQ gh :
        (Matrix α ν E × Matrix α ν E) ≃ₗ[F] Matrix α ν E × Matrix α ν E)
        (unitaryTensorEquiv F α ν x) =
      unitaryTensorEquiv F α ν
        ((tensorIsometry (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
          (hermitianFormOf c hc Q hQ)
            (toIsometryGroup c hc gh.1, toIsometryGroupOfForm c hc hQ gh.2) :
            isometryGroup (unitaryTensorForm hc ν hQ)).1 x) := by
  have e : tensorIsometry (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
      (hermitianFormOf c hc Q hQ) (toIsometryGroup c hc gh.1, toIsometryGroupOfForm c hc hQ gh.2) =
      tensorIsometryLeft (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
        (hermitianFormOf c hc Q hQ) (toIsometryGroup c hc gh.1) *
      tensorIsometryRight (conj_ringInvo_algebraMap hc) (hyperbolicHermitianForm c hc ν)
        (hermitianFormOf c hc Q hQ) (toIsometryGroupOfForm c hc hQ gh.2) := by
    rw [tensorIsometryLeft, tensorIsometryRight, MonoidHom.comp_apply, MonoidHom.comp_apply,
      ← map_mul]
    congr 1
  rw [e, pairToTraceIsometry_apply, Subgroup.coe_mul, LinearEquiv.mul_apply,
    toTraceIsometryOfForm_unitaryTensorEquiv hc hQ, toTraceIsometry_unitaryTensorEquiv hc hQ]
  rfl

end Langlands.Theta
