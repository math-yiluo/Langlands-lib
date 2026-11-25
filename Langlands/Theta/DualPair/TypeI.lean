import Langlands.LinearAlgebra.EpsilonHermitian.Isotropic
import Langlands.LinearAlgebra.EpsilonHermitian.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Trace.Basic

/-!
# Type I dual pairs: the symplectic space `W ⊗ V`

GKT §10.3.3 (the tensor product construction, p. 277) and §10.5.2 (**Theorem 10.28**, p. 288), for
a field `K` with an involution `τ` whose fixed field contains `F` (the book's Cases 1 and 3:
`D = E = F` with `τ = id`, and `D = E` a quadratic extension with its conjugation).

The spaces are left `K`-modules with forms linear in the first variable (the convention of
`Langlands.LinearAlgebra.EpsilonHermitian.Basic`): `hW` is `-ε`-Hermitian on `W`, `hV` is
`ε`-Hermitian on `V`.

* `tensorHermitianForm hW hV`: the `K`-valued form `⟨w ⊗ v, w' ⊗ v'⟩ = hW(w, w') hV(v, v')` on
  `W ⊗[K] V`, `ε₁ε₂`-Hermitian for an `ε₁`- and an `ε₂`-Hermitian form, non-degenerate when both
  are (`tensorHermitianForm_nondegenerate`);
* `tensorForm hτ hW hV`: the `F`-bilinear form `⟪x, y⟫ = tr_{K/F} ⟨x, y⟩`, so
  `⟪w ⊗ v, w' ⊗ v'⟫ = tr_{K/F}(hW(w, w') hV(v, v'))`: alternating (`isAlt_tensorForm`) and
  non-degenerate for `K / F` finite separable (`nondegenerate_tensorForm`);
* `tensorIsometry hτ hW hV : U(W) × U(V) →* Sp(W ⊗ V)`, `(g, h) ↦ g ⊗ h`, and the two embeddings
  `tensorIsometryLeft` (`g ↦ g ⊗ 1`) and `tensorIsometryRight` (`h ↦ 1 ⊗ h`), whose images commute.

The book writes `W` as a right space and the form as `tr_{D/F}(⟨w, w'⟩ · (v, v')^τ)`; for a
commutative `D` this is `tensorForm` for the left spaces `^τW` (`d · w = w d^τ`, the same values)
and `V` with the twisted action `d ⋆ v = d^τ v` and the form `(v, v')^τ`; see the page.
-/

noncomputable section

open TensorProduct Module

namespace Langlands.Theta

open Langlands.RingInvo (conj conj_conj conjRingHom conjRingHom_apply)
open Langlands.LinearMap.BilinForm (isometryGroup)

section Hermitian

variable {K : Type*} [Field K] {τ : _root_.RingInvo K} {ε₁ ε₂ : ℤˣ}
  {W : Type*} [AddCommGroup W] [Module K W] {V : Type*} [AddCommGroup V] [Module K V]
  (hW : EpsilonHermitianForm τ ε₁ W) (hV : EpsilonHermitianForm τ ε₂ V)

/-- The `K`-linear functional `w ⊗ v ↦ hW(w, w') hV(v, v')` of `W ⊗ V`, as a `τ`-semilinear
function of `w' ⊗ v'`. -/
def tensorPairing : W ⊗[K] V →ₛₗ[conjRingHom τ] (W ⊗[K] V →ₗ[K] K) :=
  TensorProduct.lift <| LinearMap.mk₂'ₛₗ (conjRingHom τ) (conjRingHom τ)
    (fun w' v' => TensorProduct.lift <| LinearMap.mk₂ K (fun w v => hW w w' * hV v v')
      (fun w₁ w₂ v => by rw [hW.map_add_left, add_mul])
      (fun a w v => by rw [hW.map_smul_left, smul_eq_mul, mul_assoc])
      (fun w v₁ v₂ => by rw [hV.map_add_left, mul_add])
      (fun a w v => by rw [hV.map_smul_left, smul_eq_mul, mul_left_comm]))
    (fun w₁ w₂ v' => TensorProduct.ext' fun w v => by
      simp [hW.map_add_right, add_mul])
    (fun a w' v' => TensorProduct.ext' fun w v => by
      simp [hW.map_smul_right, mul_comm, mul_assoc])
    (fun w' v₁ v₂ => TensorProduct.ext' fun w v => by
      simp [hV.map_add_right, mul_add])
    (fun a w' v' => TensorProduct.ext' fun w v => by
      simp [hV.map_smul_right, mul_comm, mul_left_comm])

@[simp] theorem tensorPairing_tmul_tmul (w w' : W) (v v' : V) :
    tensorPairing hW hV (w' ⊗ₜ v') (w ⊗ₜ v) = hW w w' * hV v v' := rfl

/-- The swap relation of `tensorPairing`. -/
theorem tensorPairing_swap (x y : W ⊗[K] V) :
    tensorPairing hW hV x y = (((ε₁ * ε₂ : ℤˣ) : ℤ) : K) * conj τ (tensorPairing hW hV y x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp [map_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul w' v' =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp [map_add, hy, hy', mul_add]
    | tmul w v =>
      rw [tensorPairing_tmul_tmul, tensorPairing_tmul_tmul, hW.conj_swap w', hV.conj_swap v',
        RingInvo.conj_mul, Units.val_mul, Int.cast_mul]
      ring

/-- **The tensor product of an `ε₁`-Hermitian and an `ε₂`-Hermitian form** on `W ⊗ V`:
`⟨w ⊗ v, w' ⊗ v'⟩ = hW(w, w') hV(v, v')`, an `ε₁ ε₂`-Hermitian form. -/
def tensorHermitianForm : EpsilonHermitianForm τ (ε₁ * ε₂) (W ⊗[K] V) where
  toFun x y := tensorPairing hW hV y x
  map_add_left' x y _ := map_add _ x y
  map_smul_left' a x _ := map_smul _ a x
  conj_swap' x y := tensorPairing_swap hW hV x y

@[simp] theorem tensorHermitianForm_apply (x y : W ⊗[K] V) :
    tensorHermitianForm hW hV x y = tensorPairing hW hV y x := rfl

theorem tensorHermitianForm_tmul (w w' : W) (v v' : V) :
    tensorHermitianForm hW hV (w ⊗ₜ v) (w' ⊗ₜ v') = hW w w' * hV v v' := rfl

variable {hW hV}

/-- A non-degenerate form on a finite-dimensional space has a dual basis: `h(bᵢ, cⱼ) = δᵢⱼ`. -/
theorem _root_.Langlands.EpsilonHermitianForm.exists_dual_basis {ε : ℤˣ} {U : Type*}
    [AddCommGroup U] [Module K U] [FiniteDimensional K U] {h : EpsilonHermitianForm τ ε U}
    (hh : h.Nondegenerate) {ι : Type*} [DecidableEq ι] (b : Basis ι K U) :
    ∃ c : ι → U, ∀ i j, h (b i) (c j) = if i = j then 1 else 0 := by
  have hd : Disjoint (⊤ : Submodule K U) (h.orthogonal ⊤) := by
    rw [EpsilonHermitianForm.orthogonal_top hh]; exact disjoint_bot_right
  obtain ⟨c, -, hc⟩ := EpsilonHermitianForm.exists_dual_family hd rfl
    (b.map (LinearEquiv.ofTop ⊤ rfl).symm)
  exact ⟨c, fun i j => by simpa using hc i j⟩

/-- **The tensor product of non-degenerate forms is non-degenerate.** -/
theorem tensorHermitianForm_nondegenerate [FiniteDimensional K W] [FiniteDimensional K V]
    (hhW : hW.Nondegenerate) (hhV : hV.Nondegenerate) :
    (tensorHermitianForm hW hV).Nondegenerate := by
  classical
  intro x hx
  set b := Module.finBasis K W
  set d := Module.finBasis K V
  obtain ⟨c, hc⟩ := EpsilonHermitianForm.exists_dual_basis hhW b
  obtain ⟨e, he⟩ := EpsilonHermitianForm.exists_dual_basis hhV d
  set B := b.tensorProduct d
  have key : ∀ k, B.coord k = tensorPairing hW hV (c k.1 ⊗ₜ e k.2) := by
    rintro ⟨i, j⟩
    refine B.ext fun ⟨i', j'⟩ => ?_
    rw [Basis.coord_apply, Basis.repr_self, show B (i', j') = b i' ⊗ₜ d j' from
      b.tensorProduct_apply d i' j', tensorPairing_tmul_tmul, hc, he, Finsupp.single_apply]
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp [h1, h2]
  refine B.ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply, ← Basis.coord_apply, key]
  exact hx (c k.1 ⊗ₜ e k.2)

variable (hW hV) in
theorem tensorHermitianForm_congr (g : hW.isometryGroup) (h : hV.isometryGroup)
    (x y : W ⊗[K] V) :
    tensorHermitianForm hW hV (TensorProduct.congr (g : W ≃ₗ[K] W) (h : V ≃ₗ[K] V) x)
      (TensorProduct.congr (g : W ≃ₗ[K] W) (h : V ≃ₗ[K] V) y) = tensorHermitianForm hW hV x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, EpsilonHermitianForm.map_add_left,
      EpsilonHermitianForm.map_add_left, hx, hx']
  | tmul w v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [map_add, EpsilonHermitianForm.map_add_right,
        EpsilonHermitianForm.map_add_right, hy, hy']
    | tmul w' v' =>
      rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, tensorHermitianForm_tmul,
        tensorHermitianForm_tmul]
      simp

variable (hW hV) in
/-- `(g, h) ↦ g ⊗ h`, from `U(W) × U(V)` to the isometry group of the tensor product form. -/
def tensorHermitianIsometry :
    hW.isometryGroup × hV.isometryGroup →* (tensorHermitianForm hW hV).isometryGroup where
  toFun g := ⟨TensorProduct.congr (g.1 : W ≃ₗ[K] W) (g.2 : V ≃ₗ[K] V),
    tensorHermitianForm_congr hW hV g.1 g.2⟩
  map_one' := Subtype.ext <| LinearEquiv.toLinearMap_injective <| TensorProduct.ext' fun _ _ => by
    simp
  map_mul' _ _ := Subtype.ext <| LinearEquiv.toLinearMap_injective <|
    TensorProduct.ext' fun _ _ => by simp

variable (hW hV) in
@[simp] theorem tensorHermitianIsometry_apply_tmul (g : hW.isometryGroup × hV.isometryGroup)
    (w : W) (v : V) :
    ((tensorHermitianIsometry hW hV g : (tensorHermitianForm hW hV).isometryGroup) :
      W ⊗[K] V ≃ₗ[K] W ⊗[K] V) (w ⊗ₜ v) = (g.1 : W ≃ₗ[K] W) w ⊗ₜ (g.2 : V ≃ₗ[K] V) v :=
  TensorProduct.congr_tmul _ _ _ _

end Hermitian

section Form

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] {τ : _root_.RingInvo K}
  {ε : ℤˣ}
  {W : Type*} [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W]
  {V : Type*} [AddCommGroup V] [Module K V]
  (hτ : ∀ a : F, conj τ (algebraMap F K a) = algebraMap F K a)
  (hW : EpsilonHermitianForm τ (-ε) W) (hV : EpsilonHermitianForm τ ε V)


/-- **The symplectic form of a Type I dual pair** (GKT Theorem 10.28): on `W ⊗ V`,
`⟪w ⊗ v, w' ⊗ v'⟫ = tr_{K/F}(hW(w, w') hV(v, v'))`. -/
def tensorForm : LinearMap.BilinForm F (W ⊗[K] V) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F K (tensorHermitianForm hW hV x y))
    (fun x x' y => by rw [EpsilonHermitianForm.map_add_left, map_add])
    (fun a x y => by
      rw [← algebraMap_smul K a x, EpsilonHermitianForm.map_smul_left, ← smul_eq_mul,
        algebraMap_smul, map_smul])
    (fun x y y' => by rw [EpsilonHermitianForm.map_add_right, map_add])
    (fun a x y => by
      rw [← algebraMap_smul K a y, EpsilonHermitianForm.map_smul_right, hτ, mul_comm,
        ← smul_eq_mul, algebraMap_smul, map_smul])

theorem tensorForm_apply (x y : W ⊗[K] V) :
    tensorForm hτ hW hV x y = Algebra.trace F K (tensorHermitianForm hW hV x y) := rfl

theorem tensorForm_tmul (w w' : W) (v v' : V) :
    tensorForm hτ hW hV (w ⊗ₜ v) (w' ⊗ₜ v') = Algebra.trace F K (hW w w' * hV v v') := rfl

/-- The involution `τ` of `K`, fixing `F`, as an automorphism of the `F`-algebra `K`. -/
def _root_.Langlands.RingInvo.conjAlgEquiv : K ≃ₐ[F] K :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (conjRingHom τ) (conjRingHom τ)
    (RingHom.ext fun a => conj_conj τ a) (RingHom.ext fun a => conj_conj τ a)) hτ

@[simp] theorem _root_.Langlands.RingInvo.conjAlgEquiv_apply (a : K) :
    RingInvo.conjAlgEquiv hτ a = conj τ a := rfl

include hτ in
/-- `tr_{K/F}(a^τ) = tr_{K/F}(a)` for an involution `τ` fixing `F`. -/
theorem _root_.Langlands.RingInvo.trace_conj (a : K) :
    Algebra.trace F K (conj τ a) = Algebra.trace F K a :=
  Algebra.trace_eq_of_algEquiv (RingInvo.conjAlgEquiv hτ) a

/-- `⟪y, x⟫ = -⟪x, y⟫`. -/
theorem tensorForm_swap (x y : W ⊗[K] V) : tensorForm hτ hW hV y x = -tensorForm hτ hW hV x y := by
  have hc : (((-ε * ε : ℤˣ) : ℤ) : K) = -1 := by simp
  rw [tensorForm_apply, tensorForm_apply, EpsilonHermitianForm.conj_swap, hc, neg_one_mul,
    map_neg, RingInvo.trace_conj hτ]

/-- **The form of a Type I pair is alternating** (GKT Theorem 10.28). -/
theorem isAlt_tensorForm [NeZero (2 : F)] : (tensorForm hτ hW hV).IsAlt := by
  intro x
  have h := tensorForm_swap hτ hW hV x x
  have h2 : (2 : F) * tensorForm hτ hW hV x x = 0 := by rw [two_mul]; nth_rw 1 [h]; ring
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- **The form of a Type I pair is non-degenerate** (GKT Theorem 10.28), for a finite separable
`K / F` and non-degenerate `hW`, `hV` on finite-dimensional spaces. -/
theorem nondegenerate_tensorForm [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [FiniteDimensional K W] [FiniteDimensional K V] (hhW : hW.Nondegenerate)
    (hhV : hV.Nondegenerate) : (tensorForm hτ hW hV).Nondegenerate := by
  have hsep : ∀ x : W ⊗[K] V, (∀ y, tensorForm hτ hW hV x y = 0) → x = 0 := by
    intro x hx
    refine tensorHermitianForm_nondegenerate hhW hhV x fun y => ?_
    by_contra hne
    apply Algebra.trace_ne_zero F K
    refine LinearMap.ext fun t => ?_
    have := hx ((conj τ ((tensorHermitianForm hW hV x y)⁻¹ * t)) • y)
    rw [tensorForm_apply, EpsilonHermitianForm.map_smul_right, conj_conj, ← mul_assoc,
      mul_inv_cancel₀ hne, one_mul] at this
    rw [this, LinearMap.zero_apply]
  refine ⟨hsep, fun y hy => hsep y fun x => ?_⟩
  rw [tensorForm_swap, hy x, neg_zero]

/-- **The homomorphism `(g, h) ↦ g ⊗ h`** of `U(W) × U(V)` into the symplectic group of
`(W ⊗ V, ⟪,⟫)` (GKT Theorem 10.28). -/
def tensorIsometry :
    hW.isometryGroup × hV.isometryGroup →* isometryGroup (tensorForm hτ hW hV) where
  toFun g := ⟨((tensorHermitianIsometry hW hV g : (tensorHermitianForm hW hV).isometryGroup) :
      W ⊗[K] V ≃ₗ[K] W ⊗[K] V).restrictScalars F, fun x y => by
    rw [tensorForm_apply, tensorForm_apply]
    exact congrArg _ ((tensorHermitianIsometry hW hV g).2 x y)⟩
  map_one' := Subtype.ext <| LinearEquiv.ext fun x => by
    change ((tensorHermitianIsometry hW hV 1 : (tensorHermitianForm hW hV).isometryGroup) :
      W ⊗[K] V ≃ₗ[K] W ⊗[K] V) x = x
    rw [map_one]; rfl
  map_mul' g g' := Subtype.ext <| LinearEquiv.ext fun x => by
    change ((tensorHermitianIsometry hW hV (g * g') : (tensorHermitianForm hW hV).isometryGroup) :
      W ⊗[K] V ≃ₗ[K] W ⊗[K] V) x = _
    rw [map_mul]; rfl

@[simp] theorem tensorIsometry_apply_tmul (g : hW.isometryGroup × hV.isometryGroup) (w : W)
    (v : V) :
    ((tensorIsometry hτ hW hV g : isometryGroup (tensorForm hτ hW hV)) :
      W ⊗[K] V ≃ₗ[F] W ⊗[K] V) (w ⊗ₜ v) = (g.1 : W ≃ₗ[K] W) w ⊗ₜ (g.2 : V ≃ₗ[K] V) v :=
  TensorProduct.congr_tmul _ _ _ _

/-- The embedding `g ↦ g ⊗ 1` of `U(W)`. -/
def tensorIsometryLeft : hW.isometryGroup →* isometryGroup (tensorForm hτ hW hV) :=
  (tensorIsometry hτ hW hV).comp (MonoidHom.inl _ _)

/-- The embedding `h ↦ 1 ⊗ h` of `U(V)`. -/
def tensorIsometryRight : hV.isometryGroup →* isometryGroup (tensorForm hτ hW hV) :=
  (tensorIsometry hτ hW hV).comp (MonoidHom.inr _ _)

@[simp] theorem tensorIsometryLeft_apply_tmul (g : hW.isometryGroup) (w : W) (v : V) :
    ((tensorIsometryLeft hτ hW hV g : isometryGroup (tensorForm hτ hW hV)) :
      W ⊗[K] V ≃ₗ[F] W ⊗[K] V) (w ⊗ₜ v) = (g : W ≃ₗ[K] W) w ⊗ₜ v :=
  TensorProduct.congr_tmul _ _ _ _

@[simp] theorem tensorIsometryRight_apply_tmul (h : hV.isometryGroup) (w : W) (v : V) :
    ((tensorIsometryRight hτ hW hV h : isometryGroup (tensorForm hτ hW hV)) :
      W ⊗[K] V ≃ₗ[F] W ⊗[K] V) (w ⊗ₜ v) = w ⊗ₜ (h : V ≃ₗ[K] V) v :=
  TensorProduct.congr_tmul _ _ _ _

/-- The images of `U(W)` and `U(V)` commute. -/
theorem commute_tensorIsometryLeft_tensorIsometryRight (g : hW.isometryGroup)
    (h : hV.isometryGroup) :
    Commute (tensorIsometryLeft hτ hW hV g) (tensorIsometryRight hτ hW hV h) := by
  rw [Commute, SemiconjBy, tensorIsometryLeft, tensorIsometryRight, MonoidHom.comp_apply,
    MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1

end Form

end Langlands.Theta
