import Langlands.Algebra.BrauerSplitting

/-! # Semilinear transport of splitting and Brauer periods -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.Brauer

section Tensor

variable {K L A B C D : Type*} [Field K] [Field L] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra K A] [Algebra K B] [Algebra L C] [Algebra L D]
  (k : K ≃+* L) (f : A ≃+* C) (g : B ≃+* D)
  (hf : ∀ x, f (algebraMap K A x) = algebraMap L C (k x))
  (hg : ∀ x, g (algebraMap K B x) = algebraMap L D (k x))

include hf hg in
/-- Tensor two ring equivalences semilinear for the same field equivalence. -/
def tensorSemilinearEquiv : A ⊗[K] B ≃+* C ⊗[L] D := by
  let : RingHomInvPair k.toRingHom k.symm.toRingHom := RingHomInvPair.of_ringEquiv k
  let : RingHomInvPair k.symm.toRingHom k.toRingHom := RingHomInvPair.of_ringEquiv_symm k
  let f' : A ≃ₛₗ[k.toRingHom] C :=
    { f.toAddEquiv with
      map_smul' := fun x a => by
        change f (x • a) = (k x) • f a
        rw [Algebra.smul_def, map_mul, hf, Algebra.smul_def] }
  let g' : B ≃ₛₗ[k.toRingHom] D :=
    { g.toAddEquiv with
      map_smul' := fun x b => by
        change g (x • b) = (k x) • g b
        rw [Algebra.smul_def, map_mul, hg, Algebra.smul_def] }
  let e := TensorProduct.congr f' g'
  refine { e.toAddEquiv with map_mul' := ?_ }
  intro x y
  change e (x * y) = e x * e y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']
    | tmul c d =>
      simp only [e, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.congr_tmul]
      change f (a * c) ⊗ₜ[L] g (b * d) = (f a * f c) ⊗ₜ[L] (g b * g d)
      rw [map_mul, map_mul]

@[simp] theorem tensorSemilinearEquiv_tmul (a : A) (b : B) :
    tensorSemilinearEquiv k f g hf hg (a ⊗ₜ[K] b) = f a ⊗ₜ[L] g b := rfl

end Tensor

section Splitting

variable {K : Type u} {L : Type v} [Field K] [Field L]
  {A : CSA.{u, u} K} {B : CSA.{v, v} L}
  (k : K ≃+* L) (e : A ≃+* B)
  (he : ∀ x, e (algebraMap K A x) = algebraMap L B (k x))

include he in
private theorem isSplit_of_semilinear (h : IsSplit A) : IsSplit B := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  let F := (e.symm.trans f.toRingEquiv).trans
    (k.mapMatrix : Matrix (Fin n) (Fin n) K ≃+* Matrix (Fin n) (Fin n) L)
  refine ⟨n, hn, ⟨AlgEquiv.ofRingEquiv (f := F) ?_⟩⟩
  intro x
  obtain ⟨y, rfl⟩ := k.surjective x
  change k.mapMatrix (f (e.symm (algebraMap L B (k y)))) = _
  rw [← he, e.symm_apply_apply, f.commutes]
  ext i j
  by_cases hij : i = j <;> simp [Algebra.algebraMap_eq_smul_one, hij]

include he in
/-- Matrix splitting is preserved and reflected by a semilinear ring equivalence. -/
theorem isSplit_iff_of_semilinear : IsSplit A ↔ IsSplit B := by
  refine ⟨isSplit_of_semilinear k e he, isSplit_of_semilinear k.symm e.symm ?_⟩
  intro x
  apply e.injective
  rw [e.apply_symm_apply, he, k.apply_symm_apply]

private def tensorPower {K : Type u} [Field K] (A : CSA.{u, u} K) : ℕ → CSA.{u, u} K
  | 0 => groundField K
  | m + 1 => tensor A (tensorPower A m)

private theorem classOf_tensorPower {K : Type u} [Field K] (A : CSA.{u, u} K) (m : ℕ) :
    classOf (tensorPower A m) = m • classOf A := by
  induction m with
  | zero => simp [tensorPower]
  | succ m hm => simp [tensorPower, hm, succ_nsmul, add_comm]

include he in
private def tensorPowerSemilinearEquiv (m : ℕ) :
    {f : tensorPower A m ≃+* tensorPower B m //
      ∀ x, f (algebraMap K (tensorPower A m) x) = algebraMap L (tensorPower B m) (k x)} := by
  induction m with
  | zero =>
    exact ⟨k, fun _ => rfl⟩
  | succ m hm =>
    let f := tensorSemilinearEquiv k e hm.val he hm.property
    refine ⟨f, fun x => ?_⟩
    change f (algebraMap K A x ⊗ₜ[K] (1 : tensorPower A m)) =
      algebraMap L B (k x) ⊗ₜ[L] (1 : tensorPower B m)
    rw [tensorSemilinearEquiv_tmul, he, map_one]

include he in
/-- A multiple of the Brauer class vanishes exactly when the same multiple of the
semilinearly equivalent algebra vanishes. The fields may have different universes. -/
theorem nsmul_classOf_eq_zero_iff_of_semilinear (m : ℕ) :
    m • classOf A = 0 ↔ m • classOf B = 0 := by
  rw [← classOf_tensorPower, ← classOf_tensorPower, classOf_eq_zero_iff, classOf_eq_zero_iff]
  exact isSplit_iff_of_semilinear k (tensorPowerSemilinearEquiv k e he m).val
    (tensorPowerSemilinearEquiv k e he m).property

end Splitting

end Langlands.Brauer
