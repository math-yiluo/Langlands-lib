import Langlands.Global.ProfiniteIntegerPadicProjection
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
open scoped TensorProduct

namespace Langlands.Global

namespace ProfiniteIntegerRing
variable (p : ℕ) [Fact p.Prime]

/-- The canonical local projection of rationalized full residue scalars. -/
def rationalToPadic : (ℚ ⊗[ℤ] ProfiniteIntegerRing) →ₐ[ℚ] ℚ_[p] :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ ℚ_[p])
    (((algebraMap ℤ_[p] ℚ_[p]).comp (toPadic p)).toIntAlgHom)
    (fun _ _ => Commute.all _ _)

@[simp] theorem rationalToPadic_tmul (q : ℚ) (a : ProfiniteIntegerRing) :
    rationalToPadic p (q ⊗ₜ[ℤ] a) = (q : ℚ_[p]) * (toPadic p a : ℚ_[p]) := rfl

@[simp] theorem rationalToPadic_one_tmul (a : ProfiniteIntegerRing) :
    rationalToPadic p ((1 : ℚ) ⊗ₜ[ℤ] a) = (toPadic p a : ℚ_[p]) := by
  simp

@[simp] theorem rationalToPadic_tmul_one (q : ℚ) :
    rationalToPadic p (q ⊗ₜ[ℤ] (1 : ProfiniteIntegerRing)) = (q : ℚ_[p]) := by
  simp

/-- The pure-tensor normalization uniquely specifies the rational projection. -/
theorem rationalToPadic_unique
    (g : (ℚ ⊗[ℤ] ProfiniteIntegerRing) →ₐ[ℚ] ℚ_[p])
    (hg : ∀ (q : ℚ) (a : ProfiniteIntegerRing),
      g (q ⊗ₜ[ℤ] a) = (q : ℚ_[p]) * (toPadic p a : ℚ_[p])) :
    g = rationalToPadic p := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro q a
  exact (hg q a).trans (rationalToPadic_tmul p q a).symm

end ProfiniteIntegerRing

namespace PrimeToProfiniteIntegerRing
variable (p m : ℕ) [Fact p.Prime]

/-- The canonical local projection of rationalized away residue scalars. -/
def rationalToPadic (h : Nat.Coprime p m) :
    (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) →ₐ[ℚ] ℚ_[p] :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ ℚ_[p])
    (((algebraMap ℤ_[p] ℚ_[p]).comp (toPadic p m h)).toIntAlgHom)
    (fun _ _ => Commute.all _ _)

@[simp] theorem rationalToPadic_tmul (h : Nat.Coprime p m)
    (q : ℚ) (a : PrimeToProfiniteIntegerRing m) :
    rationalToPadic p m h (q ⊗ₜ[ℤ] a) =
      (q : ℚ_[p]) * (toPadic p m h a : ℚ_[p]) := rfl

@[simp] theorem rationalToPadic_one_tmul (h : Nat.Coprime p m)
    (a : PrimeToProfiniteIntegerRing m) :
    rationalToPadic p m h ((1 : ℚ) ⊗ₜ[ℤ] a) =
      (toPadic p m h a : ℚ_[p]) := by
  simp

@[simp] theorem rationalToPadic_tmul_one (h : Nat.Coprime p m) (q : ℚ) :
    rationalToPadic p m h (q ⊗ₜ[ℤ] (1 : PrimeToProfiniteIntegerRing m)) =
      (q : ℚ_[p]) := by
  simp

theorem rationalToPadic_unique (h : Nat.Coprime p m)
    (g : (ℚ ⊗[ℤ] PrimeToProfiniteIntegerRing m) →ₐ[ℚ] ℚ_[p])
    (hg : ∀ (q : ℚ) (a : PrimeToProfiniteIntegerRing m),
      g (q ⊗ₜ[ℤ] a) = (q : ℚ_[p]) * (toPadic p m h a : ℚ_[p])) :
    g = rationalToPadic p m h := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro q a
  exact (hg q a).trans (rationalToPadic_tmul p m h q a).symm

/-- Rationalized restriction of residue scalars commutes with local projection. -/
theorem rationalToPadic_restrict (h : Nat.Coprime p m)
    (x : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
    rationalToPadic p m h
      (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (restrict m).toIntAlgHom x) =
        ProfiniteIntegerRing.rationalToPadic p x := by
  induction x using TensorProduct.inductionOn with
  | tmul q a => simp
  | add x y hx hy => simp_all

end PrimeToProfiniteIntegerRing

end Langlands.Global
