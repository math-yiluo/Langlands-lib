import Langlands.Geometry.FormalGroup.RelativeFrobenius
import Langlands.Geometry.FormalGroup.FiniteKernel

/-! # The actual relative Frobenius isogeny and kernel-rank proof target -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ]

/-- Actual relative Frobenius has affine fppf lifting and an actual finite locally free
kernel of rank `p^(n*dim)`, for every scalar-compatible coefficient Frobenius. -/
def RelativeFrobeniusIsogenyStatement (M : ModuleLaw O R σ) (p n : ℕ) [ExpChar R p] : Prop :=
  ∀ (θ : R →ₐ[O] R) (hθ : θ.toRingHom = iterateFrobenius R p n),
    (M.frobeniusHom p n θ hθ).HasHeight p (n * Nat.card σ)

/-- The full target gives both actual affine fppf lifting and an actual finite locally free kernel. -/
theorem frobeniusHom_isIsogeny_of_statement (M : ModuleLaw O R σ) (p n : ℕ) [ExpChar R p]
    (h : RelativeFrobeniusIsogenyStatement M p n)
    (θ : R →ₐ[O] R) (hθ : θ.toRingHom = iterateFrobenius R p n) :
    (M.frobeniusHom p n θ hθ).IsIsogeny := (h θ hθ).1

/-- The full target retains the rank of the actual represented Frobenius kernel. -/
theorem frobeniusHom_kernelRank_of_statement (M : ModuleLaw O R σ) (p n : ℕ) [ExpChar R p]
    (h : RelativeFrobeniusIsogenyStatement M p n)
    (θ : R →ₐ[O] R) (hθ : θ.toRingHom = iterateFrobenius R p n) :
    (M.frobeniusHom p n θ hθ).HasKernelRank (p ^ (n * Nat.card σ)) := (h θ hθ).2

namespace OrderAction

variable {D : Type w} [Ring D] [Algebra O D] {M : ModuleLaw O R σ}

/-- The same target applies to the underlying actual map of the full-order relative Frobenius. -/
theorem frobeniusHom_height_of_statement (E : OrderAction D M) (p n : ℕ) [ExpChar R p]
    (h : RelativeFrobeniusIsogenyStatement M p n)
    (θ : R →ₐ[O] R) (hθ : θ.toRingHom = iterateFrobenius R p n) :
    (E.frobeniusHom p n θ hθ).val.HasHeight p (n * Nat.card σ) := h θ hθ

end OrderAction

end Langlands.FormalGroup.ModuleLaw
