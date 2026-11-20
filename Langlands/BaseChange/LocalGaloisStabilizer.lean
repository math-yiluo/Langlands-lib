import Langlands.BaseChange.Norm
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Intertwining

/-! # Trivial Galois stabilizer for a local representation -/

set_option autoImplicit false

namespace Langlands.BaseChange

/-- A representation of `GL_n(E)` is fixed up to equivalence by no nonidentity
automorphism of `E` over `F`. -/
def HasTrivialGaloisStabilizer (F : Type*) [Field F] {E : Type*} [Field E]
    [Algebra F E] {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n E) V) : Prop :=
  ∀ τ : E ≃ₐ[F] E, τ ≠ 1 →
    ¬ Nonempty (ρ.Equiv (ρ.comp (entrywiseAut τ n).toMonoidHom))

end Langlands.BaseChange
