import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RepresentationTheory.Basic

/-! # Injectivity of the finite matrix Gauss operator

For a finite field `k`, a nontrivial additive character `ψ` of `k` and a complex
representation `ρ` of `GL_n(k)`, the operator `v ↦ ∑_g ψ(tr g) ρ(g) v` is injective.
This is a consequence of Kondo's formula for the Gauss sums of the irreducible
representations of `GL_n(k)`, as cited by Bushnell–Fröhlich (1985), (2.4.11)–(2.4.16).
The paired Markdown gives the source, the deduction and an elementary proof route.
This file states the result and does not prove it.
-/

namespace Langlands.BushnellKutzko

universe uK uV

/-- **Finite matrix Gauss injectivity.** Let `k` be a finite field, `n` a natural number,
`ψ : AddChar k ℂ` a nontrivial additive character and `ρ` a complex representation of
`GL_n(k)` on `V`. Then `v ↦ ∑_{g ∈ GL_n(k)} ψ(tr g) • ρ(g) v` is injective. -/
def FiniteMatrixGaussInjectivityStatement : Prop :=
  ∀ (k : Type uK) [Field k] [Fintype k] (n : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) k) V),
      letI := Fintype.ofFinite (Matrix.GeneralLinearGroup (Fin n) k)
      Function.Injective fun v : V =>
        ∑ g : Matrix.GeneralLinearGroup (Fin n) k, ψ (Matrix.trace g.val) • ρ g v

end Langlands.BushnellKutzko
