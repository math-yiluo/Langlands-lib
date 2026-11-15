import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-!
# Irreducibility of complex standard modules with exponents of equal real part

The statement `ComplexTemperedStandardIrreducibleStatement`: if all exponents of a list `ds` of `n`
complex characters have the same real part, the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite
functions of `complexStandardModule n ds` is irreducible. Up to the twist by a real power of
`|det|`, these are the unitary (tempered) principal series of `GL_n(ℂ)` (Badulescu–Renard 2010,
Theorem 3.1 with §9.1). The statement is only stated here.
-/

noncomputable section

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped TensorProduct Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

/-- **Irreducibility of tempered complex standard modules** (Badulescu–Renard 2010, Theorem 3.1:
`δ₁ × ⋯ × δ_l` is irreducible for square integrable modulo center `δᵢ`; for `GL_n(ℂ)` these are
the unitary characters of `ℂˣ`, §9.1; the common twist `|det|^e` does not affect
irreducibility). For every list `ds` of `n` complex characters whose exponents all have the same
real part, the `(𝔤𝔩_n(ℂ), U(n))`-module `(complexStandardRep n ds, complexStandardLie n ds)` of
`U(n)`-finite functions of `complexStandardModule n ds` is irreducible. -/
def ComplexTemperedStandardIrreducibleStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re) →
      IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)

end Langlands.Archimedean
