import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-!
# Irreducibility of real standard modules with blocks of equal real exponent

The statement `RealTemperedStandardIrreducibleStatement`: if all blocks of a list `ds` of real
blocks of total rank `n` have the same real exponent `realBlockExponent`, the
`(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite functions of `realStandardModule n ds` is irreducible.
Up to the twist by a real power of `|det|`, these are the standard modules induced from unitary
characters of `GL_1(ℝ)`, unitary twists of discrete series of `GL_2(ℝ)` and limits of discrete
series of `GL_2(ℝ)` (Badulescu–Renard 2010, Theorem 3.1 with §9.2). The statement is only stated
here.
-/

noncomputable section

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

open scoped TensorProduct Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

/-- **Irreducibility of tempered real standard modules** (Badulescu–Renard 2010, Theorem 3.1:
`δ₁ × ⋯ × δ_l` is irreducible for square integrable modulo center `δᵢ`; for `GL_n(ℝ)` these are
the unitary characters of `ℝˣ` and the unitary twists of discrete series of `GL₂(ℝ)`, §9.2; the
limit of discrete series `δ(x, 0) × δ(x, 1)` is a product of two characters; the common twist
`|det|^e` does not affect irreducibility). For every list `ds` of real blocks of total rank `n`
whose blocks all have the same real exponent, the `(𝔤𝔩_n(ℝ), O(n))`-module
`(realStandardRep n ds, realStandardLie n ds)` of `O(n)`-finite functions of
`realStandardModule n ds` is irreducible. -/
def RealTemperedStandardIrreducibleStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    (∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y) →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)

end Langlands.Archimedean
