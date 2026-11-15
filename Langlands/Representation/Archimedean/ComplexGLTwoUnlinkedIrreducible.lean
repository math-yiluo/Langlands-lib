import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit

/-!
# Irreducibility of principal series of `GL_2(ℂ)` for unlinked characters

`ComplexGLTwoUnlinkedIrreducibleStatement` says: if two complex characters `d`, `e` are not
linked (`IsComplexLinked`), the `(𝔤𝔩_2(ℂ), U(2))`-module of `U(2)`-finite functions of the
standard module of `[d, e]` is irreducible. There is no condition on the order of `d`, `e`.

Source: Tadić 2009, p. 11 (after Jacquet–Langlands): `δ₁ × δ₂` is reducible if and only if
`δ₁ δ₂⁻¹ = (z ↦ z^p z̄^q)` with `p, q ∈ ℤ` and `p q > 0`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

-- As in `ComplexLargeStandardIrreducibleSplit`: the charts on units need reduction through the
-- normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

/-- **Principal series of `GL_2(ℂ)` with unlinked characters are irreducible** (Tadić 2009,
p. 11, after Jacquet–Langlands): for complex characters `d`, `e` that are not linked, the
`U(2)`-finite functions of the standard module of `[d, e]` form an irreducible
`(𝔤𝔩_2(ℂ), U(2))`-module. -/
def ComplexGLTwoUnlinkedIrreducibleStatement : Prop :=
  ∀ d e : ComplexCharacterData, ¬ IsComplexLinked d e →
    IsIrreducibleGKModule (complexStandardRep 2 [d, e]) (complexStandardLie 2 [d, e])

end Langlands.Archimedean
