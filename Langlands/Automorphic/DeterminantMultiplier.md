# Actual determinant multiplication on continuous adelic functions

Author: Worker 2.

This is an internal construction from the published actual adelic determinant
(`Langlands.Global.AdelicGL`), Hecke characters (`Langlands.Global.HeckeCharacter`)
and continuous rational-invariant function space (`Langlands.Automorphic.Ambient`). The number
field is `F : Type u`, the coefficients are complex, and every natural rank,
including zero, is allowed.

`HeckeCharacter.adelicDeterminant n χ` is the continuous character
`x ↦ χ.onIdeles (AdelicGL.determinant F n x)`, valued in complex units.
Its value on every rational matrix is one. This follows from determinant
compatibility with coefficient maps and the existing principal-idele identity.

`ContinuousRationalFunctions.determinantMul n χ` multiplies the actual function
by this character. Rational invariance and continuity of the resulting
function are proved, as are complex linearity and the inverse identity.
`determinantMultiplier n χ` bundles the resulting continuous linear
automorphism with inverse multiplication by `χ⁻¹`. Continuity uses the
existing topology induced from compact-open continuous functions. A private
lemma reduces fixed multiplication to restrictions on compact subsets, where
continuous multiplication is available; no local compactness assumption on
the whole adelic group is added.

The evaluation formula is `Mχ f(x) = χ(det x) f(x)`. The right action satisfies
`R(g) (Mχ f) = χ(det g) Mχ (R(g) f)`, with the existing convention
`R(g) f(x) = f(x g)`.

The proofs compute these actual function maps, use the standard determinant
coefficient-map identity, and cancel inverse complex units. The two named local
additive groups are the canonical submodule structures. This module is
derived internal content and asserts no external-literature comparison.
Constant-term behavior, analytic automorphic conditions, differentiation and
total twists of operator realizations remain separate constructions.
