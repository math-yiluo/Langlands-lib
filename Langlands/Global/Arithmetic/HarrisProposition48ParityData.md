# Explicit parity data for the Proposition 4.8 induction

These are internal definitions for the proof route of Harris (1998),
Proposition 4.8, printed pp.201–203. They introduce no existence theorem.
The motivating normalization is Harris's definition on p.195 and the
half-integral twist remark on p.191.

`Proposition48Problem.IsValidAtParity Q b` repeats exactly `Q.IsValid`
with `IsAlgebraicAfterTwist b Q.ξ` in place of
`IsAlgebraicAfterTwist ([Q.E':Q.E] − 1) Q.ξ`. In particular it retains
normalized reciprocity, the same arithmetic setup and places, relative
regularity, conjugate inversion, local general position and the prescribed
components. At the original rank parity it is equivalent, by unfolding
and reassociation of conjunctions, to the original validity predicate.
It does not assert that an unmodified Mackey character has its own
rank's parity.

`withCharacters` replaces only the two local characters and the global
Hecke character in a problem. `correctedCharacter Q ν` is exactly
`Q.ξ · (ν ∘ N_{Q.E'/Q.E})`, using the actual idele-class norm.
`IsParityNormalization Q b ν χ χs` requires:

- conjugate inversion of the base Hecke character `ν`;
- algebraicity of `ν` after the parity twist
  `(b + ([Q.E':Q.E] − 1)) mod 2`;
- `ν = 1` if the original and target parities already agree;
- the unchanged original validity conditions for the corrected problem,
  with the new prescribed local characters `χ` and `χs`.

There is no assertion that a global correcting character exists. Its
existence is a separate CM Hecke-character construction obligation. The
use of a base character is essential: multiplication by its norm pullback
twists induction by that same character on the base.

`IsSolution` gives the original four output predicates for a supplied
cuspidal class. `IsUntwistedSolution Q ν S T` supplies actual cuspidal
realizations on the same rank over `Q.E`. The raw realization `S` is
weakly induced from `Q.ξ`, conjugate self-dual and supercuspidal at the
designated place. The normalized realization `T` is weakly induced from
`correctedCharacter Q ν` and has all four original output properties.
The relation requires
`OperatorRealization.IsDeterminantMultiple ν S.realization T.realization`,
whose vectors are multiplied by the genuine function `ν(det g)` on the
adelic group. Regular algebraicity of `S` is deliberately not included.
When the correction is trivial, the actual determinant relation identifies
the realizations and recovers that property.

This is a derived formalization route, not a claim that Harris explicitly
chooses these correcting base characters. It leaves their existence and
the automorphic, local and coefficient transport as named proof
obligations. No published definition or signature is changed.

Source: M. Harris, *The local Langlands conjecture for GL(n) over a p-adic
field, n < p*, Invent. Math. 134 (1998), 177–210,
`harris-1998-local-langlands`: p.195 normalization, p.191 half-integral
twist remark (TeX `math_9611226v1.tex`, lines 866–875), and Proposition
4.8 induction, pp.201–203 (lines 1574–1675).
