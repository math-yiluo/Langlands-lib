# Rational-character tensors and the actual complex image dual

Worker 6. This is the focused statement of the rational-character tensor
identification in David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, V.3.19–V.3.20, printed pages
115–116 / PDF pages 121–122. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Exact proposition

`Langlands.Plancherel.RationalCharacterTensorParameterStatement.{u}` is a
Prop-valued definition. For every nonarchimedean local field `F : Type u`
with its field, valuation and topology instances, and every actual connected
reductive group scheme `G` over `Spec F`, it asserts that the canonical
complex-linear map

\[
\mathbb C\otimes_{\mathbb Z}X^*(G)
  \longrightarrow \operatorname{Hom}_{\mathbb Z}(\Lambda(G),\mathbb C),
\qquad
s\otimes\chi\longmapsto\bigl(a\longmapsto s\,a(\chi)\bigr)
\]

is bijective.

Here `X^*(G)` is the shared `GroupScheme.rationalCharacters G`, and
`Lambda(G)` is the actual range `rationalDiscreteValuationImage G` of the
published rational-character valuation on `G(F)`. The map is the existing
`rationalCharacterTensorParameter G`; its evaluation formula is already
proved in its construction module. Its target uses additive complex
functionals on that actual image. No replacement character group, lattice,
evaluation pairing or parameter map is chosen in this statement.

The assumptions include connected reductivity and the nonarchimedean
local-field instances, with arbitrary field characteristic. There is no
splitting, rank-equality, character-restriction, supplied bijectivity or
characteristic-zero premise. The universe of the field remains arbitrary.

## Source correspondence

V.3.19 compares the split-component cocharacter lattice, the actual
valuation image and the integer dual of rational characters as lattices of
the same rank. V.3.20 passes to complex scalars and identifies the complex
parameter space with `Hom_Z(Lambda(M), C)`. On printed page 116 it also
writes that space as `X^*(M) tensor_Z C`. The proposition states the
bijectivity of the canonical evaluation map implementing that
identification. Mathlib places `C` first to obtain its standard complex
module structure; tensor commutation gives Renard's character-first
notation. Taking the reductive group itself as a Levi gives the stated
scope.

## Status and remaining obligations

This file states the identification; it does not prove it. Finite freeness
of the actual image alone does not establish the rank comparison needed
for this target. The existing character-restriction, central-torus
detection and actual split-image comparison work remains separate.

The source's exponential, its periods, quotient topology, compact unitary
torus, algebraic-torus structure, split-center comparisons and
representation-theoretic consequences are distinct obligations. The map
here is the canonical linear evaluation map underlying the already
constructed pure-tensor exponential formula.
