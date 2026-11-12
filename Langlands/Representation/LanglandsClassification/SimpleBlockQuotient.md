# Splitting a retained simple block after an equivariant quotient

Author: Worker 148, Task 5295 (`717df3ca-7a3c-40fc-a8b3-79617086393e`).
Module `Langlands.Representation.LanglandsClassification.SimpleBlockQuotient`,
namespace `Langlands.Classification`.

This is an internal algebraic helper for the retraction step in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, VII.4.2 (i), printed p.243 / PDF p.249. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source page was read as text and checked in the rendered original.

The theorem `simpleBlockQuotient_retraction` takes representations `ρ`, `τ`
and `χ` of a group on complex vector spaces in three independent carrier
universes. It assumes:

- `τ` is irreducible;
- `q : ρ → χ` is a surjective intertwiner;
- `p : ρ → τ`, `s : τ → ρ` and `E : χ → χ` are intertwiners satisfying
  `E(q(v)) = q(s(p(v)))` for every `v`;
- `j : τ → χ` is a nonzero intertwiner satisfying `E(j(w)) = j(w)`.

It constructs an intertwiner `r : χ → τ` with `r j = id`. Neither
finite-dimensionality nor smoothness, admissibility or finite length is a
premise. The theorem does not require `p s = id` or that `E` be idempotent on
all of `χ`; its two stated compatibility conditions suffice.

If `q s` vanished, the formula for `E q`, surjectivity of `q`, and `E j = j`
would make `j` vanish. Thus `q s` is a nonzero map out of the irreducible `τ`
and is injective. For `v ∈ ker q`, the formula for `E q` then forces `p(v)=0`.
Consequently `p` descends through `q` to a map `f : χ → τ`. The implementation
uses the linear maps over the group algebra, the quotient by `ker q` and
its canonical equivalence with `χ`, so the descended map is equivariant.

The identity `q s f = E` shows that `f j` is nonzero. It is an endomorphism
of the irreducible `τ`, hence bijective. Composing `f` with its inverse
produces the desired retraction.

`simpleBlockQuotientRetraction` chooses one such actual intertwiner. Its
identity after composition with `j` is proved by
`simpleBlockQuotientRetraction_comp`. No uniqueness of the retraction is
asserted.

In the intended application, `ρ` is the opposite Jacquet module of the
standard module, `χ` is its quotient induced by a quotient of the standard
module, and `s(τ)` is the identity support piece. Comaximal central kernels
should provide the compatible operator `E` and its factorization through
that piece. This module does not construct those geometric or central
operators, prove Jacquet exactness, or assert that its hypotheses hold for
Langlands triplets. It proves only the explicit algebraic implication.
