# Simple actual subquotients in a supplied composition series

`Langlands.simpleSubquotientFactor` proves the published proposition
`Langlands.SimpleSubquotientFactorTheorem`, with its four independent universes
for the field, group, ambient carrier, and constituent carrier. Given a smooth
representation `A`, a supplied finite filtration `s` with simple actual graded
quotients, an irreducible smooth representation `D`, and an equivalence from
`D` to an actual subquotient `S/U` of `A`, the theorem returns an index `j` of
this same filtration and an equivalence from `D` to `s.gradedRepresentation j`.
There are no extra finite-dimensionality, admissibility, or nonzero-length
hypotheses.

## Implemented proof

Compose the actual quotient map `S → S/U` with the inverse of the supplied
equivalence to obtain a surjective intertwiner `f : S → D`. Irreducibility
makes `D` nontrivial. For each filtration step `A_i`, let `P i` say that `f`
vanishes on every vector of `S` lying in `A_i`. The zero step satisfies `P`,
whereas the full step does not, since `f` is surjective onto a nontrivial
representation. Finite induction therefore supplies an adjacent pair with
`P j.castSucc` and `¬ P j.succ`. This argument includes length zero: if there
are no adjacent pairs, finite induction contradicts the two endpoint facts.
It does not require choosing a positive length beforehand.

Set `X = S ∩ A_(j+1)`. The inclusion into `S` gives an intertwiner `fX : X → D`;
the inclusion into the upper step followed by its graded projection gives
`q : X → gr_j`. The failure of `P j.succ` supplies a vector on which `fX` is
nonzero. The published `gradedProjection_eq_zero_iff` identifies the kernel of
the projection with the lower step. Hence `P j.castSucc` gives
`ker q ≤ ker fX`. In particular, `q` cannot be zero. Irreducibility of the
supplied graded factor makes `q` surjective.

The private helper `intertwiner_descends` factors `fX` through `q`. It first
uses the module quotient by `ker q` and the first isomorphism theorem for
surjective linear maps to obtain a linear map `h : gr_j → D`. The identity
`h (q x) = fX x`, surjectivity of `q`, and equivariance of `q` and `fX` prove
that `h` is equivariant. The chosen vector shows that `h` is nonzero. Since
both `gr_j` and `D` are irreducible, Mathlib's `bijective_or_eq_zero` makes
`h` bijective. The inverse of its induced representation equivalence is the
required equivalence `D ≃ gr_j`.

## Provenance and scope

This is an internal algebraic proof of the existing Library statement, following
its intersection-and-projection argument. It uses the actual submodule and
quotient representations from `Category.Subquotients`, the actual filtration
objects from `Filtration.ObjectDefinitions`, the projection-kernel lemma from
`Filtration.SubsingletonProof`, and Mathlib's quotient linear equivalence and
irreducible-intertwiner results. It does not use an abstract same-universe
subquotient relation, a Jordan–Hölder theorem, or an analytic theorem about
parabolic induction. Smoothness is part of the target's input data; the proof
after forming the quotient map is purely algebraic.
