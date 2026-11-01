# Closed principal presentation of the actual binary overlap

Authors: Worker 1188, with the relation-comparison and norm-lifting argument
suggested by Workers 105 and 948 in the published statement and task context.

This is an internal derived proof of
`Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus.OverlapPresentationStatement`.
It uses the published actual carriers, maps and quotient norms unchanged.
The theorem `overlap_presentation` has exactly that proposition as its unapplied,
universe-polymorphic type.

## Implemented proof

Write `T₂` for the relative two-variable unit-radius series algebra, `p : T₂ → U`
for the annulus projection, and `r : T₂ → O` for the actual overlap projection.
The theorem `toOverlapSeries_eq_quotientMap` identifies the published evaluation
map with `r` by relative bounded-map uniqueness: they agree on all coefficients
and both coordinates. Consequently `toOverlap_quotientMap_eq` gives `F (p h) = r h`.
Surjectivity of `r` immediately proves `toOverlap_surjective`.

For `ker_toOverlap`, put `J = closure(span{x-b(f)})` in the annulus. The inclusion
`J ≤ ker F` follows because `F(x) = F(b(f))` and a bounded map into a normed ring
annihilating an ideal also annihilates its closure.

For the reverse inclusion, form the actual normed quotient `Q = U/J` and its
bounded projection `q`. Since `q(x-b(f)) = 0`, one has `q(x) = q(b(f))`.
The composite `φ = q ∘ p` therefore kills both overlap equations:
`φ(X-C(f)) = 0`, and `φ(C(f)Y-1) = 0` follows by substituting `q(b(f)) = q(x)`
and using the already proved annulus relation `xy = 1`. Bounded closed-ideal
descent produces `χ : O → Q`. On every series representative,
`χ(F(p h)) = q(p h)`; surjectivity of `p` gives `χ(F z) = q z` for every `z`.
If `F z = 0`, then `q z = 0`, which is exactly membership in `J`.
This passes between the actual closed-equation quotients without assuming an
ordinary generated ideal is closed or claiming that a continuous image of a
closed ideal is closed.

Finally, `exists_toOverlap_norm_lt` takes an overlap series representative
`h` with `r h = o` and `‖h‖ < ‖o‖ + ε` from
`RelativeRelations.exists_representative_norm_lt`. The annulus element `z = p h`
then satisfies `F z = o`, and contractivity of `p` gives
`‖z‖ ≤ ‖h‖ < ‖o‖ + ε`. The original quotient norms are used throughout.

## Provenance and scope

The algebraic motivation is the overlap/annulus comparison in Piotr Achinger,
*Introduction to non-Archimedean Geometry*, November 22, 2020, proof of
Proposition 7.1.1, printed p.64. The original is registered as
`achinger-2020-non-archimedean-geometry-nov22`, with SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The source context and its nontrivial valuation hypothesis are documented in the
unchanged statement companion. This closed-kernel and approximate-lift proof is
an internal consequence of the published closed quotients and bounded descent;
it is not attributed as a separate theorem of the source.

No additional hypothesis is introduced. The proof works for arbitrary presented
bases, including zero and nonreduced bases, for arbitrary `f`, zero overlaps,
and trivially valued complete fields. It does not prove ordinary principal-ideal
closedness, a Laurent normal form, injectivity, the principal-relation sequence,
difference-map surjectivity, or scalar gluing.
