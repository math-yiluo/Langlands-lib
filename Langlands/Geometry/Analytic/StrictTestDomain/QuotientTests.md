# Quotient tests for strictly represented subsets

Author: Worker 1010.

Fix a normed field K with ultrametric absolute value and a presented strict
affinoid algebra A, the quotient of the strict Tate algebra
`StrictTateAlgebra (Fin A.arity) K` by the closed ideal `A.ideal`.

## Closed ideals

`PresentedStrictAffinoidAlgebra.isClosed_ideal` assumes K complete and an
element of norm greater than one. It shows that every ideal of A is closed.
The proof makes K a nontrivially normed field from that element. Then A is a
Noetherian Banach algebra (published `TateNoetherian` instance), and the
published `isClosed_ideal_of_noetherian_banach` applies.

## The presented quotient

`presentationMap_eq_zero_iff` records that a Tate series maps to zero in A
exactly when it lies in `A.ideal`.

For an ideal I of A that is closed, `quotient K A I hI` keeps the same Tate
variables. Its ideal is the preimage of I under the presentation map, and this
preimage is closed because the presentation map is continuous. So the carrier
is `StrictTateAlgebra (Fin A.arity) K` modulo the series whose image lies in I,
which is the algebraic quotient A/I. Its norm is the quotient norm from the
Tate algebra.

`quotientMap K A I hI : A → A.quotient K I hI` descends the new presentation
map along the old quotient, using the published `BoundedAlgHom.liftQuotient`.
This is possible because `A.ideal` is contained in the new ideal. On
representatives it sends the class of f to the class of f
(`quotientMap_presentationMap`, which holds by definition). It is surjective
(`quotientMap_surjective`), and its kernel is exactly I
(`quotientMap_eq_zero_iff`).

## Idempotent kernels

`StrictTestDomain.exists_idempotent_of_zeroLocus_subset` assumes:

- K is complete and has an element of norm greater than one;
- a bounded map `i : P → Q` of presented strict affinoid algebras represents
  `U ⊆ M(P)` for strict tests, in the sense of the published
  `StrictTestDomain.Represents`;
- every point of `M(P)` that vanishes on the kernel I of i lies in U.

It concludes that there is an idempotent e of P with `I = (e)` and
`U = {x | x e = 0}`.

The proof tests the representation on the presented quotient `P/I²`; the
square I² is closed by the first theorem. Each point z of `M(P/I²)` pulls back
to a point that vanishes on I: for a ∈ I the image of a² is zero, so the image
of a has square zero under z, and hence is zero. By hypothesis these pullbacks
lie in U. The universal property gives ψ : Q → P/I² with ψ ∘ i equal to the
quotient map. For a ∈ I this yields a ∈ I², so I ≤ I², hence I = I² and I is
an idempotent ideal. P is Noetherian, so I is finitely generated, and
Mathlib's `Ideal.isIdempotentElem_iff_of_fg` produces an idempotent generator
e. For the final set equality: U is the range of restriction along i, by the
`Represents` hypothesis, and e lies in the kernel, so every point of U kills
e. Conversely, a point killing e kills (e) = I, so it lies in U by the
hypothesis.

## Scope and provenance

Internal supporting results for the strict local rational-neighbourhood
theorem (`StrictTestDomain.LocalRationalNeighborhoodStatement`). The closedness
theorem and the existence of the idempotent use an element of norm greater
than one only to obtain Noetherianity and closed ideals; `quotient` and
`quotientMap` need no such hypothesis. The idempotent lemma is an internal
quotient-by-square argument, proved directly from the strict-test universal
property. It cites no external numbered result. Its hypothesis that the
zero locus of the kernel lies in U is assumed, not derived. It does not show
that any represented set is Zariski closed.
