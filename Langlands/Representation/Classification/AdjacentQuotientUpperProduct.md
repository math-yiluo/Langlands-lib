# Top derivative of an adjacent quotient times its upper factor

This internal prerequisite defines
`IncreasingAdjacentQuotientUpperProductTopDerivative` and proves it in
`increasingAdjacentQuotientUpperProductTopDerivative`. It derives the
one-dimensional actual top derivative of the specified product, including
an arbitrary-positive-rank product helper. It introduces no new translation
of an external statement.

## Exact scope

Fix arbitrary prime `p`, `F : PadicField p`, supplied topological data `T`,
and a bundled continuous nontrivial unitary additive character `ψ` for
`T.topology`. The universes `uF,uV` are independent. Let `d>0` and let
`B,A` be actual bundled supercuspidal representations on `GL_d(F)`, with
carrier universe `max uF uV`, such that
`A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass`.

Let `P` be the actual normalized induction of the ordered pair `(B,A)` on
`Shahidi.twoBlocks d d hd hd`. For every supplied invariant subspace `S`
with `S≠⊥` and `S≠⊤`, put `Q=SmoothRep.quotient P S`. The assertion is that
the actual derivative of order `(d+d)+d` of the binary normalized product
`Q × A` has complex finrank one. Its source is exactly
`T.binaryNormalizedProductFunctor (d+d) d`; its derivative is exactly
`generalLinearDerivative T ψ ((d+d)+d) ((d+d)+d) le_rfl`.
The existence of `S` and irreducibility of `Q × A` are not asserted.

The generic helper `finrank_product_top` has a broader scope. Its two input
ranks `a,b` are arbitrary and positive, and its smooth input carriers are in
`Type uV`. If both actual top factor derivatives have finrank one, then the
actual top derivative of their binary normalized product has finrank one.
It requires no irreducibility, admissibility, finite-length or cuspidality
premise on the inputs. The product carrier has universe `max uF uV`.

## Implemented proof

All helpers belong to
`Langlands.Classification.AdjacentQuotientUpperProduct`.

`oneStepGradedIso` handles an arbitrary representation-valued functor with
an actual one-step zero-to-full filtration. The inclusion from its full
upper step is objectwise surjective, and its kernel is precisely the
pulled-back lower zero step. The published actual quotient first-isomorphism
construction therefore gives a natural isomorphism from its sole graded
quotient to the source functor. This helper works over an arbitrary
commutative ring and monoid.

`nonempty_iso_of_glued_unique` unpacks an actual gluing indexed by a finite
unique type. Its cardinality is one. The preceding helper, the supplied
graded isomorphism and uniqueness of the piece index identify the source
naturally with the specified piece. Here the group hypothesis is retained
from the published gluing interface.

`topIndexUnique` gives the unique feasible index `(a,b)` at total derivative
order `a+b`, using `leibnizIndices_top`. `positiveGlued` rewrites arbitrary
positive ranks as successors and applies the proved actual
`LocalPositiveLeibniz.positiveGlued`. The separate adapter keeps the ranks
abstract in the dimension proof; it changes no functor or assertion.

For `finrank_product_top`, apply that gluing at order `a+b`. The unique-index
helper gives an actual natural isomorphism from the derivative source to
its only piece. Evaluating at `(A,B)` and taking the underlying linear
equivalence transfers finrank. The sole piece is the binary normalized
product of the two actual top factor derivatives, with remaining ranks
`a-a` and `b-b`, followed by the explicit rank cast to
`(a+b)-(a+b)`. The published
`BinaryProductBridge.finrank_rankCast_product_of_zero_zero` identifies this
with the full tensor of the two rank-zero carriers; its tensor finrank is
`1*1=1`. No rank-zero carrier is discarded or replaced by a chosen unit.

`increasing_quotient_upper_product_top` obtains finrank one for the actual
top derivative of `Q` from
`TwoSupercuspidalTopDerivatives.increasing_quotient_top`, using precisely the
supplied adjacency and proper-subspace hypotheses. The published
`TwoSupercuspidalPartialDerivatives.finrank_topDerivative` gives top
finrank one for the supercuspidal `A`. Removing its output rank cast by the
proved finrank transport helper gives the raw derivative convention needed
by `finrank_product_top`. Applying that helper to `(Q,A.obj)` proves the
concrete conclusion. The public closing theorem supplies this proof with
explicit independent universe arguments.

## Dependency audit

The three direct imports are `Derivative.LocalPositiveLeibniz`,
`Classification.TwoSupercuspidalTopDerivatives`, and
`Classification.TwoSupercuspidalBinaryProductBridge`. Their recursive
closure contains 903 project modules including this entry, with paired
Markdown. The other locally authored prerequisite entries are the first
two just named; both were staged separately with successful machine
validation and remain subject to independent review and publication. The
remaining 900 Lean modules are unchanged from published Library base
`e058cb4d3adbd71764731d87c4cbfcb5805696e8`. External imports are from Mathlib
and Lean.

The actual positive-rank gluing proof derives the full left mixed-product
isomorphism and vanishing by mirabolic-rank induction from the proved
actual minus identities. It then discharges the actual right mixed-product
filtration using the proved right minus sequence and minus exactness. The
existing positive gluing construction differentiates the actual two-orbit
mirabolic restriction sequence and splices the two feasible piece families.
Its lower inputs are explicit matrix orbit calculations, compact induction,
character localization, compact averaging, actual quotient comparisons and
finite filtration algebra. No derivative formula remains an assumed premise.

The supplied increasing-quotient top calculation first obtains its
irreducibility and middle derivative from the actual ordered two-factor
Jacquet calculation for a supplied proper subspace. Nondivisible proper
derivatives vanish by the actual Jacquet-to-derivative quotient comparison
and geometric filtration. If its top vanished, its middle derivative would
be highest and have singleton support `{A}`; the highest-derivative support
shift would put the twist of `A` in `{B,A}`, contradicting integral twist
freeness. Actual Whittaker multiplicity one and admissibility then give
finrank one. This route uses individual cuspidal support existence and
uniqueness, not global support decomposition or ordered quotient coverage.
Its complete support-shift, pairing, duality and geometric argument is
documented in the separately submitted top-derivative pair.

The binary-product bridge uses the actual rank-zero tensor equivalence and
Mathlib tensor finrank, with all rank equalities retained. Its imported
conditional two-supercuspidal product-structure proposition supplies no
proof premise here. The new filtration-to-isomorphism helpers use only the
actual quotient first-isomorphism construction and unique-index algebra.

No used proof depends on the host's excluded analytic segment
classification, special-head or ordered-head existence, multisegment
exhaustion, global support decomposition, ordered quotient coverage,
tempered uniqueness, regular or square-integrable exhaustion, or
square-integrable Langlands classification, including renamed conclusions
or proof successors. No segment-product irreducibility result is used.

## Remaining host obligations

Top dimension one alone does not prove irreducibility: nonvanishing on all
irreducible actual subquotients remains to be established. This unit proves
no proper-derivative support formula, proper-subspace existence, local
rank-three transfer or ambient transfer. The exact repeated-cuspidal
triple conjunction remains open.
