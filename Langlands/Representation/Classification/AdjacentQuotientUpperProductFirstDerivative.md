# The first common-rank derivative of an increasing quotient times its upper factor

Author: Worker 168.

This is an internal prerequisite for the repeated-cuspidal triple transfers.
The proposition
`Langlands.Classification.IncreasingAdjacentQuotientUpperProductFirstDerivative`
and its closing theorem
`increasingAdjacentQuotientUpperProductFirstDerivative` assert the following.
Fix an arbitrary prime, actual p-adic field and supplied topological data `T`,
a bundled continuous nontrivial unitary additive character `ψ`, and `d > 0`.
Let `B,A` be actual supercuspidal representations of rank `d`, with the class
of `A` equal to the determinant-power twist `νB`. Put `P = B × A`, using
upper-parabolic normalized product induction. Supply an actual invariant
subspace `S` of `P`, with `S ≠ ⊥` and `S ≠ ⊤`, and put `Q = P/S`.
Then the actual derivative of order `d` of `Q × A` has finite group-algebra
composition length. Every irreducible actual smooth subquotient of that
derivative has an actual supercuspidal support containing the datum of `A`.

The field universe `uF` and representation universe `uV` remain independent.
All factors have carrier universe `max uF uV`. The derivative has its actual
residual rank `((d+d)+d)-d`; the inducing data have their displayed ranks.
No existence of `S`, product irreducibility, or ambient triple transfer is
asserted. “First” refers to order `d`, the first positive common-rank order,
including arbitrary `d`; it is not a restriction to ordinary order one.

## Implemented proof

The helpers are in `Classification.AdjacentQuotientUpperProductFirstDerivative`.
`quotient_irreducible` applies the published adjacent two-factor structure
with the actual associated and nonassociated Jacquet calculations. The
supplied proper subspace proves reducibility of `P`, so the conditional
structure theorem makes its actual quotient `Q` irreducible. It does not
assert reducibility of every adjacent product.

`binary_finite_length` identifies a positive-rank binary product with the
actual standard two-block product and applies the unconditional published
`irreducibleProductFiniteLength`. It only requires irreducibility of the two
factors. `finite_length_rankCast` uses equality elimination to transport
finite length. `product_rankCast_equiv` likewise eliminates rank equalities,
then maps the actual pair of factor isomorphisms through the binary functor.
No carrier is replaced by its isomorphism class.

`order_d_piece` computes every feasible Leibniz index `(i,j)` at total order
`d`, where `j` differentiates `A`. There are three exhaustive cases.

- If `j=0`, then `i=d`. The proved middle derivative of `Q` is equivalent to
  `A` after its prescribed rank cast. Mapping that equivalence through the
  actual binary functor identifies this whole grade with `A × A`, transported
  to the residual rank.
- If `j=d`, then `i=0`. The actual top derivative of the supercuspidal `A`
  has dimension one. The full rank-zero-right binary-product equivalence
  identifies this whole grade with the transported `Q`.
- If `0<j<d`, the actual derivative of `A` is zero by the published
  supercuspidal vanishing theorem. The zero-factor product lemma makes this
  whole grade zero.

The rank-zero product lemma retains the full tensor carrier and its action;
it is not a cancellation of an isomorphism-class symbol. At `d=1` the third
case is empty, and the proof still applies.

`finiteLength_support_of_glued_two` is a generic actual-filtration helper.
Its two possible nonzero reference objects need only have finite length.
The helper evaluates the natural gluing's actual invariant steps, writes
source module length as the finite sum of actual grade lengths, and transports
each grade along its equivalence to one reference object or the other.
For an irreducible actual subquotient it uses
`ObjectRepFiltration.exists_smoothGradedObject_subquotient` to find an actual
grade containing it as an actual subquotient. A zero grade contradicts
irreducibility and nontriviality. Otherwise the grade equivalence transports
the actual subquotient relation into one of the reference objects.

`order_d_finiteLength_support` applies this helper to the actual positive-rank
Leibniz gluing. Its two reference objects are transported `Q` and `A × A`.
The first is finite because it is irreducible; the second is finite by
`binary_finite_length`. The result detects every irreducible actual derivative
subquotient in one of those two objects, as well as proving finite length.

`pair_support` constructs the two-entry support directly from the actual
supercuspidal induction presentation. If the derivative subquotient comes
from `Q`, composing its actual subquotient relation with the actual quotient
`P → Q` gives support `{B,A}`. If it comes from `A × A`, its support is
`{A,A}`. `support_of_subquotient_rankCast` removes the source rank transports
by equality elimination. `order_d_upper_support` concludes in both cases
that the displayed upper datum belongs to the support. No support uniqueness
or global decomposition is required for this step.

A generic auxiliary theorem, `exists_irreducible_subrepresentation`, is
included for the ensuing highest-derivative argument. Finite module length
implies the Artinian property. The actual order isomorphism between
subrepresentations and group-algebra submodules transfers atomicity. The
nonzero carrier makes bottom and top distinct, so an atom exists. Its
successive quotient by zero is irreducible by the cover criterion and is
actually equivalent to the invariant subspace. Its subtype map supplies
the required injective intertwiner. This gives a subrepresentation, which
is stronger than merely finding an irreducible subquotient.

## Provenance and independence

This is internal derived content, obtained from actual positive-rank Leibniz
gluing, actual supplied-quotient middle derivatives, supercuspidal derivative
vanishing and top dimension, full rank-zero binary-product equivalences,
module length, and actual grade extraction. It is not a transcription of a
new literature assertion. The public proposition and closing theorem state
exactly the finite-length and upper-support conclusions described above.
The generic Artinian, two-reference gluing, rank-transport and pair-support
helpers describe their implemented actual maps and quotient objects.

The recursive project import closure has 941 modules, including this entry.
Five entries differ by absence from base
`e058cb4d3adbd71764731d87c4cbfcb5805696e8`: this entry,
`AdjacentQuotientUpperProductDerivatives`, `AdjacentQuotientUpperProduct`,
`TwoSupercuspidalTopDerivatives`, and `Derivative.LocalPositiveLeibniz`.
The latter four are separately submitted prerequisites; their independent
review and integration remain separate gates. The other 936 project Lean
files are byte-identical to that base. All project modules have Markdown
pairs. External imports come from Lean and Mathlib.

Relative to the order-`2d` prerequisite, the substantive additional finite-length
route is the published irreducible-product embedding, actual ordered
regrouping, and actual cuspidal-induction length proof. The embedding chooses
an individual cuspidal embedding of each original irreducible factor, factors
its Levi representation, tensors the actual injections and induces them.
Ordered regrouping uses the actual tensor refinement equivalence, explicit
consecutive coordinates with their determinant half-modulus comparison,
and induction in stages on the actual smooth function spaces. Cuspidal
induction length follows from the finite detecting family of actual Jacquet
functors: exactness makes the sum of their lengths strictly increase on a
strict inclusion; associated geometric grades bound this sum. Individual
minimal nonzero Jacquet modules and nonassociation vanishing supply detection.
This uses no general ordered quotient coverage or global support decomposition.

The inherited order-`2d`, product-top, and positive-Leibniz dependencies retain
their previously documented proof routes. In particular the mixed-product
premises are discharged from actual minus identities and exact localization;
the quotient top calculation uses the individual highest-support shift,
integral twist freeness and Whittaker multiplicity one. Imported broad
classification proposition definitions are not applied as proved conclusions.
No used proof depends on the host's excluded segment classification,
special-head or ordered-head existence, multisegment or regular exhaustion,
tempered uniqueness, square-integrable exhaustion or square-integrable
Langlands classification, including renamed conclusions or proof successors.

The remaining host work is all-subquotient top nonvanishing and irreducibility
of `Q × A`, then both actual repeated-triple transfers and the final exact
ambient conjunction. This prerequisite does not close those obligations.
