# The order-2d derivative of an adjacent quotient times its upper factor

This internal prerequisite defines
`IncreasingAdjacentQuotientUpperProductSecondDerivative` and proves it in
`increasingAdjacentQuotientUpperProductSecondDerivative`. Here “second” means
the second multiple `2d` of the common cuspidal rank, not derivative order
two unless `d=1`. The result is derived from the actual product derivative
filtration and actual supplied-quotient calculations; it introduces no new
literature transcription.

## Exact scope

Fix arbitrary prime `p`, `F : PadicField p`, supplied topological data `T`,
and a bundled continuous nontrivial unitary additive character `ψ` for
`T.topology`. The universes `uF,uV` are independent. Let `d>0` and actual
bundled supercuspidals `B,A` on `GL_d(F)` have carriers in
`Type (max uF uV)` and satisfy
`A.isoClass = T.supercuspidalClassRealPowerTwist d 1 B.isoClass`.

Let `P` be the actual ordered normalized induction of `(B,A)` on
`Shahidi.twoBlocks d d hd hd`. Supply an invariant subspace `S` with
`S≠⊥` and `S≠⊤`, and put `Q=SmoothRep.quotient P S`. Let `R` be the actual
order-`d+d` derivative of the binary normalized product `Q × A`, on
`GL_(((d+d)+d)-(d+d))`. Let `U` be the actual rank transport of `A.obj` from
rank `d` to that same residual rank.

The two conclusions are `R.HasFiniteLength` and
`SmoothRep.HasConstituentSupportIn R U`. Thus every actual irreducible
subquotient of `R` is an actual subquotient of the transported upper factor
`U`. This is a statement about actual representations and actual
subquotients, not just virtual classes or a support multiset. No additional
finite-length premise on `R`, and no proper-subspace existence premise, is
hidden in the conclusion. The existence of `S`, irreducibility of `Q × A`
and either triple transfer are not asserted.

## Implemented proof

The helpers lie in
`Langlands.Classification.AdjacentQuotientUpperProductDerivatives`.

`evaluatedFiltration` evaluates each actual invariant step of a natural
filtration at a specified input object. `evaluatedGradedEquiv` is the
identity-carrier actual equivalence between its graded quotient and the
evaluated natural graded quotient. Their actions are the same actual
quotient action.

`finiteLength_of_glued` proves finite group-algebra length of an evaluated
gluing when all its evaluated pieces have finite length. It unpacks the
finite enumeration, permutation, filtration and grade isomorphisms. The
published `repLength_eq_sum_of_filtration` expresses the actual module
length as the finite sum of the piece lengths. Each term is below infinity
by the supplied finite-length hypothesis, so the sum is finite.

`subsingleton_of_isSubquotient` proves that an actual subquotient of a zero
smooth object is zero. Use the published injective/surjective presentation:
the injecting object's vectors coincide because their images do, and the
surjection transfers that equality to the target.

`finiteLength_support_of_glued` is a general smooth-representation lemma.
Suppose every evaluated piece is zero or actually equivalent to one fixed
irreducible smooth object `U`. Each piece has module length zero or one, so
the preceding finite-length argument applies. Given an irreducible actual
subquotient `D` of the glued source, the published
`exists_smoothGradedObject_subquotient` places `D` in one actual smooth graded
quotient. Its equivalence to a zero piece contradicts nonzeroness of `D`.
Otherwise the grade equivalence followed by its supplied equivalence to
`U` transports the actual subquotient relation to `U`. This extraction
does not assume finite length, simplicity or nonzeroness of the intermediate
graded quotients.

`equiv_rankCast` transports a supplied actual representation equivalence to
any common rank by equality elimination. No carrier resizing is used.

`order_two_d_piece` computes the possible Leibniz pieces at order `d+d` of
`Q × A`. Write a feasible index as `(i,j)`, where `i≤d+d`, `j≤d`, and
`i+j=d+d`.

- If `j=0`, then `i=d+d`. The actual top derivative of `Q` has finrank one
  by `TwoSupercuspidalTopDerivatives.increasing_quotient_top`. The zero-order
  derivative of `A` is the identity. The published full rank-zero-left
  binary-product equivalence identifies this piece with the transported
  `A`, retaining the arbitrary rank-zero carrier before cancellation.
- If `j=d`, then `i=d`. The actual top derivative of `A` has finrank one
  by the proved supercuspidal formula. The actual middle derivative of `Q`
  is equivalent, after its explicit rank cast, to `A`, by
  `twoSupercuspidalAdjacentProductMiddleDerivatives`. The full rank-zero-right
  binary-product equivalence cancels the top factor. `equiv_rankCast`
  then supplies the stated equivalence to `U`.
- Otherwise `0<j<d`, so the actual derivative of `A` is zero by
  `SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivative`.
  The published actual binary-product zero-factor lemma makes the whole
  rank-cast piece zero.

These cases exhaust every feasible index; no assumed derivative formula is
used. `order_two_d_finiteLength_support` applies the proved actual
`AdjacentQuotientUpperProduct.positiveGlued` to the product `Q × A` and uses
this complete zero-or-equivalent piece calculation. The target `U` is
irreducible by equality-based rank transport of the supercuspidal factor.
Applying `finiteLength_support_of_glued` gives both conclusions. The public
closing theorem supplies precisely this proof at independent universes.

## Dependency audit

The recursive project import closure has 922 modules including this entry.
The other locally authored prerequisite entries are
`AdjacentQuotientUpperProduct`, `TwoSupercuspidalTopDerivatives`, and
`Derivative.LocalPositiveLeibniz`, each separately staged with successful
machine validation and subject to its own independent review and
publication. The remaining 918 project Lean modules are unchanged from
published base `e058cb4d3adbd71764731d87c4cbfcb5805696e8`. External imports
are from Mathlib and Lean. Every module has paired Markdown.

Relative to the top-product prerequisite, the additional project modules
are actual smooth-grade extraction, evaluated composition-length algebra,
finite composition series, generic irreducible classes and their
Grothendieck-group bookkeeping. The proof uses only actual filtration
length and subquotient extraction; no virtual-class equality supplies an
occurrence or finite-length premise. `ActualGradedExtraction` proves its
extraction using the first filtration step on which the supplied actual
quotient map is nonzero, then factors through its invariant kernel.
`RepresentationLength` uses module length additivity on the actual
inclusion/quotient short exact sequences and sums along the finite chain.
The new generic helpers retain these actual objects and maps.

The inherited product derivative proof derives its mixed-product formulas
from actual minus identities, localized two-orbit Mackey sequences and
proved character-localization exactness, then splices the differentiated
actual mirabolic restriction sequence. The supplied quotient top and middle
derivative calculations use the ordered two-factor Jacquet calculation,
actual partial-derivative comparisons, support shift, integral twist
freeness and actual Whittaker multiplicity one. The rank-zero product
bridges retain the full tensor carriers and explicit compensating casts.
Their complete proof routes are documented in the separately submitted
prerequisites. Neither the conditional full two-supercuspidal product
statement nor a segment derivative assertion is used as a proved input.

No used proof relies on the host's excluded analytic segment classification,
special-head or ordered-head existence, multisegment exhaustion, global
support decomposition, general ordered quotient coverage, tempered
uniqueness, regular or square-integrable exhaustion, or square-integrable
Langlands classification, including renamed results or proof successors.
No segment-product irreducibility conclusion is used.

## Remaining host obligations

This calculation supplies actual order-`2d` constituent support and finite
length. The order-`d` finite-length calculation, nonvanishing of the top
derivative on every irreducible actual subquotient of `Q × A`, and the
resulting product irreducibility still remain. Both repeated-cuspidal
triple transfers and the final exact ambient conjunction remain open.
