# Function-field adeles over all real absolute-value places

This module constructs the cofinite restricted product over
`RealAbsoluteValuePlace F`, the quotient of all nontrivial real absolute values
by `AbsoluteValue.IsEquiv`. At each quotient place it uses the actual completion
of a chosen representative and the literal norm unit ball in that completion.
It equips the product with Mathlib's restricted-product topology and constructs
a ring equivalence and homeomorphism to `CurvePlaceAdeleRing k F`.

The comparison identifies corresponding finite-level subrings, including their
subspace topologies, and preserves the diagonal embedding of `F`. The final
algebra equivalence respects these canonical `F`-algebra structures.

## Provenance and hypotheses

This is derived infrastructure for the function-field realization of the adelic
rings in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`. Printed p.1 defines the adelic ring
and its open finite levels; printed pp.6–7 use the actual completed fields and
their valuation rings. The implementation-specific quotient representative,
completion and restricted-product comparisons here are derived from the
published `FunctionFieldAbsoluteValuePlaces`,
`FunctionFieldAbsoluteValueCompletions`, `CurvePlaceAdeleRing` and
`CurvePlaceAdeleDiagonal` modules. They are not presented as separate assertions
of the original paper.

The construction uses pinned Mathlib's `Quotient.out`, `Equiv.piCongr`,
`Equiv.subtypeEquiv`, the cofinite filter, and `RestrictedProduct` with its
topological-ring and `mapAlong_continuous` interfaces. The dependent-coordinate
proof pattern also occurs in the published `CurvePlaceAdeleCongr` module.

The completed local factor needs only a field `F`. The integral rings,
restricted product, topological-ring instance and finite-level definitions
assume fields `k` and `F` in the same arbitrary universe, `Algebra k F` and
`Finite k`. The curve-place comparisons and diagonal additionally assume
`Algebra (RatFunc k) F`, `IsScalarTower k (RatFunc k) F`, and
`FunctionField k F`, the existing finite-dimensional extension condition.
The imported diagonal's perfectness premise is supplied by the finite field
instance. Separability and a chosen normalization are not additional premises.

## Actual quotient-indexed local factors and restricted product

For `q : RealAbsoluteValuePlace F`, `Quotient.out q` chooses an actual
nontrivial absolute value representative. The abbreviation
`realAbsoluteValuePlaceCompletion q` is its `AbsoluteValue.Completion`, with
the completion's existing field structure and topology.

`realAbsoluteValuePlaceCompletionIntegers k F q` is
`absoluteValueCompletionIntegers` for this representative. The imported
finite-constant theorem supplies its nonarchimedean inequality.
`mem_realAbsoluteValuePlaceCompletionIntegers` identifies its membership
predicate with `‖x‖ ≤ 1`. It is therefore the actual norm unit ball as a
valuation subring of this completion. Its openness follows by inverse image
of the open completed valuation subring under the continuous
absolute-value-to-valuation completion comparison.

`RealAbsoluteValueAdeleRing k F` is literally

```text
Πʳ q : RealAbsoluteValuePlace F,
  [realAbsoluteValuePlaceCompletion q,
   realAbsoluteValuePlaceCompletionIntegers k F q].
```

An element is a tuple in these completed fields that lies in the unit balls at
all but finitely many quotient places. The topology is the existing cofinite
restricted-product topology. The `IsTopologicalRing` instance applies Mathlib's
restricted-product result using the proved openness of every integral subring.

`realAbsoluteValueAdeleLevel k F S` is the subring of tuples integral at each
place outside the finite set `S`. Its membership theorem expresses this
condition directly by the norms of those coordinates. These levels are open
by `RestrictedProduct.isOpen_forall_imp_mem` and increase when `S` increases.

## Completed-factor and restricted-product comparisons

Write `E := realAbsoluteValuePlaceCurvePlaceEquiv k F`. The theorem
`functionFieldPlaceOfAbsoluteValue_out` uses `Quotient.out_eq` to identify the
curve place of the chosen representative with `E q`. Thus
`functionFieldAbsoluteValuePlaceCompletionEquiv k F q` composes the published
representative-level completion comparison with transport along this equality.
Both maps are continuous. The membership equivalence identifies the source
norm unit ball with `curvePlaceCompletionIntegers (E q)`, and the `_coe`
formula sends the canonical image of `x : F` to its `algebraMap` image in
`curvePlaceCompletion (E q)`. The private equality transport is the identity
when its equality proof is reflexive; its continuity, integral membership
and field-map formulas follow by equality induction.

The private `absoluteValuePlacePiEquiv` applies `Equiv.piCongr E` to these
completed-factor ring equivalences. Reindexing by an equivalence preserves
the cofinite filter in both directions, because each inverse is injective.
Combining this fact with the pointwise integral-membership equivalence proves
that the dependent product equivalence preserves almost-everywhere
integrality. `Equiv.subtypeEquiv` therefore restricts it to the two actual
restricted products.

`functionFieldAbsoluteValueAdeleEquiv k F` equips that equivalence with the
coordinatewise ring laws. The coordinate theorem says

```text
functionFieldAbsoluteValueAdeleEquiv k F a (E q) =
  functionFieldAbsoluteValuePlaceCompletionEquiv k F q (a q).
```

Its inverse evaluates at `q` by applying the inverse completed-factor
equivalence to the target coordinate at `E q`.

The inverse continuity proof is `RestrictedProduct.mapAlong_continuous`
using `E`, the continuous inverse local maps and their preservation of
integral elements. The forward proof uses `E.symm`, the continuous forward
local maps, and equality transport from `E (E.symm v)` to `v`. The resulting
`mapAlong` function agrees with the restricted product ring equivalence by
extensionality. `functionFieldAbsoluteValueAdeleHomeomorph` packages these
two continuity proofs with that same equivalence. Both restricted-product
topologies are retained throughout.

## Finite levels and the diagonal

`functionFieldAbsoluteValueAdeleEquiv_mem_level_iff` identifies the source
level at `S` with the curve-place level at `S.map E.toEmbedding`. The proof
uses the coordinate formula, the completed-factor integral-membership
equivalence and the finite-set membership equivalence under `E`.
`functionFieldAbsoluteValueAdeleLevelEquiv` applies `RingEquiv.restrict` to
this iff. Its coercion theorem recovers the ambient adelic equivalence.
`functionFieldAbsoluteValueAdeleLevelHomeomorph` restricts the two continuous
ambient maps to the corresponding subtypes, preserving their subspace
topologies.

`realAbsoluteValueAdeleDiagonal k F` composes the published full-field
curve-place diagonal with the inverse adelic ring equivalence. The imported
finite-poles result already establishes the required almost-everywhere
integrality. `realAbsoluteValueAdeleDiagonal_apply` proves that its coordinate
at each `q` is exactly the canonical `WithAbs` image of the original element
of `F` in the chosen representative's actual completion. The proof applies
the injective local completion equivalence and its original-field formula.
`functionFieldAbsoluteValueAdeleEquiv_diagonal` states that the adelic
comparison carries this diagonal to the existing curve-place diagonal.

The diagonal ring map supplies the `F`-algebra structure, and its composite
with `algebraMap k F` supplies the compatible `k`-algebra structure.
`functionFieldAbsoluteValueAdeleAlgEquiv` is the same adelic ring equivalence
as an `F`-algebra equivalence, with the commutation law given by the diagonal
comparison.

## Remaining scope

This construction realizes all nontrivial real absolute-value places of the
global function field, with chosen actual completions, integral rings and
their restricted-product topology. The proved comparison relates this
choice of representatives to the existing curve-place adelic ring.
Local compactness, full diagonal discreteness, descent of arbitrary models,
and scheme-valued and algebraic-space-valued adelic point comparisons remain
separate obligations of the encompassing five-section program.
