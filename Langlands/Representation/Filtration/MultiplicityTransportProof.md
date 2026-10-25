# Actual finite-series and multiplicity transport

`Langlands.multiplicityTransport` proves exactly
`Langlands.MultiplicityTransportStatement`. The field universe `uK`, group
universes `uG` and `uH`, and representation-carrier universes `uA`, `uB`,
`uT` and `uU` remain independent. The proof uses the Library's actual
invariant-subspace chains, quotient representations and finite counting
subtypes. The four component theorems are also exposed separately.

## Pullback of an actual supplied filtration

`groupEquivFiltrationMultiplicityTransport` constructs a same-length
filtration from every supplied `ObjectRepFiltration A n` and actual group
equivalence `e : H ≃* G`. The helpers `pullSub` and `unpullSub` retain the
underlying vector submodule. For the inverse construction, invariance at
`g : G` follows from invariance at `e.symm g`. They form the order
isomorphism `MultiplicityTransportProof.subrepOrderIso`. Applying it to
each supplied step preserves monotonicity and the zero and full endpoints.
Thus the output filtration has exactly the original vector submodule at
every index.

The proof uses `LengthCriterionProof.hasSimpleFactors_iff_covBy` in both
directions. The order isomorphism preserves and reflects covering
relations, hence the actual successive quotients are simple on one side
if and only if they are simple on the other. No simple-factor assumption
is needed to construct this pullback filtration.

Pullback commutes definitionally with the actual successive quotient:
the upper subspace and the pulled-back lower denominator are unchanged,
and the quotient action is the original action evaluated at `e h`. The
identity representation equivalence therefore gives the required graded
identification at every index.

The helpers `pullEquiv` and `unpullEquiv` keep the underlying linear
equivalence and preserve or reflect its intertwining equations. Reflection
again evaluates the pulled-back equation at `e.symm g`. Consequently a
pulled-back graded factor is equivalent to the pulled-back counted
representation precisely when the original graded factor is equivalent
to the original counted representation. The identity on `Fin n`
restricts through `Equiv.subtypeEquiv` to an equivalence of the actual
finite counting types. `Nat.card_congr` proves the exact
`factorMultiplicity` equality, including repeated factors at their
distinct indices. The counted representation need not be irreducible.

## Ambient and constituent equivalences

`equivCompositionSeriesMultiplicityTransport` reuses the published
`Langlands.jordanHolderSeriesTransport` from
`Langlands.Representation.Filtration.JordanHolderTransportProof`. That
theorem constructs the actual image composition series with the same
length, simple factors and indexwise graded equivalences.

Write `f : s_i ≃ t_i` for a graded equivalence and `ψ : τ ≃ υ` for the
supplied constituent equivalence. A factor equivalence `q : t_i ≃ υ`
gives `f.trans q` followed by `ψ.symm`, hence `s_i ≃ τ`. Conversely,
`p : s_i ≃ τ` gives `f.symm.trans p` followed by `ψ`, hence `t_i ≃ υ`.
These implications identify the factor predicates at the same indices.
As above, `Equiv.subtypeEquiv` and `Nat.card_congr` give the exact count
equality. This adds count transport to the existing actual image-series
construction without proving that construction again.

## Multiplicity witnesses and scope

`equivJordanHolderMultiplicityTransport` transports each actual series
witness using the preceding ambient construction, and composes its exact
count equality with the supplied equality to `m`. The inverse ambient
and constituent equivalences give the reverse implication.

`groupEquivJordanHolderMultiplicityTransport` similarly transports an
actual witness by the supplied-filtration pullback construction. For the
reverse implication it pulls back along `e.symm`, then uses
`doublePullEquiv`, the identity linear equivalence from each double
pullback to the original representation. Its intertwining property is
`e (e.symm g) = g`. The fixed-group witness transport just proved then
returns the actual series witness to the original ambient and counted
representations, with the identical natural number `m`.

The final theorem bundles the four component proofs. All lengths are
included, with no positive-length or nonzero-representation restriction.
No composition series is chosen without a supplied witness. This is an
internal elementary proof for the published filtration, quotient and
representation-equivalence constructions; it has no external literature
attribution. It proves no additivity, finite-length theorem for induction,
Jacquet comparison, analytic continuation or classification result.
