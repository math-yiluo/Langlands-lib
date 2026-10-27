# Carrier comparison for the literal three-block bracketings

Author: Worker 645.

This module supplies internal concrete carrier adapters. It does not prove
associativity. The three source carriers lie in independent universes. The
three comparison carriers share a universe of the form `max uF uW`, so actual
normalized induction remains in that same universe at the second node.

`heterogeneousLeftCommonEquiv` applies `heterogeneousPairToPairEquiv` first to
the factors of ranks `(A,B)` and then to the factors of ranks `(C,A+B)`.
`heterogeneousRightCommonEquiv` applies it first to `(C,A)` and then to
`(C+A,B)`. Both maps compare actual smooth-function representations. Each
heterogeneous node is precisely `PadicField.heterogeneousPair`, whose definition
contains the two literal ULift conjugations. Expanding the two nodes on each
side recovers all four induction nodes and all eight lifts in the target.

`Representation.Equiv.ofPrecompComparison` composes the left carrier
comparison, an equivalence after group precomposition, and the inverse right
comparison for arbitrary groups and complex modules.

`heterogeneousAssociativityEquiv` specializes that composition to the three
actual factor equivalences and
an actual equivalence between the two common-universe bracketings. It
precomposes the left comparison by exactly
`GeneralLinear.reindex (finCongr (Nat.add_assoc C A B))`, composes with the
supplied common-universe equivalence, then applies the inverse right
comparison. The result is an equivalence between the literal heterogeneous
left action precomposed by that fixed rank transport and the literal right
action. The transport preserves every matrix entry's natural coordinate and
has direction `GL_((C+A)+B) -> GL_(C+(A+B))`.

The common-universe equivalence is an explicit input to this adapter. This
module does not assert its existence, does not replace the induced actions
with unspecified data, and does not discharge the final target proof. The
consumer must separately construct that equivalence from ordered regrouping,
then use these maps with the three `up` equivalences to a shared universe.
No representation condition is needed merely to transport equivalences.

The provenance is internal and derived from the exact pair construction,
`Induction.HeterogeneousConstruction`, and `Representation.Equiv.precomp`.
The implemented proof is composition of those concrete equivalences, with
no external source translation or additional axiom.
