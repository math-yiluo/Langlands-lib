# Original tensor associativity interface checks

Worker 691 supplies internal checks for the additive associativity statement
interfaces. These do not prove the principal associator or its naturality.
The mathematical provenance and source scope are in
`NonUnitalTensorAssociativityStatements.md`.

Every principal proposition is used unapplied against its complete telescope.
The two complementary assignments `(0,1,0,1,0,1,0,1)` and
`(1,0,1,0,1,0,1,0)` refer in order to the universes of
`R,S,X,Y,Z,X',Y',Z'`. Both are checked in addition to the independent generic
universes. Exact definitional equalities unfold the triple-tensor formulas,
both whole nested lifts, both inverse identities, canonical and existence
clauses, the two whole-map naturality squares, and the closed target. The
closed target is also unfolded at both complementary assignments. The
inner evaluation helpers and their actual quotient lifts are checked
pointwise or as whole maps according to their roles.

The competing-structure section introduces original ring structures on `R,S`,
original additive groups and original actions on all six carriers, while
installing separate ring, group and action instances. Competing groups and
residual actions are also installed on all four inner tensor carriers and
competing groups on all four iterated tensor carriers. Definitional checks
first establish that instance search really selects the competing structures.
Fully explicit applications then check the original quotient carriers,
inherited groups, evaluation pairings, whole outer lifts, existential
witness type and both general naturality squares. The expected expressions
use the named original residual actions and published one-sided maps.

The boundary checks form the proposition interfaces for subsingleton carriers
at independent universes over arbitrary rings. On nonzero integer groups
with zero original actions, the interfaces still elaborate; the actions are
explicitly degenerate and the unit law fails. Both actual iterated quotient
tensors are proved nonzero by detecting the pure tensor `(1,1,1)` with
integer-valued nested quotient lifts. Multiplication of integers is balanced
for the zero actions because both scalar inputs vanish. The residual scalar
endomorphisms are zero by pure-tensor extensionality; this proves balancing
of the outer detecting pairings. Applying the resulting whole additive maps
to an alleged zero pure tensor would give `1 = 0`. No associator is used in
these nonzero checks.

For regular integer actions, the interfaces elaborate and the residual
pure-tensor actions are exactly multiplication on the middle factor.
Forward and inverse evaluation pairings have the prescribed triple-tensor
values in both the regular and zero-action settings. All these are internal
scope checks, not a proof of `NonUnitalTensorAssociativityTheorem`.
