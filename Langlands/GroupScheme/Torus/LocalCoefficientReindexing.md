# Gluing locally specified coefficient permutations

This internal construction glues coefficient-algebra reindexings along an open
cover of an arbitrary scheme. It is derived from the structure sheaf's unique
gluing property and elementary permutation algebra.

`LocalCoefficientReindexing.Datum S I J` consists of a small open cover and
equivalences `J ≃ I` on its members. The supplied equivalences must agree
whenever two cover members have nonempty intersection. No equality of
permutations is required on an empty intersection. Neither index type is
required to be inhabited or finite.

`permutation_eq_of_unitTests` derives the agreement condition when both
permutations describe one transformation on families of units on all relative
tests whose image lies in the respective open. On a nonempty intersection,
the dual-number test of `SplitCoordinateSeparation` supplies a unit different
from one. A family supported at one index distinguishes any two different
images of an input index. `ofUnitTransform` therefore constructs a `Datum`
from an open cover of local formulas for a single transformation. This
uniqueness argument needs no naturality assumption on the transformation.

For a family of global sections indexed by `I`, the local output at `j : J`
is its coordinate selected by the supplied permutation, restricted to that
cover member. These sections are compatible: on a nonempty intersection the
indices agree, while on an empty intersection the sheaf has only one section.
The structure sheaf uniquely glues them to `sectionMap`.

`Datum.hom` is the resulting algebra homomorphism from `I`-indexed to
`J`-indexed global sections over `Γ(S, ⊤)`. All algebra laws follow by restricting
to each cover member. Reversing the local permutations gives an inverse
homomorphism: the two compositions are locally the identity and hence globally
the identity. `Datum.equiv` packages the actual algebra equivalence, and
`equiv_restrict` records its local coordinate formula.

The construction does not assume affineness, connectedness, nonemptiness, or a
constant permutation on the whole base. Establishing the local unit-test
formulas for transitions of torus charts and establishing descent cocycles
remain separate obligations.
