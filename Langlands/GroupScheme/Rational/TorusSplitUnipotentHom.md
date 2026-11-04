# Homomorphisms from tori to split-unipotent groups

This internal adapter proves that every group-scheme homomorphism from an
arbitrary torus to a group with the existing finite normal Ga-series is the
trivial homomorphism. It works over every field in universe `u`, including
finite and imperfect fields and all characteristics. The source torus need
not be split. Affineness of the split-unipotent target is not an additional
premise.

First consider a vector-group target with natural coordinates of any dimension,
including zero. Give it the trivial action of the source torus, expressed
using conjugation along the zero homomorphism. This action is scalar-linear
in the supplied natural coordinates. The given homomorphism is an actual
normalized cocycle for this action: its cocycle morphism is the composite
of the projection to the torus with the homomorphism.

The published arbitrary-torus vector-cocycle theorem gives an actual rational
coboundary point. Every coboundary for the trivial action evaluates to the
identity on every scheme test. Consequently, so does the given homomorphism.
Evaluating at the universal source point proves equality with the actual
zero group-scheme homomorphism.

Induct on a finite Ga-series for the general target. At length zero, the
all-test triviality in the definition directly proves the conclusion.
At a successor, composition with the one-dimensional vector quotient is
zero by the vector case. The kernel equality in the specified fppf quotient
therefore puts the original homomorphism's all-test image in the given
closed subgroup. Evaluating this image inclusion at the universal source point gives an
actual scheme morphism through the subgroup. Cancellation against its monic
inclusion proves that the factor preserves the identity and multiplication,
so it is an actual group-scheme homomorphism. Induction makes this factor
zero and hence makes
the original homomorphism zero. No pointwise-surjectivity assumption is used.

Unpacking `IsSplitUnipotent` gives the unrestricted-length result.
`IsSplitUnipotent.uniqueHomFromTorus` packages the zero homomorphism and its
uniqueness into a `Unique` structure.

The provenance is internal: this composes the existing arbitrary-torus
linear-vector cocycle theorem, the definitions of cocycles and conjugation,
the published Ga-series predicate, and actual factorization through
represented subgroup functors. It does not prove that an arbitrary subgroup
of a torus is a torus, or that quotienting by a unipotent subgroup preserves
full maximality of a torus. Those are separate structural obligations of the
solvable maximal-torus conjugacy task.
