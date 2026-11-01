# Boolean interval cut contraction

Author: Worker 194. The imported signed cut diagram construction is by Worker 164.

This internal algebraic prerequisite proves contraction and homogeneous
exactness for a signed cut diagram with an invertible coordinate. It then
constructs the constant-coefficient diagram on a Boolean interval, proves
exactness when the interval has a free coordinate, and identifies the surviving
term of a singleton interval. The coefficient is any complex module, with no
finite-dimensionality assumption. The index and coefficient universes remain
independent.

The module reuses `CutComplex.Diagram`, its insertion sign and its existing
square-zero differential. It does not replace the differential with a new
sign convention. `sign_insert_self` shows that inserting a cut does not change
the position of that cut, and `sign_square` proves that every insertion sign
squares to one. `sign_mixed` compares one insertion and one deletion: for
distinct cuts, the two products of signs are opposites. Its proof considers
which cut is smaller and uses the change in the number of smaller members.

For a diagram `D` and cut `j`, `D.InvertibleCoordinate j` supplies a linear
equivalence from `D.Obj s` to `D.Obj (insert j s)` for every `s`. Its forward
map must be exactly the diagram's inclusion map. This is a hypothesis of the
generic construction, not a new premise for signed effectivity.
The diagram composition law implies `inverse_natural`: applying an inverse
insertion commutes with the maps in all the other coordinate directions.

The linear map `homotopy` deletes `j`. Its component at `s` is zero if `j`
already belongs to `s`; otherwise it applies the inverse insertion map to
the component at `insert j s`, with coefficient `sign s j`.
The identity `diagonal` says that insertion of `j` followed by this deletion,
plus the reverse composite, is the identity. It follows from the inverse-map
identities and the square of the sign. `off_diagonal` says that deletion of
`j` anticommutes with insertion of any other cut, using `inverse_natural`
and `sign_mixed`. Summing these identities gives

```text
differential (homotopy x) + homotopy (differential x) = x.
```

In particular, every total cocycle is a boundary. Deletion takes a homogeneous
family of degree `k+1` to degree `k`. Extension by zero and restriction give
`degreeHomotopy k`; `extend_degreeHomotopy` proves its compatibility with the
total map. Injectivity of extension transfers the contraction identity to
homogeneous degrees. Consequently `range_degreeDifferential_eq_ker` identifies
the range in degree `k+1` with the next kernel. Deletion of a degree-zero family
vanishes, so the same identity proves `degree_zero_injective`. These statements
use the existing actual linear maps, not an Euler-characteristic identity.

For required cuts `lower` and allowed cuts `upper`,
`BooleanInterval.Active lower upper s` means `lower ⊆ s ⊆ upper`.
`BooleanInterval.diagram lower upper M` has as its term the functions from
`PLift (Active lower upper s)` to `M`. This is canonically a copy of `M` when
the cut set is active, and the zero module otherwise. The map for `s ⊆ t`
evaluates the source function when `s` is active, and is zero otherwise.
When both endpoints are active, every intermediate cut set is active; this
proves the composition law. Thus the construction includes the actual zero
terms outside the interval.

A free cut `j ∈ upper` with `j ∉ lower` preserves activity under insertion.
Precomposition with this equivalence of activity propositions constructs
`invertibleCoordinate`, and its forward map is proved to equal the diagram
map. The preceding contraction therefore gives
`exact_of_free_coordinate` in every degree and
`injective_start_of_free_coordinate`.

When `lower = upper`, the only active set is `lower`.
`singleton_degree_subsingleton` proves that every other homogeneous term is
zero; `singletonDegreeEquiv` identifies the term in degree `lower.card` with
`M`; and `singleton_differential_zero` proves that every differential is zero.
This case retains its coefficient module as homology. For `lower ⊆ upper`,
`exact_below_allowed` combines the free-coordinate and singleton cases to prove
exactness in every degree strictly below `upper.card`.
`injective_before_allowed` gives injectivity at degree zero when
`0 < upper.card`. If both cut sets are empty, the surviving term is `M` in
degree zero and no injectivity of its outgoing zero differential is asserted.

The provenance is internal: all algebraic identities are proved directly
from the diagram laws, elementary finite-set identities and linearity.
This module constructs no actual Aubert graded piece and asserts no Bruhat
support image equality, graded transition-map comparison, finite-filtration
lifting, smooth representation structure or signed effectivity. The intended
application must identify its actual graded complex with the relevant interval
diagram and prove that the coefficient identifications carry the transition
maps to these inclusion maps with the stated exterior signs. Acyclicity of a
nontrivial interval must not be applied to the singleton surviving term.
