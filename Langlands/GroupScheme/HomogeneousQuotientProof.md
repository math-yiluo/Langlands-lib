# Scheme quotients by smooth closed subgroups

`smoothSubgroupQuotientExistence` proves exactly the published proposition
`Langlands.GroupScheme.SmoothSubgroupQuotientExistenceStatement.{u}`,
for arbitrary universe `u`.

For every field `k`, actual smooth affine group scheme `G` over `Spec k`,
and actual smooth closed subgroup `i : H → G`, the theorem supplies an
actual relative scheme `Q` and morphism `q : G → Q`. The structural
morphism of `Q` is separated, locally of finite type and quasi-compact.
The morphism `q` is smooth, surjective and quasi-compact. On every
relative scheme `T`, equality `g ≫ q = h ≫ q` is equivalent to
membership of `g⁻¹ h` in precisely `SubgroupFunctor.range i` on `T`.
This includes nonaffine and nonreduced tests and fields of any
characteristic or cardinality.

The implemented proof has two inputs. First,
`Chevalley.exists_line_stabilizer` constructs an actual finite matrix
representation and a coordinate line whose global-unit scalar stabilizer
is exactly that subgroup on every relative scheme test. Its finite-type
hypothesis on `G` follows from smoothness. Second,
`ProjectiveOrbit.quotientOfLineStabilizer` constructs the actual quotient
from this representation, closedness of `i` and smoothness of `H`.
The proof returns the scheme, projection, six geometric properties
and all-test fiber criterion from that constructed quotient.

The imported construction identifies the canonical relative coordinate
section with its normalized pullback, converts its fixed-section
condition into the matrix scalar-unit condition, and obtains exact
coset fibers for the actual orbit morphism into a separated projective
scheme. The smooth equivalence-relation quotient and its embedding into
that scheme give schemehood; descent and quasi-compactness arguments
in `HomogeneousQuotientFromEmbedding` provide the remaining properties.
These steps are proved in the imported modules and introduce no extra
premises into the theorem.

This final assembly is derived from those constructions. The line
stabilizer was constructed by Worker 669; the projective comparison
and quotient geometry were constructed by Worker 148. The published
target and its imported definitions are unchanged. No reductivity,
connectedness, splitness, algebraic closure or infinitude assumption is
used.
