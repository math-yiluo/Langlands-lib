# Topology families and source axioms for actual nonaffine points

This construction makes explicit the assignments and requirements appearing in
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), Proposition 3.1, printed page 4. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The formulation with coefficient ring `R` and value `R`-algebra `S` is a derived
relative extension of the source setting `S = R`. It is infrastructure for
separate existence and uniqueness statements, and proves neither assertion.

## The actual assignments

All declarations belong to `Langlands.AlgebraicGeometry.PointTopology`.
`R` and `S` are commutative rings in a common arbitrary universe, with their
specified `Algebra R S`. `SchemePointTopologyFamily R S` assigns an arbitrary
topology to the actual carrier `RingPoint R X S` for every scheme `X` over
`Spec R` with `LocallyOfFiniteType X.hom`. The family has no compatibility
fields. Its domain includes nonaffine and nonseparated schemes and requires
neither quasi-compactness nor finite presentation.

`schemePointTopologyFamilyToAffines` restricts a family to the published
finite-type affine family. The latter is represented using affine schemes
whose structure morphisms are locally of finite type; for affines this is
finite type. `evaluationSchemePointTopologyFamily` instead assigns the
published `schemePointTopology` to every scheme in the full locally finite
type domain. That named topology is constructed independently as the final
topology of actual affine-open point charts. Its definition requires only a
topology on `S` and assumes none of the requirements below.

## The five requirements

For an arbitrary assignment `T`, the following are Prop-valued definitions:

- `SchemePointTopologyFunctorial` requires continuity of actual relative
  scheme postcomposition for every morphism in the family domain.
- `SchemePointTopologyPullbacks` requires the actual comparison for every
  limiting relative pullback cone to be a homeomorphism onto the compatible
  pairs, equipped with the subspace topology from the product of `T X` and
  `T Y`. The common point of the cone's base varies. An explicit locally
  finite type instance for the apex supplies its family-domain witness;
  actual pullbacks of these schemes have this property. The imported
  comparison function has an historical `affineScheme` prefix but imposes
  no affine condition.
- `SchemePointTopologyClosedImmersions` requires actual closed immersions
  to induce embeddings. It imposes no closed-image requirement.
- `SchemePointTopologyOpenImmersions` requires actual open immersions to
  induce open embeddings.
- `SchemePointTopologyLine` requires coordinate evaluation on the actual
  affine line `Spec (MvPolynomial Unit R)` to be a homeomorphism onto `S`
  with its given topology.

`SchemePointTopologyAxioms` is their conjunction, listing closed and open
immersions separately. Each condition selects the family topologies
explicitly, so no inferred alternate topology supplies its conclusion.
There is no assumed theorem about the canonical family.

The source gives these requirements for a local topological ring with open
units and continuous inversion, on locally finite type schemes. The predicates
can be formulated without those ring hypotheses, and hence do not include
them in their definitions; later existence and uniqueness targets must state
their needed hypotheses individually. Only the normalization predicate and
the canonical family use a topology on `S`. No topology on `R` is imposed.
Fixed base coefficients become constants in `S`, which explains the relative
formulation of the affine-line normalization and actual point maps. This
unit does not assert that arbitrary such ring data admit a family satisfying
these requirements, or that the requirements determine a unique family.
