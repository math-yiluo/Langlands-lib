# Pullback comparison at actual arithmetic levels

`Langlands.Global.adelicLevelModelPullback` proves exactly
`Langlands.Global.AdelicLevelModelPullbackStatement` in arbitrary common
universe `u`. Both arithmetic clauses use the original actual relative
scheme points, arithmetic integer bases, level rings and level topologies.
The comparison sends a point to its two composites with the projections
of the specified limiting pullback cone. Its target is the subspace of
globally compatible pairs in the product of the two level point spaces.

The proof first establishes a private general result. Let `C` be a
commutative ring, `A` a `C`-algebra, and `R i` a family of local
topological `C`-algebras with open units. Specify algebra maps
`π i : A →ₐ[C] R i`. For a scheme `X` over `Spec C`,
`localModelRestriction` first changes the coefficients of an actual
`A`-point along `π i`, then applies the existing actual scalar
base-change point equivalence. `restrictionPointTopology` is the
initial topology of this map into the product of the existing
`schemePointTopology` spaces on the base-changed models.

`localModelRestriction_natural` follows from associativity of
composition and `ringPointBaseChangeEquiv_natural`. The restriction map
is inducing by definition of the topology. Consequently
`continuous_restrictionPointMap` proves continuity of postcomposition:
after testing at every factor, naturality identifies it with
postcomposition on a local model, where `schemePointContinuity_proof`
applies.

For a limiting pullback cone `c`, the already constructed equivalence
`affineSchemePullbackPointEquiv C A c hc` identifies actual points of
`c.pt` with globally compatible pairs. Its historical name imposes no
affineness hypothesis. Its forward map is continuous because its two
coordinates are the just-proved continuous postcomposition maps.

To prove continuity of the inverse, test it through every local
restriction. The actual scalar base-change functor
`Over.pullback (Spec.algebraMap C (R i))` is a right adjoint and
preserves limits. Thus the base-changed cone `c.map F` is limiting.
The published `schemePullbackPointHomeomorph` gives a homeomorphism
for points of this cone over `R i`, for arbitrary schemes.

The map `t` from globally compatible pairs to locally compatible
pairs restricts both coordinates. Naturality proves its compatibility
equation, and its two coordinates are continuous by the initial
topology construction. The restriction of the original inverse
comparison equals the local inverse homeomorphism composed with `t`.
To prove that equality, apply the local homeomorphism, compare the two
projections, use naturality and the original equivalence's inverse
identity. The local inverse is continuous, so each restriction of the
original inverse is continuous. The inducing property and continuity
into a product conclude the general homeomorphism assertion.

The curve clause instantiates this result with
`curvePlaceSIntegers`, `curvePlaceAdeleLevel`, the actual
`CurvePlaceLevelFactor` family and `curvePlaceLevelFactorAlgHom`.
The number-field clause uses the actual `S`-integer ring,
`numberFieldAdeleLevel`, `NumberFieldLevelFactor` and
`numberFieldLevelFactorAlgHom`. The proved `adelicLocalFactorUnits`
supplies the open-unit hypotheses in both cases. The private initial
topologies and maps specialize definitionally to the existing level
topologies and maps. Every infinite number-field factor is retained.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The paragraph on printed p.8 after the proof of Theorem 3.6 states
preservation of fiber products for finite-type arithmetic models;
printed pp.6–8 construct their topology. The arbitrary-scheme and
arbitrary-curve-field scope is the derived extension explained in the
target Markdown. The implemented proof does not use injectivity or
surjectivity of a level-to-product point map. It adds no finite-type,
separatedness, quasi-separatedness, compactness, finite-constant-field
or nonempty-`S` assumption. Preservation for fixed-model final
topologies and generic-fiber adelic topologies remains a separate
assertion.
