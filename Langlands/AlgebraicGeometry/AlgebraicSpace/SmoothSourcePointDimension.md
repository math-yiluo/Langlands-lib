# Intrinsic dimensions of arbitrary smooth algebraic spaces over a field

Author: Worker 502.

This is a derived host bridge for the manifold clause of Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
printed p.15, Proposition 5.4. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The dimension function is supporting content derived from the Library geometry,
not a separately numbered assertion in Conrad.

For a field `K`, an actual algebraic space `X` over `Spec K`, and
`hX : SmoothOverBase X`, `SmoothDimensionPieces.atlas` and `atlasMap`
choose the actual smooth, surjective, etale scheme atlas supplied by
`StructuralAtlasGeometry.SmoothOverBase`. Its source is locally Noetherian:
its structure map is smooth, hence locally of finite type over the Noetherian
field spectrum, and `LocallyOfFiniteType.isLocallyNoetherian` applies.
There is no quasi-compactness, finite type, connectedness, separatedness or
finite-range assumption.

`structuralChart` places any etale chart over `K` in a commuting chart square
for the existing `structuralMorphism X`. Its target is the identity chart of
`Spec K`; commutativity follows from `basePresheafIsTerminal`.
`pointDimension hX : Points X.presheaf → ℕ` is exactly
`EtaleMorphismChart.pointDimension` from `SmoothRelativePointDimension`,
applied to this structural atlas. This reuses its componentwise smooth scheme
dimension and actual local relative topological Krull dimension; no parallel
dimension notion or assumed dimension laws are introduced.

`pointDimension_spec` is the existing all-chart specification specialized to
the structure map. It applies to every commuting etale chart square, including
non-surjective source charts. `pointDimension_chart` expresses it directly for
every etale scheme chart `U → X` over `K`, with value
`relativeTopologicalKrullDimAt U.hom x` in `WithBot ℕ∞`.
`pointDimension_isLocallyConstant` reuses the existing local-constancy theorem
for `pointTopology X.presheaf`, the ordinary quotient point topology.

`pointDimension_eq_of_atlas` compares the construction with any other actual
smooth surjective etale atlas with locally Noetherian source. (Over the field,
that last property follows from smoothness.) Lift each quotient point to that
atlas, apply the two all-chart specifications and use injectivity of the
natural-number cast. Thus atlas choices do not affect the function;
`pointDimension_independent` also records independence from the smoothness
witness.

This unit supplies only the intrinsic numerical function. Genuine algebraic
dimension pieces, restricted atlases and section maps are the next construction
units. The homeomorphism for the etale-chart rational-point topology,
functorial analytic assembly across intersections with target dimension pieces,
etale dimension preservation and local analytic isomorphisms, and uniqueness
of a varying-dimensional analytic structure remain subsequent statement and
proof obligations. The full manifold assertion is not claimed here.
