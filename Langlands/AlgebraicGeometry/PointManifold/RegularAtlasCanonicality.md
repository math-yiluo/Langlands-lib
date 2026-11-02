# Independence and naturality of regular atlases: exact targets

These internal proposition definitions state the choice independence and
actual-map consequences needed for the smooth affine point construction.
They use an affine object `X` over `Spec k`, an `RCLike` field `k` in
`Type`, and a natural number `d`. No algebraic smoothness hypothesis is
needed for these analytic consequences: the separate chart-existence
target must produce regular atlases from algebraic smoothness.

`regularAtlasIndependenceStatement k X d` says that any regular atlas `A`
of model dimension `d` and any regular atlas `B` of model dimension `e`
on the same actual point carrier admit an identity real `C∞`
diffeomorphism. The proposition explicitly passes `A.chartedSpace` and
`B.chartedSpace` to the two charted-space arguments of `Diffeomorph`.
Thus even when `d = e`, the source and target use their respective
atlases. The underlying equivalence is required to equal `Equiv.refl`.
There is no assumption that `d` or `e` is positive or that points exist.

`regularAtlasMorphismSmoothnessStatement k X d` says that for every affine
`Y` over the same field, every dimension `e`, atlases `A` and `B`, and
actual relative morphism `f : X ⟶ Y`, the actual point map
`p ↦ p ≫ f` is real `C∞`. Its source and target charted spaces are also
explicitly distinguished. No smoothness or étaleness assumption on `f`
is imposed.

`regularAtlasEvaluationSmoothnessStatement k X d` says that evaluation of
every global regular function is real `C∞` from each regular atlas into
`k` with its real normed-space model.

`regularAtlasIsomorphismStatement k X d` says that each actual relative
isomorphism `f : X ≅ Y` induces a real `C∞` diffeomorphism between any
two regular atlases. Both its forward and inverse maps are required to
be the actual postcomposition maps. This supplies the presentation
comparison when two affine presentations are related by their given
scheme isomorphism. For choices on the same scheme the preceding
identity statement gives literal identity on actual points. Every
charted space here has the already published regular-evaluation
topology, since `RegularAtlas.chartedSpace` takes that topology as an
input; these statements introduce no replacement topology.

`regularAtlasCanonicalityStatement` is the conjunction of the four
propositions. Each declaration is `Prop`-valued and unproved. None
constructs a manifold from algebraic smoothness by itself. The actual
real and complex fields are included in the `RCLike` formulation.

The provenance is internal. The intended proof applies the independently
stated regular-atlas manifold and family comparison in
`RegularAtlasComparison` to the two atlases. Actual morphism smoothness
then follows by pullback of global regular functions, evaluation
smoothness by applying the family criterion to the identity, and
identity/isomorphism diffeomorphisms by the two resulting smooth maps.
No proof or unconditional algebraic-to-differential construction is
asserted in this statement file.
