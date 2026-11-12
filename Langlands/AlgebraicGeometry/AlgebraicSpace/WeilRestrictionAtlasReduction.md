# Reduction of restricted atlases to restricted schemes over test schemes

Author: Worker 185.

This is derived infrastructure for the affine-atlas step in Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Lemma 5.10,
printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`). Conrad notes that restriction of
scalars carries an étale surjective atlas `U' → X'` to an étale surjective map
`R_{S'/S}(U') → R_{S'/S}(X')`. This module reduces that statement to one input
about schemes, `RepresentationInput`; the input is proved in
`WeilRestrictionAtlasLocalRepresentation`. The reduction is written for this
Library and is not copied from the source.

All declarations are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAtlas`.

## Comparison with the fibre presheaf

Fix `π : S' ⟶ S` and a scheme `V` over `S`. `testSquare π V` is the pullback
square of `V.hom` and `π`, with `V' = (Over.pullback π).obj V` the base change.
`unitPoint π V` is the tautological point of the restricted presheaf
`(Over.pullback π).op ⋙ (schemeYoneda S').obj V'` over `V`: the identity of
`V'`. `unitPoint_app_pt` evaluates it at a morphism `c : T ⟶ V` as the point
`(Over.pullback π).map c`.

For a scheme `T` over `V.left`, `testIso π T` is the Library's comparison
`WeilRestrictionBaseChange.testIso` of the two ways of base-changing `T` to
`S'`: along `pullback.fst V.hom π` and, after viewing `T` over `S`, along `π`.
`testIso_hom_map_toTest` and `testIso_inv_naturality` record its compatibility
with `toTest T` and its naturality in `T`.

Now let `qY : Y ⟶ V'` be a morphism of schemes over `S'`. `fibreScheme π qY` is
`Y` regarded as a scheme over the base change `V.left ×_S S'` via `qY.left`.
`fibre π qY` is the presheaf `TestFibre.presheaf` (module
`TestFibreRepresentation`) of the restricted transformation
`Functor.whiskerLeft (Over.pullback π).op ((schemeYoneda S').map qY)` at the
point `unitPoint π V`. Its value at `T` over `V.left` is the set of morphisms
`y` from the base change of `T` to `Y` over `S'` with `y ≫ qY` equal to the
base change of `toTest T` (`mem_fibre_iff`).

`toFibreHom` and `ofFibreHom` transport such morphisms through `testIso`; they
are mutually inverse (`fibreEquiv`). `fibreIso π qY` is the resulting natural
isomorphism between the restriction
`(Over.pullback (pullback.fst V.hom π)).op ⋙ (schemeYoneda _).obj (fibreScheme π qY)`
of `fibreScheme π qY` to schemes over `V.left` and `fibre π qY`. Naturality
follows from `testIso_inv_naturality`.

## Quasi-compactness and separation of represented base changes

`quasiCompact_isSeparated_of_isPullback` states: let `X` be a quasi-separated
algebraic space over `S`, that is, its diagonal is relatively quasi-compact. Let
`a` be a chart from an affine scheme `U` over `S` (`IsAffineHom U.hom`) and `x`
a point of `X` over a scheme `V`. If `(p, q)` is a pullback square of
represented presheaves for `a` and `x`, then `q.left` is quasi-compact and
separated. Proof: the pairing `m = prod.lift p q : Y ⟶ U ⨯ V` is a base change
of the diagonal, so it is quasi-compact by the Library lemma
`relative_diagonal_property_chart_pairing`. It is a monomorphism, because the
represented square has unique lifts, so it is separated. The projection
`U ⨯ V ⟶ V` is, through `Over.prodLeftIsoPullback`, the base change of the
affine morphism `U.hom`, hence affine, quasi-compact and separated. `q.left` is
the composite of `m.left` and this projection.

## The representation input and the assembly

`RepresentationInput` is the proposition: for every finite projective algebra
`R → R'`, every scheme `V` over `Spec R`, and every scheme `Y` over
`V.left ×_{Spec R} Spec R'` that is étale, surjective, quasi-compact and
separated, there is a scheme `W` over `V.left` that is étale and surjective,
together with an isomorphism from its represented presheaf to the restriction
`(Over.pullback (pullback.fst V.hom π)).op ⋙ (schemeYoneda _).obj Y` of `Y`,
where `π = Spec.algebraMap R R'`. It is an internal intermediate statement, not
a Library target.

`exists_isPullback` assumes `RepresentationInput`. It takes the data of the
target: a quasi-separated algebraic space `X'` over `Spec R'`, an affine scheme
`U'` over `Spec R'`, and an étale surjective `a` from its represented presheaf
to `X'`. For a test scheme `V` over `Spec R` and a point `g` of the restricted
presheaf of `X'` over `V`, it gives an étale surjective scheme `W` over `V.left`
and a pullback square of presheaves on schemes over `Spec R`. In that square
the restricted transformation `Functor.whiskerLeft (Over.pullback π).op a` is
pulled back along `g` to the represented projection
`(schemeYoneda _).map (toTest W)`. Proof:

1. `g` corresponds to a point `x` of `X'` over `V'`. Representability of `a`
   gives a pullback square with `qY : Y ⟶ V'` (`ha.rep.isPullback'`). `qY.left`
   is étale and surjective because `a` is, and quasi-compact and separated by
   `quasiCompact_isSeparated_of_isPullback`.
2. `RepresentationInput`, applied to `fibreScheme π qY`, gives `W` and an
   isomorphism to its restriction; composing with `fibreIso π qY` gives an
   isomorphism to `fibre π qY`. `TestFibre.isPullback` turns this into a
   pullback square over `unitPoint π V`.
3. Restricting the pullback square of `x` along `Over.pullback π`
   (`weilRestriction_presheaf_isPullback`) and pasting horizontally gives a
   pullback square over `unitPoint π V ≫ whiskerLeft x`. This composite equals
   `g`: both have the same Yoneda element.

`weilRestrictionAffineEtaleAtlas_of_representationInput` derives
`WeilRestrictionAffineEtaleAtlasStatement` from `RepresentationInput`.
Étaleness and surjectivity of the restricted transformation are relative
properties. `MorphismProperty.relative.of_exists` proves each from one
pullback square per test point with the property; `exists_isPullback` supplies
the square. The represented projection's underlying morphism is definitionally
`W.hom` (as recorded by `TestFibre.toTest_left`).
