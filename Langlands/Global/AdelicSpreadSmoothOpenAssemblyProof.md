# Proof of the assembly of Conrad's Theorem 4.5

`adelicSpreadSmoothOpenAssembly` proves `AdelicSpreadSmoothOpenAssemblyStatement`.
Given its five premises, it derives Theorem 4.5 of Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.12–13, for arbitrary finite-type spreads in both characteristics. The
premises stay explicit hypotheses. The proof establishes none of them, in
particular not uniform Lang–Weil.

The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The assembly and its arithmetic enlargement are derived implementation steps
for the cited proof. This pair reuses Worker 208's complete shared proof draft,
with its Lean source unchanged.

## Absolute finite type of models

`locallyOfFiniteType_toSpecULiftZ_of_over` takes a ring `R` of finite type
over `ℤ` and a model `X` locally of finite type over `Spec R`. It shows that
the canonical map from `X` to `Spec (ULift ℤ)` is locally of finite type. The
ring `R` becomes a `ULift ℤ`-algebra through `Langlands.ULiftInt.algebra`, and
it is of finite type over `ULift ℤ` by restriction of scalars. The structure
map of `Spec R` is then locally of finite type. Terminality identifies the
canonical map of `X` with the composite of `X.hom` and this map.
`over_hom_separated_quasiCompact` shows that a morphism of models is
separated and quasi-compact when its source is quasi-compact and separated
and its target is separated. The usual cancellation lemmas give this, since
the composite with the target structure map is the source structure map.

## Fixed models at a finite-type level

The private lemmas `curve_fixedModel_open` and `number_fixedModel_open` work
at a level whose actual integer ring is of finite type over `ℤ`. Take
separated, quasi-compact, finite-type models `M`, `N` there and a smooth,
geometrically connected `gm : M ⟶ N`. The fixed-model reduction premise is
applied to `gm`. Its local-openness hypothesis is the local premise at every
enlarged level and factor. Its cofinite-surjectivity hypothesis is the
level-component premise, applied with uniform Lang–Weil and target `N`. Here
`N` has finite type over the integers by the first helper, and `N` is
compact because `Spec R` is compact and `N.hom` is quasi-compact. Separation
and quasi-compactness of `gm` come from the second helper.

`curve_spread_open_of_model` and `number_spread_open_of_model` transport this
openness to the spread topologies of compatible generic-fibre isomorphisms
`e`, `f`. These topologies are defined by the published homeomorphisms
`...SpreadAdelePointHomeomorph`. The published naturality lemma
`...GenericFiberAdelePointEquiv_natural` and the compatibility equation show
that the generic map `p ↦ p ≫ g` is the fixed-model map conjugated by these
homeomorphisms. This follows the published proper-map proof
`AdelicSpreadProperMapProof`.

## Enlargement and arbitrary spreads

In `curvePlaceSpreadSmoothOpenAssembly`, the source and target schemes over
the field are first shown to be locally of finite type and quasi-compact,
since they have finite-type spreads. They are separated by hypothesis. The
model premise for `Smooth ⊓ GeometricallyConnected` then provides a level
`T`, compatible separated finite-type models `M`, `N` and a smooth
geometrically connected model map `gm`. The published construction
`curvePlacePrincipalLevelAbove k F T` chooses a level `U` above `T`. Its
actual integer ring has finite type over `ℤ` by the published instance. The
models and `gm` are pulled back to `U` with `curvePlaceLevelModelBaseChange`.
This pullback preserves finite type, quasi-compactness and separatedness.
`MorphismProperty.overPullbackMap` preserves smoothness and geometric
connectedness of the map. The generic fibres of the pulled-back models are
identified with the original ones by `modelPullbackCompIso`.
`pullbackComp_naturality` carries the compatibility equation to level `U`.
The published `curvePlaceSpreadTopologyIndependence` rewrites both given
spread topologies as those of the pulled-back models. Finiteness of `k`
supplies its perfect-field hypothesis. The previous lemma then concludes.

`numberFieldSpreadSmoothOpenAssembly` repeats the argument with
`numberFieldPrincipalLevelAbove`, `numberFieldLevelModelBaseChange` and
`numberFieldSpreadTopologyIndependence`. The full adeles keep all infinite
factors throughout. `adelicSpreadSmoothOpenAssembly` pairs the two theorems.
The theorem uses only the standard axioms.
