# The ordinary-module dictionary for categorical geometric descent

This internal construction connects the full categorical singleton descent data
of the core of ordinary modules to the geometric descent data used by the
published module effectivity results. The scheme universe `u` is arbitrary.
The schemes and test morphisms are unrestricted.

## Objects and pullback coherence

`pseudofunctor` is `corePseudofunctor` applied to the published ordinary module
pseudofunctor on schemes after forgetting its adjunction structure. Its objects
are actual ordinary modules and its arrows are their actual isomorphisms.
`mod` and `modHom` recover the underlying module and module morphism.

The identity, composition and pullback formulas for `modHom` are definitional.
The two `mapComp'` formulas identify the pseudofunctor comparisons with the
ordinary module `compIso`, with the hom comparison corresponding to the inverse
of `compIso`. They are proved by reducing the composite morphism to the literal
composite and unfolding the published coherence constructions.
`modHom_pullHom` consequently identifies categorical transport with geometric
transport `tr`. `modHom_toDescentData_obj_hom` expresses the transition of a
pulled-back object as the composite of the first `compIso` hom and the second
`compIso` inverse.

## From categorical data to geometric data

For an arbitrary morphism `p : X ⟶ Y`, `datum p D` has cover module
`mod (D.obj ())`. Its comparison for maps `a b : V ⟶ X` with equal composites
to `Y` is the actual isomorphism underlying `D.hom`, evaluated with common
composite `a ≫ p`. Categorical transport and the preceding comparison formula
prove naturality on every scheme test. The categorical composition law proves
the geometric cocycle law. `hom_congr` reconciles equal common composites;
`datum_θ_hom` records the comparison's underlying morphism.

## Returning an effective structure to categorical data

`effectiveIso p D M S` assumes an actual effective geometric structure
`S : Str (datum p D) (𝟙 Y) M` and constructs an isomorphism
from the categorical descent datum of the actual core object `⟨M⟩` to `D`.
Its component is `S.γ` at the identity of `X`, followed by the ordinary
pullback identity isomorphism. Naturality of `S` expresses every pullback of
this component through `compIso` and the corresponding test comparison.
The ordinary pullback unit law and cancellation reduce compatibility with
`D.hom` to the cocycle compatibility of `S`. `Core.isoMk` and
`Pseudofunctor.DescentData.isoMk` package this component and its verified
compatibility into the actual categorical isomorphism.

`exists_effective` assumes that `p` is affine, flat and surjective and that
the cover module `mod (D.obj ())` is quasi-coherent. Published geometric
quasi-coherent effectivity supplies a quasi-coherent ordinary module `M`
and an effective structure `S`; `effectiveIso` supplies the categorical
isomorphism. No affineness assumption is imposed on `Y`.

## Provenance and scope

The comparison calculations and the reverse construction adapt the
rank-independent portions of the published `Picard.LineBundleStackDictionary`
and `Picard.LineBundleStackBase`. This file constructs the core of all ordinary
modules directly and does not instantiate their rank-one `ModuleRealization`.
The effectivity input is `Modules.GeometricQuasicoherentDescent.exists_str`.
All assertions here are internal consequences of those published constructions.

This file proves singleton categorical effectivity with the stated
quasi-coherence assumption. It does not assert effectivity for arbitrary
ordinary modules, descent for general covering families, a stack condition,
or the coherent-family atlas theorem.
