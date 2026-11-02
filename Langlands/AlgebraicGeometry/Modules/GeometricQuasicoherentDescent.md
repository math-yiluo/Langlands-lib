# Effective geometric descent with quasi-coherence and relative flatness

This internal unit uses the actual ordinary module categories of schemes in
an arbitrary universe `u`, and the rank-independent, all-scheme-test `Datum`
and `Str` of `LineBundleFlatDescentStr`.

For an affine flat surjection `p : X → Y` and a quasi-coherent module `F` on
`X` carrying a geometric datum `D`, the conclusions are:

- Every effective structure `Str D t N`, on any test scheme `t : T → Y`,
  forces `N` to be quasi-coherent.
- Such a quasi-coherent effective module exists on every test scheme.
- For any two effective structures on the same test, there is exactly one
  actual module isomorphism compatible with all their comparison maps.

For the first conclusion, the comparison map on `X ×_Y T` identifies the
pullback of `N` with the pullback of `F`. The latter is quasi-coherent.
The projection to `T` is again affine, flat and surjective, so
`FaithfullyFlatQuasicoherentDescent` detects quasi-coherence of `N`.
Existence starts with the actual ordinary module and effective structure
provided by `GeometricModuleEffectivity`, and restricts that structure
along `t`. The first conclusion supplies quasi-coherence. The uniqueness
result applies the published compatible-isomorphism descent theorem of
`GeometricModuleDescent`, with its target quasi-coherence premise now
discharged from the effective structure.

The construction `pullbackIsoOfStr` itself has no affine, flat, surjective
or quasi-coherence hypotheses. For an effective structure on `Y`, its
comparison at `(X, id_X, p)` gives `p*N ≅ id_X*F`. Composition with the
actual pullback identity comparison gives the actual isomorphism `p*N ≅ F`.

There are two relative-flatness consequences. If `p` is flat and
surjective and `F` is flat over `p ≫ f` for a fixed `f : Y → B`, then
every effective module `N` on `Y` is flat over `f`. Transport relative
flatness through `pullbackIsoOfStr`, then apply the published detection
theorem along a flat surjection of the source.

In a Cartesian square with maps `p : X → Y`, `q : X → T`, `f : Y → B`,
and flat surjective `g : T → B`, flatness of `F` over `q` implies
flatness of every effective module over `f`. The square makes `p` flat
and surjective. Flatness of `g` permits composition of relative flatness
from `q` to `q ≫ g = p ≫ f`, reducing to the previous consequence.
These relative-flatness results need no quasi-coherence premise.

The provenance is internal: this unit composes the specified geometric
effectivity, quasi-coherence detection, compatible-isomorphism uniqueness,
and actual relative-stalk-flatness descent results. It introduces no
literature assertion. It does not assert finite presentation,
effectivity of arbitrary covering-family descent data, a stack condition,
or an atlas.
