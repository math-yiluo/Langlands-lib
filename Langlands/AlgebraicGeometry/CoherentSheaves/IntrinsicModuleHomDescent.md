# Descent of all morphisms of actual module sheaves

For any schemes `Y` and `B` in universe `u`, any morphism `p : Y ⟶ B`,
and actual module sheaves `M N : Y.Modules` with quasi-coherent target `N`,
`intrinsicModuleHomSheaf p M N` is the fppf sheaf on the entire scheme
slice over `B` whose underlying presheaf is exactly
`intrinsicModuleHomPresheaf p M N`.

At every `Z : Over B`, its values retain the explicit `ULift` of all maps
between the ordinary pullbacks of `M` and `N` to `Z.left ×[B] Y`.
Its restrictions are the restrictions of the published intrinsic
presheaf. No hypothesis on `p`, on the source module `M`, or on the
base and test schemes is imposed. In particular, the source need not be
quasi-coherent.

The theorem `isSheaf_intrinsicModuleHomPresheaf_fpqc` proves the stronger
fpqc sheaf condition for this same presheaf.
`isSheaf_intrinsicModuleHomPresheaf_fppf` restricts this condition along
the inclusion of the fppf topology into the fpqc topology. The final
definition packages that fppf sheaf condition without changing any values
or maps.

The intermediate results lie in `IntrinsicModuleHomDescent`. The implemented
argument has the following steps.

1. `mapComp'_hom` and `mapComp'_inv` identify the coherence maps of the
   actual module pullback pseudofunctor with the existing ordinary
   `compIso` comparisons. Accordingly, `toDescentData_obj_hom` identifies
   the transition of the canonical descent data with the composite of
   two such comparisons. `modCompat` reads the commutation equation of
   a morphism of descent data as compatibility of actual module maps.
2. `bijective_toDescentData_map_of_unique` turns unique gluing of those
   maps into bijectivity of the canonical map on descent morphisms.
   `bijective_toDescentData_map_openCover` obtains this unique gluing
   from the published `OpenCoverHomGluing.openCoverHomGluing`, after
   expressing its overlap equation through the same composition
   comparisons. Thus the pseudofunctor of all modules is a Zariski
   prestack; this step applies to arbitrary source and target modules.
3. For an affine, flat, surjective map,
   `bijective_toDescentData_map_singleton` applies the published
   `Modules.FaithfullyFlatHomDescent.existsUnique_hom`. The equation
   supplied by a morphism of canonical descent data is the required
   `PullbackHomCompatible` equation for every common source, expressed
   through `equalCompositeIso`. This step requires quasi-coherence only
   of the target.
4. `isSheafFor_singleton_over` converts that bijectivity into the
   singleton sheaf condition at every object `s : S ⟶ Y` of the full
   slice. It applies the previous step to `s* M` and `s* N`, using
   preservation of quasi-coherence under arbitrary ordinary pullback.
   Mathlib's `overMapCompPresheafHomIso` transfers the Hom presheaf
   along `s`, and its sheaf-condition comparison for `Over.map`
   transfers the covering family. This preserves every test scheme and
   every slice arrow.
5. `isSheaf_presheafHom_fpqc` combines Zariski descent with these
   affine faithfully flat singleton conditions through the published
   `Picard.isSheaf_fpqcTopology_over`. This is a theorem for a fixed
   pair with quasi-coherent target; it does not assert that the
   pseudofunctor of all modules is an fpqc prestack.
6. The relative theorem applies the explicit universe lift and then
   precomposes with `Over.pullback p`. Mathlib supplies continuity of
   that functor for the induced slice topologies, so this gives the
   stated sheaf on `Over B`. The bundled fppf sheaf uses the standard
   equivalence between the sheaf conditions for type-valued functors.

This is an internal derivation from the published intrinsic module Hom
construction, ordinary open-cover and faithfully flat Hom descent,
pullback preservation of quasi-coherence, and the existing site and
pseudofunctor comparisons. It introduces no external geometric premise.
It establishes the sheaf condition needed by local representation
gluing. Finite linear model existence and the affine finite-presentation
representation of proper coherent-family Hom remain separate results.
