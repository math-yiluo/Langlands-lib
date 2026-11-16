# Local exactness of free Čech augmentations

This internal construction extends the objectwise exactness result from
`ObjectwiseCechExactness` to every locally surjective presheaf arrow.
For a category `C : Type u` with morphisms in `Type v`, a Grothendieck
topology `J`, a commutative ring `R : Type w` and
`HasSheafify J (ModuleCat.{w} R)`, it proves

```lean
quasiIso_freeCechAugmentation_of_locally_surjective
    (f : Arrow (Cᵒᵖ ⥤ Type w)) [Presheaf.IsLocallySurjective J f.hom] :
    QuasiIso (freeCechAugmentation J R f)
```

The morphism here is the actual augmentation defined in `FreeNerve`,
from its alternating-face-map chain complex to the free sheaf generated
by the target presheaf, concentrated in degree zero. No products in `C`,
local-smallness assumption, points of the site or sheafification of
set-valued presheaves are required. All Čech limits used below belong
to the category of set-valued presheaves.

The range factorization is
`P → range(f) → Q`. Its first map is objectwise surjective; its second
map is objectwise injective and locally surjective. Two constructions
compare their augmented free sheaf nerves.

First, `cechPostMonoMap p m` is the square with identity on the source
and `m` on the target, from `p` to `p ≫ m`. In a category with finite
limits, if `m` is a monomorphism, `cechPostMonoTermIso p m n` identifies
the actual degree `n` Čech terms. Its forward map is precisely
`Arrow.mapCechNerve (cechPostMonoMap p m)` in that degree. Its inverse
keeps all projections to the source of `p`, and takes the base map
to be projection zero followed by `p`. Equality of the composites
with `m` implies the required equality of maps to the smaller base,
by cancellation of the monomorphism. The two inverse laws follow
from the wide-pullback projections and base map.
`isIso_mapCechNerve_postMono` uses these term isomorphisms to prove
that the actual simplicial map is an isomorphism. The use of
`Fin (n + 1)` supplies projection zero in every degree.

Second, `hom_ext_of_locally_surjective` says that two presheaf maps
`Q → Z`, with `Z` a sheaf, agree whenever their composites with a
locally surjective map `P → Q` agree. For each section of `Q`, its
image sieve is covering. Naturality and the assumed equality show
that the two images agree on this sieve; sheaf separatedness makes
them equal. Applying the free-sheaf adjunction gives
`epi_freeSheaf_map_of_locally_surjective`. The target module sheaf
is also a sheaf after forgetting to sets.
`mono_freeSheaf_map_of_injective` uses injectivity of `Finsupp.mapDomain`
to obtain a monomorphism of free module presheaves for an objectwise
injective map. Exact module sheafification preserves that monomorphism.
The abelian category of module sheaves then gives
`isIso_freeSheaf_map_of_injective_of_locally_surjective`.

`rangeArrowComparison f` is the actual arrow morphism from
`Subfunctor.toRange f.hom` to `f.hom`, with identity on the source
and the range inclusion on the target. For locally surjective `f`,
`freeRangeAugmentedCechIso J R f` compares the augmented free sheaf
nerves. Its unaugmented component comes from the Čech comparison
under a monomorphism, followed by the free sheaf functor. Its point
component is the isomorphism obtained by applying that functor to
the range inclusion. The augmented square is the image of
`Arrow.mapAugmentedCechNerve (rangeArrowComparison f)`.

`freeRangeAugmentationArrowIso J R f` applies the alternating-face-map
complex functor to the unaugmented component and the single-complex
functor to the point component. Naturality of Mathlib's actual
augmentation `AlternatingFaceMapComplex.ε` proves the required square
of chain complexes. Thus this is an isomorphism of the actual
augmentation arrows, including their target complexes.

Finally, `Subfunctor.toRange f.hom` is objectwise surjective, since
each element of its target carries a preimage witness. Its free sheaf
augmentation is a quasi-isomorphism by
`quasiIso_freeCechAugmentation_of_objectwise_surjective`.
Transport across `freeRangeAugmentationArrowIso` proves the displayed
local exactness theorem.

The provenance is internal: the presheaf range factorization,
the universal property of nonempty Čech wide pullbacks, separatedness
on covering image sieves, the free-sheaf adjunction and exact module
sheafification. The module establishes the local Čech exactness
ingredient. It does not construct finite analytic higher-nerve
presentations or prove restricted-injective coefficient acyclicity
or the analytic comparison theorem.
