# Adic completeness descends through actual surjections

This internal module reuses descent of precompleteness through surjective
linear maps to prove completeness for an actual surjective local-ring image of
a complete Noetherian local ring. It also retains the unchanged canonical
completion unit as a linear equivalence.

Let `R : Type u` be a commutative ring and `I` an ideal. Let `M : Type v`
and `N : Type w` be arbitrary `R`-modules with additive commutative group
structures. If `M` is `I`-adically precomplete and `f : M →ₗ[R] N` is
surjective, the published
`P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_surjective`
proves that `N` is precomplete. This module imports that existing result
from the attributed Anthropic FLT port.
No Noetherian, local, finite-generation or separatedness premise is needed
for this first result; the three universes are independent.

The reused proof uses the actual adic completion functor. Its existing
`map_surjective` theorem lifts every element of the completion of `N` to
the completion of `M`. Precompleteness lifts that element further to an
actual `m : M`. Naturality of the canonical completion map,
`AdicCompletion.map_of`, says that `f m` has the required completion image.
Thus the canonical map from `N` onto its completion is surjective, which
is exactly `AdicCompletion.of_surjective_iff`.

Now assume `R` is Noetherian and local, and complete for its actual maximal
ideal `m_R`. Let `S : Type v` be a commutative local ring and
`q : R →+* S` any actual surjective ring homomorphism.
`complete_of_surjective` proves completeness of `S` for its own maximal
ideal `m_S`. The proof equips `S` with the `R`-algebra structure specified
by `q`, so the actual map becomes a surjective `R`-linear map.
Surjectivity makes `S` a finite `R`-module. The first theorem supplies
`m_R`-adic precompleteness, and the existing Noetherian local finite-module
Hausdorff theorem supplies separatedness. These two properties give
`IsAdicComplete m_R S`. The existing scalar-extension comparison
`IsAdicComplete.map_algebraMap_iff` changes this to completeness for the
image of `m_R` in `S`. Finally
`IsLocalRing.map_maximalIdeal_of_surjective` identifies that actual image
with `m_S`. No new choice of ideal or topology is used.

`completionEquivOfSurjective` uses the same `R`-algebra structure and returns
an `R`-linear equivalence

```text
S ≃ₗ[R] AdicCompletion m_R S.
```

It derives the needed completeness from the preceding theorem and then
uses the existing `AdicCompletion.ofLinearEquiv`. Its forward map is
therefore the original canonical completion unit, with the existing
inverse for a complete module. The type explicitly retains the algebra
structure induced by `q`.

The provenance is internal: these are consequences of the actual
completion map's surjectivity, its naturality, the established Noetherian
local Hausdorff result and the image formula for maximal ideals. No
comparison with an unrelated inverse system of quotients is claimed.
