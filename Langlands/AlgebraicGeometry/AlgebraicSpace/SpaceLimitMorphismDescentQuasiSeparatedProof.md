# Morphisms of quasi-separated algebraic spaces along cofiltered limits: proof

Authors: Worker 208 (carried draft); revalidated against the current Library and
submitted by Worker 2057.

The theorem `spaceLimitMorphismDescentQuasiSeparated` proves exactly
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentQuasiSeparated`
from `SpaceLimitMorphismDescentQuasiSeparatedStatement`. It keeps the
statement's arbitrary universe and hypotheses:

- a cofiltered diagram `D` of affine schemes over an affine base `S`, with a
  limit cone `c`;
- a quasi-separated source space `X` with a quasi-compact atlas;
- a target space `Z` with a locally finitely presented atlas.

This is a proof-only module: it changes neither the statement nor anything the
statement imports.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), printed p.5 (Theorem 3.4(1)) and printed p.13, registered
as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. On p.13
Conrad states Theorem 3.4 for finitely presented algebraic spaces, which are
quasi-separated, and says it follows from the scheme case by étale descent.

The proof reuses the helpers and the shape of the separated proof
`spaceLimitMorphismDescent` (module `SpaceLimitMorphismDescentProof`, which
this module imports). That proof uses separatedness in one place only: the
affine equalizer scheme `E`, through which a pair of atlas points with the same
image factors exactly. In the quasi-separated case, `E` is replaced by an affine
étale cover of the overlap `U ×_X U`, through which such a pair factors only
after an étale surjective refinement of its domain. The gluing step absorbs the
refinement by injectivity of pullback along étale surjections.

## New helper result (namespace `SpaceLimitMorphisms`)

`exists_local_equalizer_scheme`. Let `a : h_U ⟶ X` be an affine atlas of a
quasi-separated space `X` over an affine base `S`. Then there are an affine
scheme `E` over `S` and two maps `r₁, r₂ : E ⟶ U` such that:

- every pair `f, f' : T ⟶ U` with the same atlas section admits an étale
  surjective `e : T' ⟶ T` and a map `r : T' ⟶ E` with `r ≫ r₁ = e ≫ f` and
  `r ≫ r₂ = e ≫ f'`;
- for every `r : T ⟶ E`, the atlas sections of `r ≫ r₁` and `r ≫ r₂` agree.

Proof. `U ×_S U` is affine. Since `X` is quasi-separated, the overlap
`selfPullback a` (the scheme `U ×_X U`) is quasi-compact, by the Library's
`EtaleChartFibreCount.compactSpace_selfPullback`. Then `exists_affine_refinement`
(from `SpaceFilteredRingPointProof`), applied to its identity, gives an affine
scheme `W` with an étale surjective `j : W ⟶ U ×_X U`. Take `E = W`, with `r₁`
and `r₂` equal to `j` followed by the two projections `selfFst a`,
`selfSnd a`. For the first property, the pair `(f, f')` lifts to
`selfLift a f f' : T ⟶ U ×_X U`, via `KernelPair.map_comp_eq_of_app_eq`. Its
pullback along `j` is the required `e`, and `r` is the second projection of
that pullback. The second property is the commutative square of
`selfPullback_isPullback a`.

## The main proof

Choose an affine atlas `a` of `X` (`exists_affine_qc_atlas`), the scheme `E`
with `r₁, r₂` of the helper, and a locally finitely presented atlas `aZ` of
`Z`.

1. **The value of `φ` on the atlas.** This step is the same as in the separated
   proof. The base changes `D_i ×_S U` have limit `c.pt ×_S U`. Let `x₀` be the
   universal base-changed atlas point over the limit and `z = φ(x₀)`. The
   helper `exists_stage` (namespace `SpaceFilteredPoints`, from
   `SpaceFilteredRingPointProof`) makes `z` the pullback of a section `y₀` of
   `Z` over some stage `D_{j₀} ×_S U`.
2. **Compatibility.** This step is also as in the separated proof. Over the
   limit, the two pullbacks of `y₀` along the maps `D_{j₀} ×_S E ⟶ D_{j₀} ×_S U`
   induced by `r₁, r₂` are the values of `φ` on the atlas sections of the two
   composites `c.pt ×_S E ⟶ E ⟶ U`. These agree by the second property of the
   helper. `SpaceFilteredPoints.exists_eq_of_limit`, on the diagram
   `D_i ×_S E` over `j₀`, makes the two pullbacks agree at a later stage `j`. Pulling `y₀` back
   to a section `y` over `D_j ×_S U` keeps them equal (`hcompat`).
3. **Gluing.** This is the step that changes. First, `hexact`: suppose two
   atlas points `w₁, w₂` of the base change of `X` to `D_j`, over some `T`,
   factor through `E` by a single map `r`, i.e. `r ≫ r₁` and `r ≫ r₂` are the
   second components of `w₁` and `w₂`. Then `w₁` and `w₂` factor through
   `D_j ×_S E` by the map `ν`, and the pullbacks of `y` along them agree by
   step 2. Now let `w₁, w₂` be any two atlas points with the same image. The
   first property of the helper gives an étale surjective `e : T' ⟶ T` and
   `r : T' ⟶ E` through which `e ≫ w₁` and `e ≫ w₂` factor. As a morphism
   `eT` over `D_j`, `e` is étale and surjective. By `hexact`, the pullbacks of
   `y` along `eT ≫ w₁` and `eT ≫ w₂` agree. Pullback along `eT` is injective
   (`SpaceFilteredPoints.pullback_injective`), so the
   pullbacks along `w₁` and `w₂` agree. `exists_hom_of_atlas` then gives `φj`
   from the base change of `X` to the base change of `Z` along `t.app j`. It
   sends each base-changed atlas point `w` to the pullback of `y` along `w`.
4. **Agreement over the limit.** This step is the same as in the separated
   proof and does not use separatedness. For `x` over `W`,
   `SpaceFilteredPoints.exists_atlas_lift` gives an étale surjective
   `e : W' ⟶ W` on which `x` is an atlas point `v`. After pullback along `e`, both sides are the pullback of `z` along `v`.
   Injectivity of pullback along `e` gives the equation.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Published dependencies

The module imports `SpaceLimitMorphismDescentQuasiSeparatedStatement`, the
unchanged target, and `SpaceLimitMorphismDescentProof`, which provides the
separated-case atlas and affine-limit helpers. The latter imports
`SpaceFilteredRingPointProof`, which provides `exists_affine_refinement`,
`exists_stage`, `exists_eq_of_limit`, `exists_atlas_lift` and
`pullback_injective`. It also imports `EtaleChartFibreCount` directly for
`compactSpace_selfPullback`. All these modules are in the published Library.
The new local equalizer helper is derived from these published results, as
described above.

## Scope

This proves only existence of a descended morphism for a quasi-separated
source. It does not prove uniqueness or eventual equality of descended
morphisms, descent of spaces (model existence), descent of properties, or any
arithmetic specialization.
