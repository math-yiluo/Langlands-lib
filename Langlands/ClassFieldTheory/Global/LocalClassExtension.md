# Class-indexed completed-local extensions and maps to global extensions

This module realizes every class in the existing second cohomology of a
completed-field unit representation by an actual topological group extension.
It proves independence of the normalized representative up to continuous
multiplicative equivalence over both ends. Given equality of the local image
and restricted global class, it constructs a continuous homomorphism to the
published global class-indexed extension.

## Setting and local classes

The fields `F, E : Type u` are number fields with `[Algebra F E]`; `v` is a
finite place of `F`, `w` is a finite place of `E`, and
`[w.asIdeal.LiesOver v.asIdeal]`. Write `F_v = v.adicCompletion F` and
`E_w = w.adicCompletion E`. The completed algebra is the existing scoped
`AdelicFunctoriality.FiniteExtension` instance.

`CompletionH2 v w` is exactly the existing
`relativeCohomology (padicField v).Carrier E_w 2`. Its scalar ring is the
existing universe lift of the integers, and its coefficient representation is
the actual automorphism action on the additive notation for `E_wˣ`.
`CompletionUnitCocycle.cohomologyClass_surjective` specializes the generic
normalized-representative theorem to this representation. The representations
in the generic theorem and the local cohomology API are definitionally equal.

The local automorphism group is `CompletionGalois v w = E_w ≃ₐ[F_v] E_w`.
As in `LocalCocycleMap`, this module installs `completionGaloisTopology` as
a local instance, giving that group the discrete topology. Local units retain
their existing units topology; no arbitrary topology is introduced on the
coefficients. The module does not require normality or a Galois assumption for
the local extension construction.

## The extension of a class

For `x : CompletionH2 v w`,
`CompletionClassExtension.representative v w x` chooses a normalized cocycle
using the surjectivity theorem. `cohomologyClass_representative` proves its
class is `x`. This is a classical choice with no uniqueness claim.

`CompletionClassExtension v w x` is the actual
`CompletionUnitCocycle.Extension` of that representative. In particular, its
carrier consists of pairs `(a, σ)`, with the published cocycle multiplication
and product topology from `E_wˣ × CompletionGalois v w`. Its topological-group
instance is the already proved instance of that construction.

The namespace `CompletionClassExtension` supplies the actual coefficient
`inclusion`, quotient `projection`, and distinguished set-theoretic
`sectionMap`. Their formulas are respectively `a ↦ (a, 1)`,
`(a, σ) ↦ σ`, and `σ ↦ (1, σ)`. It proves:

- injectivity of inclusion, surjectivity of projection, and equality of the
  inclusion's range with the projection's kernel;
- continuity of inclusion, projection and section, with
  `continuousInclusion` and `continuousProjection` packaging the first two;
- `isOpenEmbedding_inclusion`, so the coefficient subgroup carries its actual
  topology and is open;
- `isOpenQuotientMap_projection`, so the specified discrete topology is the
  quotient topology;
- the factor-set formula for the section and the conjugation formula
  `t * inclusion(a) * t⁻¹ = inclusion(projection(t) • a)`, using the actual
  completed-field automorphism action.

The first, continuity, factor-set and conjugation results specialize the
generic cocycle-extension laws. The open quotient proof identifies projection
with the product's second projection using the published product
homeomorphism. For the open embedding, the same homeomorphism identifies
inclusion with `a ↦ (a, 1)`; its range is the inverse image of the open
singleton `{1}` under projection, by exactness.

## Independence of the representative

For any `z : CompletionUnitCocycle v w` with `hz : z.cohomologyClass = x`,
`equivOfRepresentative v w z hz` is a continuous multiplicative equivalence
from `CompletionUnitCocycle.Extension z` to `CompletionClassExtension v w x`.
It is the published `NormalizedTwoCocycle.continuousEquivOfCohomologyClassEq`,
applied to `hz` and the chosen representative's class identity. This theorem
chooses a relating cochain and uses identity maps on both end groups.

The four compatibility lemmas
`equivOfRepresentative_inclusion`, `projection_equivOfRepresentative`,
`equivOfRepresentative_symm_inclusion`, and
`projection_equivOfRepresentative_symm` show that this equivalence and its
inverse fix the unit subgroup and commute with projection. There is no claim
that the equivalence, cochain or section is canonical.

## A map to the global class extension

This section adds `[Normal F E]`, as required by the existing
`decompositionHom v w`. Let `y : relativeIdeleClassCohomology F E 2`.
The global target is exactly the published `ClassExtension y`; it uses the
actual idele class group `C_E`, its quotient topology and arithmetic action,
and the discrete `relativeGaloisTopology`. `GlobalHom v w x y` abbreviates
continuous homomorphisms between these two constructed extensions.

The explicit proposition `GlobalCompatible v w x y` is

`localIdeleClassMap v w 2 x = decompositionRestriction v w 2 y`.

Given a proof `h` of this proposition, `exists_globalCochain` applies
`LocalCocycleMap.exists_compatible_iff` to the two chosen representatives and
rewrites their classes to `x` and `y`. It obtains precisely the compatibility
cochain required by the existing construction. `globalCochain` chooses this
cochain; `globalCochain_spec` proves its equation.

`toGlobal v w x y h` is `LocalCocycleMap.toExtension` for these representatives
and this cochain. If `i_w : E_wˣ → C_E` is the actual local-unit idele-class
map and `d = decompositionHom v w`, its coordinates are

`(a, σ) ↦ (i_w(a) * globalCochain(h)(σ), d(σ))`.

`toGlobal_left` and `toGlobal_right` prove the coordinate formulas.
`toGlobal_inclusion` proves that the map restricts to `i_w` on coefficients;
`projection_toGlobal` proves it covers `d` on quotient groups.
`toGlobal_sectionMap` gives the target section multiplied by the inclusion of
the chosen cochain. Continuity and multiplicativity are inherited from the
explicitly constructed map of `LocalCocycleMap`.

## Provenance and scope

This is internal derived material. It specializes
`Langlands.GroupTheory.CocycleCohomology` and `CocycleClassEquiv` to the actual
local unit representation, following the existing global `ClassExtension`
construction. It reuses `LocalCocycleMap` for the local topological extension
and the cochain-induced map, and the existing `CohomologyMaps` criterion for
cochain existence. The proofs and topology arguments are described above;
no new external theorem is assumed.

These are extensions indexed by arbitrary actual cohomology classes. The
module does not select arithmetic fundamental classes or prove that they
satisfy `GlobalCompatible`. It also does not identify the local extension with
a genuine local Weil group, prove injectivity of `toGlobal`, establish
cochain-independent maps, or construct a coherent tower or inverse limit.
Those remain separate arithmetic and compatibility obligations.
