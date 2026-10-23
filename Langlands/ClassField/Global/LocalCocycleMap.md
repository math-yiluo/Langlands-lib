# Completed-local cocycle extensions and their maps to idele-class extensions

This module constructs continuous homomorphisms from normalized cocycle
extensions of actual completed-field automorphism groups by local units to
normalized relative idele-class extensions. Its inputs are actual cocycles and
an explicit compatibility cochain. It also derives existence of such a map
from the corresponding equality of second cohomology classes.

## Fields, actions and topologies

The number fields `F` and `E` lie in the same universe `Type u`, with an
`Algebra F E` structure. Let `v` and `w` be finite places of `F` and `E`,
with `w.asIdeal.LiesOver v.asIdeal`. The completed-field algebra is the published
scoped instance from `Langlands.Global.AdelicFunctoriality.FiniteExtension`.
Write `F_v = v.adicCompletion F`, `E_w = w.adicCompletion E`, and
`C_E = NumberField.IdeleClassGroup (𝓞 E) E`.

`CompletionGalois v w` is the actual group `E_w ≃ₐ[F_v] E_w`.
`completionGaloisTopology` gives it the discrete topology, installed locally
in this module. It can be installed elsewhere with
`letI := completionGaloisTopology v w`.
`completionGaloisDiscreteTopology` records discreteness. The units of `E_w`
retain their existing units topology and the actual action of algebra
automorphisms. `completionUnitsContinuousSMul` proves this action continuous:
for each automorphism use `continuous_localAut`, then continuity on units;
the acting group is discrete. No chosen action or coefficient topology is
accepted as a parameter.

## Local extensions

`CompletionUnitCocycle v w` abbreviates normalized multiplicative two-cocycles
for this automorphism action on `E_wˣ`. For such a cocycle `z`, its namespace
supplies `Extension z`, the published product-coordinate cocycle extension.
It consists of pairs `(a, σ)` with multiplication

`(a, σ) * (a', τ) = (a * σ(a') * z(σ, τ), σ * τ)`.

The group and topology are inherited from
`NormalizedTwoCocycle.Extension`. The topology is the product topology on
`E_wˣ × CompletionGalois v w`. `extensionIsTopologicalGroup` applies the
published generic construction: the action is continuous, and the cocycle is
continuous because its domain is discrete.

The names `inclusion`, `projection` and `sectionMap` denote the actual maps
`a ↦ (a, 1)`, `(a, σ) ↦ σ`, and `σ ↦ (1, σ)`. The module specializes the
published proofs of injectivity, surjectivity, equality of the inclusion's
range with the projection's kernel, continuity of both homomorphisms, and the
factor-set equation for the section. `toCocycle₂` views `z` as a cocycle in the
existing local `unitsRepresentation F_v E_w`; `cohomologyClass` is its image
under Mathlib's `H2π`. It is an arbitrary class, with no fundamental-class
selection.

## Compatibility and the constructed map

The namespace `LocalCocycleMap` additionally assumes `[Normal F E]`. This is
the hypothesis of the existing `decompositionHom v w`; no identification
with a decomposition subgroup is added here. Let `y` be a
`RelativeIdeleCocycle F E`, let `d = decompositionHom v w`, and let
`i_w = IdeleClassGroup.ofAdicCompletion (𝓞 E) E w`. The latter sends a local
unit to the class of the idele supported at `w`. The global group uses the
published discrete `relativeGaloisTopology`, and `C_E` uses its existing
quotient topology and the published arithmetic `relativeIdeleClassAction`.

For `b : CompletionGalois v w → C_E`, the proposition
`Compatible v w z y b` is exactly

`i_w(z(σ, τ)) * b(σ * τ) = b(σ) * ρ(d σ)(b(τ)) * y(d σ, d τ)`

for all `σ, τ`, where `ρ = relativeIdeleClassAut F E`.
`mapData` specializes `NormalizedTwoCocycle.MapData` with this cochain, the
coefficient map `i_w`, and the group map `d`. Its equivariance proof is the
published arithmetic theorem
`relativeIdeleClassAut_decompositionHom_ofAdicCompletion`.

`ExtensionHom v w z y` abbreviates continuous monoid homomorphisms between
the two actual extensions. Given `hb : Compatible v w z y b`,
`toExtension v w z y b hb` constructs such a homomorphism with formula

`(a, σ) ↦ (i_w(a) * b(σ), d σ)`.

Multiplicativity and normalization come from the generic `MapData`
construction. Continuity uses the published continuous `finiteClassInclusion`
and discreteness of the completed automorphism group, which makes both `d`
and `b` continuous. In particular, continuity of `b` is proved rather than
assumed.

The two coordinate formulas are `toExtension_left` and `toExtension_right`.
`toExtension_inclusion` says that the map restricts to `i_w` on coefficients;
`projection_toExtension` says it covers `d` on quotient groups.
`toExtension_sectionMap` sends the distinguished local section at `σ` to
the target inclusion of `b(σ)` times the target section at `d σ`.

## Cohomological criterion and provenance

`exists_compatible_iff` states

`(∃ b, Compatible v w z y b) ↔ localIdeleClassMap v w 2 [z] = decompositionRestriction v w 2 [y]`.

It is the published
`localIdeleClassMap_eq_decompositionRestriction_iff`, applied to `z.toCocycle₂`
and reversed. Thus it uses the existing local and global cohomology objects
and the existing maps, without a new cohomology theory.
`exists_toExtension` uses this equivalence to obtain `b`, constructs the
continuous map above, and proves its compatibility with inclusion and
projection. The class equality remains an explicit hypothesis.

This is internal derived material, specializing the published
`Langlands.GroupTheory.CocycleMap`,
`Langlands.ClassField.Global.CohomologyMaps`,
`Langlands.ClassField.Global.ClassExtension`, and
`Langlands.Global.Adelic`. The new content is their combination on actual
completed local units and idele classes, including the local topological
action and the resulting extension-map construction. All intrinsic proofs
reuse the generic coordinate identities or the proved arithmetic
equivariance and cohomology criterion described above.

The module does not select arithmetic fundamental classes, prove their
local-global compatibility, construct a canonical local or global Weil group,
or assert that the constructed map is injective or independent of the chosen
cochain. Those arithmetic and canonicity questions remain separate obligations.
