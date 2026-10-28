# Extension and restriction of scalars of smooth representations

Author: Worker 61. Built on
`Langlands.Cohomology.DivisibleSystem.ScalarExtension`
(`baseChangeRepresentation`, `restrictScalarsRepresentation`,
`restrictScalarsModule`, `repExtendScalars`, `repRestrictScalars`,
`repExtendScalarsUnit`, `repExtendScalarsCounit`,
`repExtendScalarsAdjunction`) and on the published smooth representations of
`Langlands.Representation.Smooth.Definitions` (`fixedVectors`,
`IsSmoothVector`, `IsSmooth`),
`Langlands.Representation.Smooth.SmoothPart.BasicProof`
(`isSmoothVector_add`) and `Langlands.Representation.Category.Basic`
(`smoothRepProperty`, `SmoothRep`, `SmoothRep.toRep`, `SmoothRep.hom`). From
Mathlib it uses `TensorProduct.inductionOn`, `RestrictScalars.addEquiv`,
`ObjectProperty.lift`, `ObjectProperty.homMk`, `ObjectProperty.hom_ext`,
`Adjunction.mkOfUnitCounit` and `Functor.mapHomologicalComplex`.

Everything is in the namespace `Langlands.Cohomology`. The published
`SmoothRep.{uR, uG, uV} R G` is the full subcategory of Mathlib's
`Rep.{uV} R G` on the representations all of whose vectors are fixed by some
open subgroup. This module shows that the extension and restriction of
scalars of the ScalarExtension module preserve this property, and restricts
the two functors and their adjunction to these full subcategories. All
underlying representations, maps, units and counits are those of the
ScalarExtension module; none is redefined.

## Smoothness

`R` and `S` are commutative rings (universes `uR`, `uS`) with an algebra
structure `algebraMap R S`, and `G` is a group. From the second item on, `G`
also has a topology; no compatibility of the topology with the group law is
assumed.

- `tmul_mem_fixedVectors_baseChangeRepresentation S ρ K s hv`: if the
  subgroup `K` fixes `v`, it fixes `s ⊗ v` in `baseChangeRepresentation S ρ`,
  where `g` acts by `s ⊗ v ↦ s ⊗ ρ g v`.
- `restrictScalarsRepresentation_fixed_iff R S σ K x`: every element of `K`
  fixes `x` in `restrictScalarsRepresentation R S σ` if and only if every
  element of `K` fixes the corresponding element
  `RestrictScalars.addEquiv R S W x` of `W` under `σ`. The statement is
  written with the action directly, not with `fixedVectors`, because instance
  search does not find the `Membership` instance for the submodule
  `fixedVectors` of `RestrictScalars R S W` formed with the module structure
  `restrictScalarsModule` of the ScalarExtension module. Membership in
  `fixedVectors ρ K` is by definition this condition for all `k : K`.
- `isSmooth_baseChangeRepresentation S hρ`: if `ρ` is smooth, so is
  `baseChangeRepresentation S ρ`. The proof is by induction on tensors: a
  pure tensor `s ⊗ v` is fixed by an open subgroup fixing `v` (previous
  item), and a sum of two smooth vectors is smooth (`isSmoothVector_add`:
  the smooth vectors form a submodule).
- `isSmooth_restrictScalarsRepresentation_iff R S σ`:
  `restrictScalarsRepresentation R S σ` is smooth if and only if `σ` is.
  Both directions use the same open subgroup, via
  `restrictScalarsRepresentation_fixed_iff`.

## The functors

From here on `G` is a group with a topology.

- `smoothRepExtendScalars R S G :
  SmoothRep.{uR, uG, w} R G ⥤ SmoothRep.{uS, uG, max uS w} S G`: the
  functor `SmoothRep.toRep ⋙ repExtendScalars R S G`, lifted to the full
  subcategory by `isSmooth_baseChangeRepresentation`
  (`ObjectProperty.lift`). On objects it is `V ↦ S ⊗[R] V` with `g` acting by
  `s ⊗ v ↦ s ⊗ g v`. On morphisms it is `f ↦ f.baseChange S`. The carrier
  `S ⊗[R] V` lies in universe `max uS w`.
- `smoothRepRestrictScalars R S G :
  SmoothRep.{uS, uG, w} S G ⥤ SmoothRep.{uR, uG, w} R G`: the functor
  `SmoothRep.toRep ⋙ repRestrictScalars R S G`, lifted by
  `isSmooth_restrictScalarsRepresentation_iff`. On objects it is
  `W ↦ RestrictScalars R S W`, with the action and the morphisms transported
  along `RestrictScalars.addEquiv`.
- `smoothRepExtendScalars_comp_toRep` and
  `smoothRepRestrictScalars_comp_toRep`: followed by the inclusion
  `SmoothRep.toRep` into `Rep`, the two functors are equal to
  `SmoothRep.toRep ⋙ repExtendScalars R S G` and
  `SmoothRep.toRep ⋙ repRestrictScalars R S G` (both by `rfl`).
  `smoothRepExtendScalarsToRepIso` and `smoothRepRestrictScalarsToRepIso`
  are the same identifications as natural isomorphisms with identity
  components.
- Explicit formulas, all by `rfl`:
  `smoothRepExtendScalars_obj_representation_tmul`
  (`g` sends `s ⊗ v` to `s ⊗ g v`), `smoothRepExtendScalars_map_tmul`
  (`f` sends `s ⊗ v` to `s ⊗ f v`),
  `smoothRepRestrictScalars_obj_representation_apply` and
  `smoothRepRestrictScalars_map_apply` (the action and the maps are those
  of `W` and `f`, transported along `RestrictScalars.addEquiv`).
- `smoothRepExtendScalars_additive`, `smoothRepRestrictScalars_additive`:
  both functors are additive. Morphisms of `SmoothRep` are morphisms of
  `Rep`, with the same addition, so this follows from the additivity of
  `repExtendScalars` and `repRestrictScalars`.

## Unit, counit and adjunction

The carrier universe is `max uS w` on both sides, as for
`repExtendScalarsAdjunction`, so that the composites of the two functors map
each category to itself.

- `smoothRepExtendScalarsUnit R S G`: the natural transformation from the
  identity of `SmoothRep.{uR, uG, max uS w} R G` to
  `smoothRepExtendScalars ⋙ smoothRepRestrictScalars`, whose component at
  `V` is the component `v ↦ 1 ⊗ v` of `repExtendScalarsUnit` at the
  underlying representation (`toRep_map_smoothRepExtendScalarsUnit_app`,
  `smoothRepExtendScalarsUnit_app_apply`).
- `smoothRepExtendScalarsCounit R S G`: the natural transformation from
  `smoothRepRestrictScalars ⋙ smoothRepExtendScalars` to the identity of
  `SmoothRep.{uS, uG, max uS w} S G`, whose component at `W` is the
  component `s ⊗ w ↦ s • w` of `repExtendScalarsCounit`
  (`toRep_map_smoothRepExtendScalarsCounit_app`,
  `smoothRepExtendScalarsCounit_app_tmul`).
  In both cases naturality is the naturality in `Rep`, since morphisms in the
  full subcategory are determined by their underlying morphisms.
- `smoothRepExtendScalarsAdjunction R S G`:
  `smoothRepExtendScalars ⊣ smoothRepRestrictScalars`, built from this unit
  and counit. Each triangle identity, on underlying morphisms, is the
  corresponding triangle identity of `repExtendScalarsAdjunction`.
  `smoothRepExtendScalarsAdjunction_unit` and
  `smoothRepExtendScalarsAdjunction_counit` record its unit and counit.
- `smoothRepExtendScalarsAdjunction_homEquiv_hom` and
  `smoothRepExtendScalarsAdjunction_homEquiv_symm_hom`: on underlying
  morphisms, the adjunction bijection
  `(S ⊗[R] V ⟶ W) ≃ (V ⟶ RestrictScalars R S W)` and its inverse are those
  of `repExtendScalarsAdjunction` (both by `rfl`).

## Complexes

`c` is a complex shape on an index type `ι`.

- `smoothRepExtendScalarsComplex R S G c` and
  `smoothRepRestrictScalarsComplex R S G c`: the two functors applied
  degreewise to complexes of smooth representations of shape `c`
  (`Functor.mapHomologicalComplex`, which uses additivity).
- `smoothRepExtendScalarsComplexUnit R S G c`: the natural chain map from a
  complex `K` in `SmoothRep.{uR, uG, max uS w} R G` to the restriction of
  scalars of its extension of scalars, with degree-`i` component the unit at
  `K.X i`, `v ↦ 1 ⊗ v`. It commutes with the differentials by naturality of
  the unit.

## Provenance and interpretation

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
printed p.92 (one-based PDF page 18), forms a complex of smooth
`Z_ℓ[S(e,d)]`-modules as an inverse limit and continues: "Tensoring with
Q_ℓ, we obtain our complex C(e,d)." Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999),
printed p.311 (one-based PDF page 13), works in "the category of smooth
L_ℓ[GJ]-modules" (Proposition 4.10). The two passages are quoted in full in
the ScalarExtension module's Markdown. The tensoring step there goes from
smooth modules over the coefficient integers to smooth modules over the
coefficient field. This module supplies that step for smooth
representations: extension of scalars `S ⊗[R] -` from smooth representations
over `R` to smooth representations over `S`, with restriction of scalars as
its right adjoint.

The smoothness results, the lifted functors, the unit, counit, adjunction
and their degreewise versions are ours. They are the standard facts that
extension and restriction of scalars of modules, with the group acting on
the second tensor factor or on the same additive group, preserve the
property that every vector is fixed by an open subgroup. The cited passages
do not state them separately. The ring map `R → S` is an arbitrary algebra of commutative rings;
the Harris case is `CoefficientIntegers l → FiniteCompletion L l`, the
algebra used in the ScalarExtension module, but this module does not
specialize to it.

## Scope

The module proves that extension and restriction of scalars preserve
smoothness, and defines the two functors on `SmoothRep`, their additivity,
the unit, counit and adjunction, the identifications with the `Rep`
constructions, and the degreewise functors on complexes with the degreewise
unit. It proves nothing about Ext groups or derived functors, injective
objects, flatness, exactness, inverse limits or cohomology. In particular it
does not show that extension of scalars commutes with Ext, with inverse
limits or with taking cohomology, and it does not compare these functors
with the smooth part of the ScalarExtension module or with Godement
resolutions.

Source registration: Harris 1997, `harris-1997-drinfeld-cohomology`,
SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`;
Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
