# Smooth locally constant coefficient systems

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem`: `ℓ`-divisible systems (Harris 1999,
  (2.1)), `hom_ext`, `mapFunctor C ℓ F` for additive functors preserving
  finite limits and colimits, and `SmoothSheafDivisibleSystem R G X ℓ`.
- `Langlands.Cohomology.DivisibleSystem.SpatialInduction` (Worker 61): `isoMk`
  and the equivalence `smoothRestrictionSystemEquivalence R H hH X ℓ` of
  `ℓ`-divisible systems of smooth sheaves on `G ×ᴴ X` and on `X`.
- `Langlands.Sheaf.Equivariant.LocallyConstantSmooth`: the full smooth locally
  constant sheaf functor `LocallyConstantSheaf.smoothFunctor R G X`. It sends
  a smooth representation `A` to the sheaf whose sections over an open `U` are
  all locally constant functions `U → A`.
- Worker 13's `Langlands.Sheaf.Equivariant.SmoothSpatialLocallyConstant`: the
  ambient functor `SpatialInduction.smoothLocallyConstantFunctor H hH X R` on
  `G ×ᴴ X` (`Space H X`) and the natural isomorphisms
  `smoothRestrictLocallyConstantNatIso` and `smoothInduceLocallyConstantNatIso`,
  with components `smoothRestrictLocallyConstantIso` and
  `smoothInduceLocallyConstantIso`.
- `Langlands.Representation.Induction.OpenAdjunction`: restriction
  `Induction.smoothRestriction R H` of smooth representations to a subgroup.
  `Langlands.Cohomology.SmoothExtBaseChangeSummand` supplies its additivity
  instance.
- `Langlands.Representation.Category.ExactInclusion`: `SmoothRep.toRep`
  preserves finite limits and finite colimits.
  `Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`: the inclusion
  `smoothInclusion R G X` of smooth sheaves into all equivariant sheaves
  preserves finite limits. Both are used below.

`R` is a commutative ring. `R`, the groups and the spaces lie in one universe
`u`, as in the Library's abelian structure on smooth sheaves.

## Locally constant functions

Namespace `Langlands.Sheaf.Equivariant.LocallyConstantSheaf`.

- `moduleFunctor R Y : ModuleCat R ⥤ ModuleCat R` sends `M` to the module of
  locally constant functions `Y → M` and acts by composition
  (`LocallyConstant.mapₗ`). `@[simps obj]` records the objects.
- `moduleFunctor_additive`: it is additive (`rfl`).
- `moduleFunctor_preservesFiniteLimits`: it preserves finite limits. Proof:
  by Mathlib's `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`
  it suffices that for every exact short complex `A → B → C` of modules with
  `A → B` injective, the image complex is exact and the image of `A → B` is
  injective. For exactness, let `s : Y → B` be locally constant with image 0
  in `C`. Each value `s y` then has a preimage in `A`. Define the lift by
  choosing a preimage of each value of `s` (`dite` with `Exists.choose`). The
  lift is `s` followed by a function `B → A`, so it is locally constant
  (`LocallyConstant.map`), and it maps to `s` pointwise. Injectivity is
  pointwise.

## Exactness of the smooth locally constant sheaf functor

Same namespace. `G` is a topological group and `X` a topological space with a
`G`-action by homeomorphisms and `HasStableNeighbourhoods G X`.

- `smoothFunctorSectionsIso R G X U`: after forgetting to presheaves
  (`smoothInclusion R G X ⋙ toTransportPresheaf G X (ModuleCat R)`) and
  evaluating at an open `U`, `smoothFunctor R G X` is naturally isomorphic to
  `SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R) ⋙ moduleFunctor R U`.
  All components are identities (`Iso.refl`).
- `smoothFunctor_preservesFiniteLimits`. Proof: each evaluation of the
  composite with the presheaf functor preserves finite limits by the
  isomorphism above, since `SmoothRep.toRep`, `forget₂` and `moduleFunctor`
  do. Hence the composite does (Mathlib's
  `preservesFiniteLimits_of_evaluation`), and the presheaf functor reflects
  finite limits (`preservesFiniteLimits_of_reflects_of_preserves`).
- `smoothFunctor_preservesEpimorphisms`. Proof: an epimorphism `f : A ⟶ B` of
  smooth representations is surjective (`SmoothRep.epi_iff_surjective`). Over
  each open, a locally constant `t : U → B` is the image of `t` followed by a
  set-theoretic section of `f` (`Function.surjInv`). So the presheaf map is
  an epimorphism (`NatTrans.epi_of_epi_app`). Both forgetful functors are
  faithful, so the map of smooth sheaves is an epimorphism
  (`Functor.epi_of_epi_map`).
- `smoothFunctor_additive`, `smoothFunctor_preservesHomology`,
  `smoothFunctor_preservesFiniteColimits`. The proofs use Mathlib:
  additivity from preservation of binary products
  (`Functor.additive_of_preserves_binary_products`), homology from
  preservation of epimorphisms and kernels
  (`Functor.preservesHomology_of_preservesEpis_and_kernels`), and finite
  colimits from homology (`Functor.preservesFiniteColimits_of_preservesHomology`).

## Exactness of restriction

Namespace `Langlands.Induction`. `H` is a subgroup of `G`.

- `smoothRestriction_preservesFiniteLimits` and
  `smoothRestriction_preservesFiniteColimits`. Proof:
  `smoothRestriction R H ⋙ SmoothRep.toRep` is, by definition,
  `SmoothRep.toRep ⋙ Rep.resFunctor H.subtype`, which preserves finite limits
  and colimits. `SmoothRep.toRep` reflects them.

## The ambient coefficient functor on `G ×ᴴ X`

Namespace `Langlands.Sheaf.Equivariant.SpatialInduction`. `H` is a subgroup of
`G` with `hH : IsOpen (H : Set G)`, and `X` has a continuous `H`-action and
`HasStableNeighbourhoods H X`.

- `smoothLocallyConstantFunctor_additive`,
  `smoothLocallyConstantFunctor_preservesFiniteLimits` and
  `smoothLocallyConstantFunctor_preservesFiniteColimits`. The functor
  `smoothLocallyConstantFunctor H hH X R` is defined as
  `LocallyConstantSheaf.smoothFunctor R G (Space H X)`, using the stable
  neighbourhoods `hasStableNeighbourhoods_induced H hH X`. The instances
  above transfer (`inferInstanceAs`).

## Natural isomorphisms of system functors

Namespace `Langlands.Cohomology.DivisibleSystem`. `C`, `D`, `E` are abelian
categories.

- `natIsoMk ℓ e he naturality : Φ ≅ Ψ` for functors
  `Φ Ψ : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ`. Its inputs are
  isomorphisms `e T : (Φ.obj T).tower ≅ (Ψ.obj T).tower` of the underlying
  inverse systems, commuting with the inclusions `i` (`he`) and natural in
  `T` (`naturality`). Components are `isoMk (e T) (he T)`.
  `natIsoMk_hom_app_tower` and `natIsoMk_inv_app_tower`: the tower of the
  component at `T` is `(e T).hom`, resp. `(e T).inv` (`rfl`).
- `mapFunctorCompIso ℓ F F' F'' α : mapFunctor C ℓ F ⋙ mapFunctor D ℓ F' ≅
  mapFunctor C ℓ F''` for exact additive functors and `α : F ⋙ F' ≅ F''`. It is
  `natIsoMk` with `e T` the whiskering of `α` by `T.tower`. Compatibility with
  `i` and naturality are naturality of `α`.
  `mapFunctorCompIso_hom_app_tower_app` and `_inv_`: the component at level
  `m` is `α.hom` (resp. `α.inv`) at `T m` (`rfl`).
- `mapFunctorComp ℓ F F'`: the case `α = Iso.refl`, identifying
  `mapFunctor C ℓ F ⋙ mapFunctor D ℓ F'` with `mapFunctor C ℓ (F ⋙ F')`.

## The coefficient system functors

Same namespace.

- `smoothLocallyConstantSystemFunctor R ℓ G X` is
  `mapFunctor _ ℓ (LocallyConstantSheaf.smoothFunctor R G X)`. It sends an
  `ℓ`-divisible system of smooth `G`-representations to an `ℓ`-divisible
  system of `G`-equivariant smooth sheaves on `X`. This uses the exactness
  instances above.
  `smoothLocallyConstantSystemFunctor_obj_tower`: the tower of the image of
  `T` is `T.tower ⋙ LocallyConstantSheaf.smoothFunctor R G X` (`rfl`).
- `smoothRestrictionSystemFunctor R ℓ H` is
  `mapFunctor _ ℓ (Induction.smoothRestriction R H)`, from systems of smooth
  `G`-representations to systems of smooth `H`-representations.
  `smoothRestrictionSystemFunctor_obj_tower`: the tower of the image is
  `T.tower ⋙ smoothRestriction R H` (`rfl`).

## Comparison under spatial induction

Same namespace and hypotheses as for the ambient coefficient functor. The
ambient category of systems of smooth sheaves on `G ×ᴴ X` uses
`hasStableNeighbourhoods_induced H hH X`. It is supplied by `letI` in the
statements, as in `smoothRestrictionSystemEquivalence`.

- `smoothRestrictLocallyConstantSystemIso R H hH X ℓ`:
  `smoothLocallyConstantSystemFunctor R ℓ G (Space H X) ⋙
  (smoothRestrictionSystemEquivalence R H hH X ℓ).functor ≅
  smoothRestrictionSystemFunctor R ℓ H ⋙ smoothLocallyConstantSystemFunctor R ℓ H X`.
  Restricting the locally constant system of `T` on `G ×ᴴ X` to the unit chart
  gives the locally constant system on `X` of the restriction of `T` to `H`.
  It is `natIsoMk` with `e T` the whiskering of
  `smoothRestrictLocallyConstantNatIso H hH X R` by `T.tower`.
  `smoothRestrictLocallyConstantSystemIso_hom_app_tower_app` and `_inv_`: the
  component at level `m` is
  `smoothRestrictLocallyConstantIso H hH X R (T m)` (`rfl`).
- `smoothInduceLocallyConstantSystemIso R H hH X ℓ`:
  `(smoothRestrictionSystemFunctor R ℓ H ⋙ smoothLocallyConstantSystemFunctor R ℓ H X) ⋙
  (smoothRestrictionSystemEquivalence R H hH X ℓ).inverse ≅
  smoothLocallyConstantSystemFunctor R ℓ G (Space H X)`.
  Smooth spatial induction of the locally constant system on `X` of the
  restricted system recovers the locally constant system on `G ×ᴴ X`. It is
  `natIsoMk` with `smoothInduceLocallyConstantNatIso H hH X R`.
  `smoothInduceLocallyConstantSystemIso_hom_app_tower_app` and `_inv_`: the
  component at level `m` is `smoothInduceLocallyConstantIso H hH X R (T m)`
  (`rfl`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.304 (one-based PDF
page 6). Worker 61 read the page in the rendered scan.

1. What Harris uses. Harris defines `ℓ`-divisible systems of
   `S(ẽ)`-modules over `U(ẽ)` by (2.1) and states: "Lemma 2.2. For each m
   the constant sheaf Z/ℓ^mZ admits an RΓ_c-acyclic resolution
   0 → Z/ℓ^mZ → F_m^0 → F_m^1 → ⋯ → F_m^q → ⋯ such that, for each q,
   {F_m^q} is an ℓ-divisible system of S(ẽ)-modules over U(ẽ)." The
   resolved object is the system of constant sheaves `ℤ/ℓ^mℤ`, a locally
   constant coefficient system.
2. What is formalized. The module is internal framework. Harris does not
   state the exactness results or the comparison isomorphisms. The functor
   `smoothLocallyConstantSystemFunctor` produces `ℓ`-divisible systems of
   smooth sheaves from `ℓ`-divisible systems of smooth coefficient
   representations. Harris's constant system corresponds to the trivial
   representations `ℤ/ℓ^mℤ`. That coefficient system is not constructed
   here. Reading `H` as `S(ẽ)`, `X` as `U(ẽ)` and `G` as `GJ` is our
   interpretation, as in the parent module `SpatialInduction`. Under it, the
   two comparison isomorphisms say that the locally constant system of a
   `GJ`-coefficient system on `GJ ×^{S(ẽ)} U(ẽ)` corresponds to the locally
   constant system on `U(ẽ)` of its restriction to `S(ẽ)`.
3. Exactness. The exactness of the locally constant sheaf functor and of
   restriction are standard facts. They are proved here because
   `DivisibleSystem.mapFunctor` needs them as instances.
4. Sites. As in the parent modules, the Library's sheaves are equivariant
   sheaves on topological spaces with ordinary opens, not étale sheaves on
   rigid analytic spaces.

## Scope

The module makes no statement about cohomology, compact sections or
resolutions of these systems. It does not construct the system of trivial
representations `ℤ/ℓ^mℤ`. It does not compare the induced space with a
subspace of a Drinfeld space.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
