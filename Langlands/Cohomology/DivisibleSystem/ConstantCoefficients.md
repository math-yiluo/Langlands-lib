# Constant coefficient systems

Author: Worker 61. This module builds on the following published modules:

- `Langlands.Cohomology.DivisibleSystem`: `ℓ`-divisible systems (Harris 1999,
  (2.1)), multiplication `powSMul ℓ m X` by `ℓ ^ m`, the functor
  `mapFunctor C ℓ F` and its object map `DivisibleSystem.map`, and
  `SmoothSheafDivisibleSystem R G X ℓ`.
- `Langlands.Cohomology.DivisibleSystem.Reduction` (Worker 61): for an object
  `L` with `ℓ` a monomorphism on it, the system `reductionSystem ℓ L` of the
  cokernels `L / ℓ ^ m L` (`reductionTower ℓ L`), with projections
  `reductionπ ℓ L m : L ⟶ L / ℓ ^ m L`. Its maps `j` are induced by the
  identity of `L` (`reductionπ_map`); its maps `i` are the maps
  `reductionInclusion`, induced by multiplication by `ℓ ^ (m - m')`
  (`reductionπ_inclusion`).
- `Langlands.Cohomology.DivisibleSystem.ReductionAdic` (Worker 61):
  `powSMul_moduleCat_hom_apply`, `powSMul ℓ m` on a module is scalar
  multiplication by `(ℓ : R) ^ m`.
- `Langlands.Cohomology.DivisibleSystem.PermutationProjective` (Worker 61):
  the trivial smooth representation functor
  `smoothTrivialFunctor R G : ModuleCat R ⥤ SmoothRep R G` (Mathlib's
  `Rep.trivialFunctor R G` lifted to smooth representations) and the
  adjunction `smoothTrivialAdjunction R G` with the invariants functor.
- `Langlands.Cohomology.DivisibleSystem.StandardResolution` (Worker 61):
  `groupStandardResolutionSystem T`, the standard resolutions along
  `Ind_1^Γ Res_1^Γ` of the levels of a system `T` of representations of a
  finite group `Γ`.
- `Langlands.Cohomology.DivisibleSystem.Resolution` (Worker 61):
  `smoothGodementResolutionSystem h T` and
  `smoothGodementResolutionSystemObjIso`, the smooth Godement resolutions of
  the levels of a system `T` of smooth sheaves, given
  `h : SmoothGodementZeroExactStatement R G X` (Worker 3's hypothesis that the
  degree-zero smooth Godement functor is additive and exact).
- `Langlands.Cohomology.DivisibleSystem.SmoothLocallyConstant` (Worker 61):
  `smoothLocallyConstantSystemFunctor R ℓ G X`,
  `smoothRestrictionSystemFunctor R ℓ H`, `mapFunctorCompIso`, and the
  comparison isomorphisms `smoothRestrictLocallyConstantSystemIso` and
  `smoothInduceLocallyConstantSystemIso` under spatial induction.
  Through it, `LocallyConstantSheaf.smoothFunctor R G X`, which sends a smooth
  representation `A` to the sheaf whose sections over an open `U` are all
  locally constant functions `U → A` (Worker 13's
  `Langlands.Sheaf.Equivariant.LocallyConstant` and `LocallyConstantSmooth`).
- Mathlib: `Rep.trivialFunctor`, `Rep.invariantsAdjunction`,
  `Rep.coinvariantsAdjunction` (imported from
  `Mathlib.RepresentationTheory.Coinvariants`) and
  `Int.quotientSpanNatEquivZMod` (imported from
  `Mathlib.Data.ZMod.QuotientRing`).

`R` is a commutative ring. `R`, the groups and the spaces lie in one universe
`u`, as in the parent modules. The `ℤ` cases use `Type`.

## Non-zero-divisors

Namespace `Langlands.Cohomology`.

- `isSMulRegular_natCast hℓ`: in a domain of characteristic zero, a nonzero
  natural number `ℓ` is a non-zero-divisor (cancellation of `ℓ ≠ 0`). It
  applies to `ℤ`.
- `mono_powSMul_one_self R ℓ hℓ`: if `(ℓ : R)` is a non-zero-divisor, then
  multiplication by `ℓ` is a monomorphism on the `R`-module `R`. Proof:
  injectivity, with `powSMul_moduleCat_hom_apply`.

## Exactness of the trivial-action functors

Same namespace. `Γ` is a group, `G` a group with a topology.

- `repTrivialFunctor_preservesLimits` and
  `repTrivialFunctor_preservesColimits`: Mathlib's `Rep.trivialFunctor R Γ`
  is right adjoint to coinvariants (`Rep.coinvariantsAdjunction`) and left
  adjoint to invariants (`Rep.invariantsAdjunction`).
  `repTrivialFunctor_additive` follows
  (`Functor.additive_of_preserves_binary_products`).
- `smoothTrivialFunctor_preservesColimits`: `smoothTrivialFunctor R G` is a
  left adjoint (`smoothTrivialAdjunction`).
- `smoothTrivialFunctor_preservesFiniteLimits`: its composite with
  `SmoothRep.toRep` is, by definition, `Rep.trivialFunctor R G`, which
  preserves finite limits; `SmoothRep.toRep` is fully faithful, hence
  reflects them (`preservesFiniteLimits_of_reflects_of_preserves`).
- `smoothTrivialFunctor_additive` follows as above.

These instances let `DivisibleSystem.map` apply to the two functors.

## The scalar system

Namespace `Langlands.Cohomology.DivisibleSystem`. `ℓ` is a natural number and
`hℓ : IsSMulRegular R (ℓ : R)`.

- `range_powSMul_self R ℓ m`: the image of multiplication by `ℓ ^ m` on `R` is
  the ideal `Ideal.span {(ℓ : R) ^ m}`.
- `scalarSystem R ℓ hℓ : DivisibleSystem (ModuleCat R) ℓ` is
  `reductionSystem ℓ (ModuleCat.of R R)`, using `mono_powSMul_one_self`.
  `scalarSystem_tower` and `scalarSystem_inclusion` record its tower and its
  maps `i` (`rfl`).
- `scalarπ hℓ m : R ⟶ (scalarSystem R ℓ hℓ).obj m` is `reductionπ`, typed into
  the level of the system. It is an epimorphism. `scalarπ_projection`: the
  maps `j` commute with it. `scalarπ_inclusion`: `i` sends the class of `r` to
  the class of `ℓ ^ (m - m') r`.
- `scalarSystemObjIso hℓ m : (scalarSystem R ℓ hℓ).obj m ≅
  ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})` is Mathlib's
  `ModuleCat.cokernelIsoRangeQuotient` followed by `Submodule.quotEquivOfEq`
  along `range_powSMul_self`. `scalarπ_scalarSystemObjIso_hom`: it sends the
  class of `r` to the class of `r`.
- `span_pow_le_span_pow` and `span_pow_le_comap_mulLeft`: for `m' ≤ m`,
  `(ℓ ^ m) ≤ (ℓ ^ m')`, and multiplication by `ℓ ^ (m - m')` maps `(ℓ ^ m')`
  into `(ℓ ^ m)`.
- `projection_scalarSystemObjIso_hom`: under `scalarSystemObjIso`, `j` for
  `m' ≤ m` is the reduction `R ⧸ (ℓ ^ m) ⟶ R ⧸ (ℓ ^ m')`
  (`Submodule.factor`).
- `inclusion_scalarSystemObjIso_hom`: under `scalarSystemObjIso`, `i` for
  `m' < m` is multiplication by `ℓ ^ (m - m')`,
  `R ⧸ (ℓ ^ m') ⟶ R ⧸ (ℓ ^ m)` (`Submodule.mapQ` of `LinearMap.mulLeft`).
  Both proofs cancel the epimorphism `scalarπ` and compare elements.

## The integer system

Same namespace. `hℓ : ℓ ≠ 0`.

- `intSystem ℓ hℓ : DivisibleSystem (ModuleCat ℤ) ℓ` is
  `scalarSystem ℤ ℓ (isSMulRegular_natCast hℓ)` (an `abbrev`).
- `intSystemObjIso ℓ hℓ m : (intSystem ℓ hℓ).obj m ≅
  ModuleCat.of ℤ (ZMod (ℓ ^ m))` is `scalarSystemObjIso` followed by
  `Ideal.quotEquivOfEq` (the ideals `((ℓ : ℤ) ^ m)` and `((ℓ ^ m : ℕ) : ℤ)`
  agree) and Mathlib's ring isomorphism `Int.quotientSpanNatEquivZMod (ℓ ^ m)`,
  as an isomorphism of `ℤ`-modules.
- `scalarπ_intSystemObjIso_hom`: the composite from `ℤ` is the cast
  `ℤ → ZMod (ℓ ^ m)`.

So level `m` of `intSystem ℓ hℓ` is `ℤ/ℓ^mℤ`, `j` is reduction and `i` is
multiplication by `ℓ ^ (m - m')`.

## Trivial representations

Same namespace. `Γ` is a group.

- `trivialRepSystem hℓ Γ : DivisibleSystem (Rep R Γ) ℓ` is the image of
  `scalarSystem R ℓ hℓ` under `Rep.trivialFunctor R Γ` (`DivisibleSystem.map`).
- `trivialRepSystemObjIso hℓ Γ m`: level `m` is
  `Rep.trivial R Γ (R ⧸ Ideal.span {(ℓ : R) ^ m})`, the image of
  `scalarSystemObjIso`.
- `trivialStandardResolutionSystem hℓ Γ`, for finite `Γ`, is
  `groupStandardResolutionSystem (trivialRepSystem hℓ Γ)` (an `abbrev`): the
  standard resolutions along `Ind_1^Γ Res_1^Γ` of the trivial
  representations `R / ℓ ^ m R`, as one `ℓ`-divisible system of chain
  complexes. The published theorem
  `quasiIso_groupStandardResolutionSystemAugmentation` applies to it, so each
  level is a resolution.

## Trivial smooth representations

Same namespace. `G` is a group with a topology.

- `smoothTrivialSystem hℓ G : DivisibleSystem (SmoothRep R G) ℓ` is the image
  of `scalarSystem R ℓ hℓ` under `smoothTrivialFunctor R G`.
- `smoothTrivialSystemObjIso hℓ G m`: level `m` is
  `(smoothTrivialFunctor R G).obj (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))`.

From here on `G` is a topological group and `H` a subgroup.

- `smoothTrivialRestrictionIso R H : smoothTrivialFunctor R G ⋙
  Induction.smoothRestriction R H ≅ smoothTrivialFunctor R H`: the
  restriction to `H` of a trivial smooth representation is the trivial smooth
  representation of `H`. The components are identities.
- `smoothTrivialSystemRestrictionIso hℓ H :
  (smoothRestrictionSystemFunctor R ℓ H).obj (smoothTrivialSystem hℓ G) ≅
  smoothTrivialSystem hℓ H` is the component at `scalarSystem R ℓ hℓ` of
  `mapFunctorCompIso` for `smoothTrivialRestrictionIso`.

## The constant sheaf system

Namespace `Langlands.Cohomology.DivisibleSystem`, opening
`Langlands.Sheaf.Equivariant`. `X` is a topological space with a `G`-action
by homeomorphisms and `HasStableNeighbourhoods G X`.

- `constantSheafSystem hℓ G X : SmoothSheafDivisibleSystem R G X ℓ` is
  `(smoothLocallyConstantSystemFunctor R ℓ G X).obj (smoothTrivialSystem hℓ G)`.
- `constantSheafSystemObjIso hℓ G X m`: level `m` is the locally constant
  sheaf `(LocallyConstantSheaf.smoothFunctor R G X).obj` of the trivial
  smooth representation `R / ℓ ^ m R`.

Its sections over an open `U` are the locally constant functions
`U → R / ℓ ^ m R`, so it is the constant sheaf `R / ℓ ^ m R` on `X`. In the
published sheaf `LocallyConstantSheaf.sheaf`, the pullback along an arrow
labelled `g ∈ G` precomposes with the point map of `g` and applies the
inverse coefficient operator of `g`. For trivial coefficients that operator
is the identity, so `G` acts through its action on `X` only.

- `constantGodementResolutionSystem hℓ G X h`, for
  `h : SmoothGodementZeroExactStatement R G X`, is
  `smoothGodementResolutionSystem h (constantSheafSystem hℓ G X)` (an
  `abbrev`).
- `constantGodementResolutionSystemObjIso hℓ G X h m`: level `m` is the
  smooth Godement complex `smoothComplex R G X` of the locally constant
  sheaf of the trivial representation `R / ℓ ^ m R`. It is
  `smoothGodementResolutionSystemObjIso` followed by
  `smoothComplexFunctor R G X` applied to `constantSheafSystemObjIso`.

## Spatial induction

Same namespace. `H` is a subgroup of `G` with `hH : IsOpen (H : Set G)`, and
`X` has a continuous `H`-action and `HasStableNeighbourhoods H X`. As in the
parent module, the stable neighbourhoods on `G ×ᴴ X` (`Space H X`) are
`hasStableNeighbourhoods_induced H hH X`, supplied by `letI`.

- `constantSheafSystemRestrictIso hℓ H hH X`: restricting
  `constantSheafSystem hℓ G (Space H X)` to the unit chart along
  `smoothRestrictionSystemEquivalence R H hH X ℓ` gives
  `constantSheafSystem hℓ H X`. It is the component of
  `smoothRestrictLocallyConstantSystemIso` at `smoothTrivialSystem hℓ G`,
  followed by the image of `smoothTrivialSystemRestrictionIso`.
- `constantSheafSystemInduceIso hℓ H hH X`: the inverse of the equivalence
  sends `constantSheafSystem hℓ H X` to `constantSheafSystem hℓ G (Space H X)`.
  It is the image of the inverse of `smoothTrivialSystemRestrictionIso`,
  followed by the component of `smoothInduceLocallyConstantSystemIso`.

## Integer coefficients

Same namespace; `Γ`, `G` and `X` lie in `Type`, and `hℓ : ℓ ≠ 0`.

- `intTrivialRepSystem ℓ hℓ Γ` is `trivialRepSystem` for `R = ℤ` (an
  `abbrev`). `intTrivialRepSystemObjIso ℓ hℓ Γ m`: level `m` is
  `Rep.trivial ℤ Γ (ZMod (ℓ ^ m))`.
- `intConstantSheafSystem ℓ hℓ G X` is `constantSheafSystem` for `R = ℤ` (an
  `abbrev`). `intConstantSheafSystemObjIso ℓ hℓ G X m`: level `m` is the
  locally constant sheaf of the trivial smooth representation `ZMod (ℓ ^ m)`.
  Both isomorphisms are images of `intSystemObjIso`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.304 (one-based PDF
page 6). Worker 61 read the page in the rendered scan.

1. What Harris uses. After defining `ℓ`-divisible systems by (2.1), Harris
   states: "Lemma 2.2. For each m the constant sheaf Z/ℓ^mZ admits an
   RΓ_c-acyclic resolution 0 → Z/ℓ^mZ → F_m^0 → F_m^1 → ⋯ → F_m^q → ⋯ such
   that, for each q, {F_m^q} is an ℓ-divisible system of S(ẽ)-modules over
   U(ẽ)." The lemma resolves the constant sheaves `ℤ/ℓ^mℤ`, for all `m`, by
   `ℓ`-divisible systems.
2. What is formalized. `intConstantSheafSystem ℓ hℓ G X` is the family of
   constant sheaves `ℤ/ℓ^mℤ` on an ordinary `G`-space, as an `ℓ`-divisible
   system. Its maps `i` are multiplication by `ℓ ^ (m - m')` and its maps `j`
   are the reductions (`intSystemObjIso`, `inclusion_scalarSystemObjIso_hom`,
   `projection_scalarSystemObjIso_hom`). The quoted lemma does not name
   these maps; this choice is ours, and the published `reductionSystem`
   proves that it satisfies (2.1).
   Reading `G` as `S(ẽ)` and `X` as `U(ẽ)` is our interpretation, as in the
   parent modules. The general `R` with `ℓ` a non-zero-divisor, the
   trivial-representation systems and the spatial comparisons are internal
   framework.
3. Resolutions. `constantGodementResolutionSystem` is the resolution system of
   the published module `Resolution` applied to the constant system; that
   module states that Lemma 2.2 is its case of the constant sheaves, which it
   does not construct. The exactness of the degree-zero smooth Godement
   functor (Harris's Fact 3 in this setting) stays the hypothesis
   `SmoothGodementZeroExactStatement R G X`. The `RΓ_c`-acyclicity of the
   terms is not proved here. `trivialStandardResolutionSystem` is not from
   Harris: it is the published group standard resolution applied to the
   trivial representations, provided as an adapter.
4. Sites. As in the parent modules, the Library's sheaves are equivariant
   sheaves on topological spaces with ordinary opens, not étale sheaves on
   rigid analytic spaces.

## Scope

The module makes no statement about cohomology or acyclicity of these systems
or their resolutions, and proves no exactness of the smooth Godement
functors. It does not construct `ℓ`-adic or `ℤ_ℓ`-coefficient limits.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
