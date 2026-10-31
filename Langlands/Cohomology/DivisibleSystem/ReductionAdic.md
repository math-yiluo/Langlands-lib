# Reductions as ideal-adic quotients and as tensor products

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.Reduction` (`reductionTower`,
`reductionπ`, `reductionπ_map`, `reductionTowerMap` with
`reductionTowerMap_app`, `reductionπ_reductionTowerMap_app`,
`reductionTowerMap_id`, `reductionTowerMap_comp`, and `reductionπ_reductionMap`)
and `Langlands.Coefficients.AdicTensorComparison` (Worker 13:
`tensorPower`, `tensorPowerIso`, `tensorPowerIso_unit`, `tensorFunctor`,
`tensorFunctorIso`). Through their imports it uses `powSMul` and
`map_powSMul` (`Langlands.Cohomology.DivisibleSystem`) and, from Worker 13's
`Langlands.Coefficients.AdicSystem`, `powerReduction`, `quotientMap`,
`transition`, `quotientMap_transition`, `system` and `functor`. From Mathlib
it uses `PreservesCokernel.iso` with `PreservesCokernel.π_iso_hom`,
`cokernelIsoOfEq` with `π_comp_cokernelIsoOfEq_hom`,
`ModuleCat.cokernelIsoRangeQuotient` with
`ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply`,
`Submodule.quotEquivOfEq`, `LinearEquiv.toModuleIso`,
`ModuleCat.hom_nsmul`, `Nat.cast_smul_eq_nsmul`, `Ideal.span_singleton_pow`,
`Submodule.ideal_span_singleton_smul`,
`Submodule.mem_smul_pointwise_iff_exists`,
`ModuleCat.extendRestrictScalarsAdj`, `NatIso.ofComponents`,
`Functor.whiskeringRight`, the forgetful functor `forget₂ (Rep R G)
(ModuleCat R)`, `Rep.epi_iff_surjective` and `Rep.hom_comm_apply`.

## Conventions

`ℓ` and `m` are natural numbers. `powSMul ℓ m X` is the published
endomorphism "multiplication by `ℓ ^ m`" of an object `X` of a preadditive
category. The published `reductionTower ℓ L : ℕᵒᵖ ⥤ C`, for `L` in an abelian
category `C`, is the inverse system whose level `m` is
`cokernel (powSMul ℓ m L)`, written `L / ℓ ^ m L`, with transition maps the
projections `L / ℓ ^ m L ⟶ L / ℓ ^ n L` for `n ≤ m`;
`reductionπ ℓ L m : L ⟶ L / ℓ ^ m L` is the cokernel projection, and
`reductionTowerMap ℓ f` is the map of towers induced by `f : L ⟶ L'`.

For a commutative ring `R`, an ideal `I` and an `R`-module `M`, Worker 13's
published `AdicSystem` has the functor `powerReduction I m`, sending `M` to
the quotient `M / I ^ m M` (the quotient by the submodule `I ^ m • ⊤`) as an
`R`-module, the quotient maps `quotientMap I m : M ⟶ M / I ^ m M`, the
transitions `transition I h : M / I ^ n M ⟶ M / I ^ m M` for `h : m ≤ n`,
the inverse system `system I M : ℕᵒᵖ ⥤ ModuleCat R` of these quotients and
`functor I : M ↦ system I M`. The published `AdicTensorComparison` has
`tensorPower I m`, the functor `M ↦ (R / I ^ m) ⊗_R M` (extension of scalars
along `R → R / I ^ m` followed by restriction back to `R`), the natural
isomorphism `tensorPowerIso I m : tensorPower I m ≅ powerReduction I m`,
whose composite with the unit of the extension-restriction adjunction is
`quotientMap I m` (`tensorPowerIso_unit`), and the tensor system
`tensorFunctor I : M ↦ {(R / I ^ m) ⊗_R M}_m` with
`tensorFunctorIso I : tensorFunctor I ≅ functor I`. Here always
`I = (ℓ) = Ideal.span {(ℓ : R)}`; since `(ℓ) ^ m = (ℓ ^ m)`, the ring
`R / (ℓ) ^ m` is `R / ℓ ^ m R`.

## The tower as a functor (namespace `Langlands.Cohomology.DivisibleSystem`)

- `reductionTowerFunctor ℓ : C ⥤ (ℕᵒᵖ ⥤ C)` sends `L` to `reductionTower ℓ L`
  and `f` to `reductionTowerMap ℓ f`; the functor laws are
  `reductionTowerMap_id` and `reductionTowerMap_comp`.

## Transport along functors preserving cokernels

`C` and `D` are abelian categories and `F : C ⥤ D` is an additive functor
that preserves colimits indexed by `WalkingParallelPair` (in particular
cokernels).

- `reductionCompIso ℓ F L m : F (L / ℓ ^ m L) ≅ F L / ℓ ^ m F L` is the
  comparison `PreservesCokernel.iso F (powSMul ℓ m L)` of `F` applied to the
  cokernel with the cokernel of `F.map (powSMul ℓ m L)`, followed by
  `cokernelIsoOfEq` along `F.map (powSMul ℓ m L) = powSMul ℓ m (F L)`
  (`map_powSMul`).
- `map_reductionπ_reductionCompIso_hom` and
  `reductionπ_reductionCompIso_inv`: the comparison carries
  `F.map (reductionπ ℓ L m)` to `reductionπ ℓ (F L) m`, and its inverse
  carries `reductionπ ℓ (F L) m` back to `F.map (reductionπ ℓ L m)`.
- `reductionTowerCompIso ℓ F L : reductionTower ℓ L ⋙ F ≅ reductionTower ℓ (F L)`
  has components `reductionCompIso` (`reductionTowerCompIso_hom_app`).
  Naturality in `m` is checked after cancelling the epimorphism
  `reductionπ ℓ (F L) m` and the inverse comparison: both sides reduce to
  `F.map` of the composite of `reductionπ ℓ L m` with a transition map, by
  `reductionπ_map` in `C` and in `D`.
- `reductionCompIso_hom_naturality`: the comparison is natural in `L`, by the
  same cancellation and `reductionπ_reductionTowerMap_app`.
- `reductionTowerFunctorCompIso ℓ F` is the natural isomorphism
  `reductionTowerFunctor ℓ ⋙ (composition with F) ≅ F ⋙ reductionTowerFunctor ℓ`
  with components `reductionTowerCompIso ℓ F L`.

## Modules: the tower is the published `(ℓ)`-adic system

`R : Type u` is a commutative ring and `L` is in `ModuleCat.{v} R`.

- `powSMul_moduleCat_hom_apply`: `powSMul ℓ m L` sends `x` to
  `(ℓ : R) ^ m • x`. `powSMul` is the `ℓ ^ m`-fold sum of the identity, and a
  natural-number multiple agrees with the scalar multiple by its image in `R`
  (`ModuleCat.hom_nsmul`, `Nat.cast_smul_eq_nsmul`).
- `range_powSMul`: the range of `powSMul ℓ m L` is the submodule
  `(ℓ) ^ m • ⊤` of `L`, because `(ℓ) ^ m • ⊤` is the set of multiples
  `ℓ ^ m • y` (`Ideal.span_singleton_pow`,
  `Submodule.ideal_span_singleton_smul`,
  `Submodule.mem_smul_pointwise_iff_exists`).
- `reductionAdicIso ℓ L m : L / ℓ ^ m L ≅ powerReduction (ℓ) m L` is
  Mathlib's identification of the cokernel in `ModuleCat` with the quotient
  by the range (`ModuleCat.cokernelIsoRangeQuotient`), followed by the
  equality of submodules `range_powSMul` (`Submodule.quotEquivOfEq`).
- `reductionπ_reductionAdicIso_hom`: composed with `reductionπ ℓ L m` it is
  `quotientMap (ℓ) m`, that is, it sends the class of `x` to the class of `x`
  (`ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply`).
- `reductionAdicIso_hom_transition`: the comparisons commute with the
  transition maps of the two towers. After cancelling the epimorphism
  `reductionπ ℓ L n`, both sides are `quotientMap (ℓ) m`, by
  `reductionπ_map` and the published `quotientMap_transition`.
- `reductionTowerAdicIso ℓ L : reductionTower ℓ L ≅ system (ℓ) L`, with
  components `reductionAdicIso` (`reductionTowerAdicIso_hom_app`).
- `reductionAdicIso_hom_naturality`: `reductionAdicIso` is natural in `L`;
  after cancelling `reductionπ ℓ L m` this is the naturality of
  `quotientMap (ℓ) m`.
- `reductionTowerFunctorAdicIso ℓ R : reductionTowerFunctor ℓ ≅ functor (ℓ)`,
  the functor `L ↦ {L / ℓ ^ m L}` is the published `AdicSystem.functor (ℓ)`
  (components `reductionTowerFunctorAdicIso_hom_app_app`).

## Modules: the tensor presentation

Here the carriers lie in `Type u`, the universe of `R`, as in the published
`AdicTensorComparison`.

- `reductionTowerFunctorTensorIso ℓ R : reductionTowerFunctor ℓ ≅ tensorFunctor (ℓ)`
  is `reductionTowerFunctorAdicIso` followed by the inverse of the published
  `tensorFunctorIso (ℓ)`: the functor `L ↦ {L / ℓ ^ m L}` is
  `L ↦ {(R / (ℓ) ^ m) ⊗_R L}`, the levels viewed as `R`-modules, naturally
  in `L` and compatibly with the transition maps.
- `reductionTensorIso ℓ L m : L / ℓ ^ m L ≅ (R / (ℓ) ^ m) ⊗_R L` is its
  component at `L` and `m`.
- `reductionπ_reductionTensorIso_hom`: composed with `reductionπ ℓ L m`,
  `reductionTensorIso` is the unit of the adjunction between extension and
  restriction of scalars along `R → R / (ℓ) ^ m`, the map `x ↦ 1 ⊗ x`. The
  proof composes both sides with the isomorphism
  `tensorPowerIso (ℓ) m` at `L`: the right side becomes `quotientMap (ℓ) m` by
  the published `tensorPowerIso_unit`, and the left side becomes
  `reductionπ ℓ L m ≫ (reductionAdicIso ℓ L m).hom`, which is
  `quotientMap (ℓ) m` by `reductionπ_reductionAdicIso_hom`.

## Representations

`R : Type u` is a commutative ring, `G : Type v` a monoid and `X` is in
`Rep.{w} R G`; `forget₂ (Rep R G) (ModuleCat R)` sends `X` to its underlying
`R`-module. It is additive and preserves colimits.

- `reductionTowerForgetAdicIso ℓ X` is the isomorphism of inverse systems of
  `R`-modules between the underlying modules of the tower
  `{X / ℓ ^ m X}` of representations and the published quotient system
  `system (ℓ)` of the underlying module of `X`: `reductionTowerCompIso` for
  the forgetful functor, followed by `reductionTowerAdicIso`.
- `map_reductionπ_reductionTowerForgetAdicIso_hom` and
  `reductionTowerForgetAdicIso_hom_reductionπ`: it sends the class of `x` in
  `X / ℓ ^ m X` to the class of `x` in `X / (ℓ) ^ m X`.
- `reductionTowerForgetAdicIso_hom_ρ`: it carries the action of `g ∈ G` on the
  representation `X / ℓ ^ m X` to the map `powerReduction (ℓ) m (ρ(g))`
  induced on `X / (ℓ) ^ m X` by the action of `g` on `X`. Every element of
  `X / ℓ ^ m X` is a class `reductionπ ℓ X m x` (`reductionπ` is an
  epimorphism, hence surjective by `Rep.epi_iff_surjective`); `reductionπ`
  commutes with the actions (`Rep.hom_comm_apply`), and both sides are the
  class of `g • x`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §4, printed p.311 (one-based PDF page 13): "Now we want to let `m` vary.
  Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
  `𝒪`-modules".
- §3, printed p.308 (one-based PDF page 10): the coefficients at level `m`
  are `𝒪/ℓ^m𝒪`: "`D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)`" and "Let `𝓛` be a free
  `𝒪/ℓ^m𝒪`-module of finite order".
- §3, printed p.306 (one-based PDF page 8): "`L_v = L ⊗_ℚ ℚ_v`" for a place
  `v` of `ℚ`; printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring
  of integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in
  `W(L)`." Thus `L_ℓ = L ⊗_ℚ ℚ_ℓ` is in general a finite product of finite
  extensions of `ℚ_ℓ`, and `𝒪` is a commutative ring; nothing below uses
  more than that.

We read `𝒪_m` on p.311 as `𝒪/ℓ^m𝒪`, the coefficient ring of p.308. The
published `Reduction` module models `𝓛_m` by the cokernel `L / ℓ ^ m L` of
multiplication by `ℓ ^ m` and records the identification
`𝓛 ⊗_𝒪 𝒪/ℓ^m𝒪 ≅ 𝓛/ℓ^m𝓛` as not formalized there. This module formalizes it,
with `R` for `𝒪` and an arbitrary `R`-module `L` for `𝓛`:
`reductionTensorIso ℓ L m : L / ℓ ^ m L ≅ (R / (ℓ) ^ m) ⊗_R L`, natural in
`L`, compatible with the transition maps, and sending the class of `x` to
`1 ⊗ x`. It holds for every module, so the lattice hypotheses of Harris are
not needed. For a representation it identifies the underlying modules and
transports the action. The comparisons are assembled from the published
results of Worker 13 and Mathlib's description of cokernels of modules; the
statements, their naturality and compatibility, and the transport along
functors preserving cokernels are ours. The module is derived.

## Scope

The tensor comparison is an isomorphism of `R`-modules: the levels
`(R / (ℓ) ^ m) ⊗_R L` are viewed as `R`-modules, as in the published
`tensorPower`, not as `R / (ℓ) ^ m`-modules, and the carriers must lie in
the universe of `R`. For representations only the underlying `R`-modules
are compared; the action is transported by
`reductionTowerForgetAdicIso_hom_ρ`, but no isomorphism of inverse systems
of representations, nor a comparison with Worker 13's
`AdicSystem.actionFunctor` or with
`Langlands.Shimura.Coefficients.torsionSystem` (systems in
`Action (ModuleCat R) G`), is formalized. The published
`Langlands.Shimura.Coefficients.torsionTensorEquiv` gives the pointwise
equivalence `(R / I ^ n) ⊗_R M ≃ M / I ^ n M` for an ideal `I` by the same
Mathlib map; this module does not use it. The module does not construct
Harris's lattice `𝓛_W`, the sheaves `𝓛̃_m` or `W̃`, and makes no
statement about cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
