# Harris's stable coefficient lattices as `ℓ`-divisible systems

Author: Worker 61. Built on the published modules
`Langlands.Cohomology.DivisibleSystem.ReductionAdic` (`reductionCompIso`,
`map_reductionπ_reductionCompIso_hom`, `reductionTowerCompIso`,
`reductionAdicIso`, `reductionπ_reductionAdicIso_hom`,
`powSMul_moduleCat_hom_apply`) and
`Langlands.Shimura.Coefficients.HarrisLattice` (Worker 57: `harrisLattice`,
`harrisLattice_stable`, `harrisLatticeAction`, `HarrisCoefficientIntegers`).
Through their imports it uses `powSMul` and `map_powSMul`
(`Langlands.Cohomology.DivisibleSystem`), `reductionTower`, `reductionπ`,
`reductionπ_map` and `reductionSystem`
(`Langlands.Cohomology.DivisibleSystem.Reduction`), Worker 13's
`Langlands.Coefficients.AdicSystem` (`quotientMap`,
`quotientMap_transition`), and Worker 57's
`Langlands.Shimura.Coefficients.Lattice` (`IsStable`, `latticeAction`,
`torsionSystem`, `torsionAction`, `torsionQuotientMap`, `CoefficientIntegers`,
`StableCoefficientLattice` with `carrier`, `stable`, `action` and `system`).
From Mathlib it uses `Action.forget`, `Action.mkIso`, `Action.Hom.ext`,
`Functor.map_epi`, `Functor.mono_map_iff_mono`, `ModuleCat.mono_iff_injective`,
`NatIso.ofComponents`, `cancel_epi`, `Rep.ActionToRep`,
`Representation.IntertwiningMap.ext`, `Submodule.coe_smul`,
`Nat.cast_smul_eq_nsmul`, `IsUnit.smul_left_cancel`, `map_natCast`,
`Nat.cast_ne_zero`, `Ne.isUnit` and `IsUnit.map`.

## Conventions

`ℓ` and `m` are natural numbers. `powSMul ℓ m X` is the published
endomorphism "multiplication by `ℓ ^ m`" of an object `X` of a preadditive
category. For `X` in an abelian category, the published
`reductionTower ℓ X : ℕᵒᵖ ⥤ C` is the inverse system whose level `m` is the
cokernel `X / ℓ ^ m X` of `powSMul ℓ m X`, with the projections as transition
maps, and `reductionπ ℓ X m : X ⟶ X / ℓ ^ m X` is the cokernel projection.
When multiplication by `ℓ` is a monomorphism on `X`, the published
`reductionSystem ℓ X` is the `ℓ`-divisible system (Harris 1999, (2.1)) with
tower `reductionTower ℓ X`.

`R : Type u` is a commutative ring, `G : Type v` a group, and `M` is in
`Action (ModuleCat.{w} R) G`, an action of `G` on an `R`-module `M.V`. For an
ideal `I` of `R`, Worker 57's published `torsionSystem I M` is the inverse
system in `Action (ModuleCat R) G` whose level `m` is
`torsionAction I M m`, the quotient `M.V / I ^ m M.V` with the induced action,
and `torsionQuotientMap I M m : M ⟶ torsionAction I M m` is the equivariant
quotient map. Here always `I = (ℓ) = Ideal.span {(ℓ : R)}`.

## Actions on modules (namespace `Langlands.Cohomology.DivisibleSystem`)

- `reductionActionVIso ℓ M m` is the isomorphism of `R`-modules between the
  underlying module of `M / ℓ ^ m M` (the cokernel in
  `Action (ModuleCat R) G`) and `M.V / (ℓ) ^ m M.V`: the published
  `reductionCompIso` for the forgetful functor `Action.forget`, which is
  additive and preserves cokernels, followed by the published
  `reductionAdicIso`.
- `reductionπ_hom_reductionActionVIso_hom`: composed with the underlying map
  of `reductionπ ℓ M m`, it is `quotientMap (ℓ) m`, that is, it sends the
  class of `x` to the class of `x`.
- The underlying map of `reductionπ ℓ M m` is an epimorphism (instance,
  `Functor.map_epi`).
- `reductionActionIso ℓ M m : M / ℓ ^ m M ≅ torsionAction (ℓ) M m` is the
  isomorphism of actions (`Action.mkIso`) with underlying isomorphism
  `reductionActionVIso`. It commutes with the action of `g ∈ G`: after
  cancelling the epimorphism `reductionπ`, which commutes with the actions,
  both sides are `quotientMap (ℓ) m` composed with the action of `g`, by the
  naturality of `quotientMap`.
- `reductionπ_reductionActionIso_hom`: `reductionπ ℓ M m` followed by
  `reductionActionIso` is `torsionQuotientMap (ℓ) M m`.
- `reductionTowerActionIso ℓ M : reductionTower ℓ M ≅ torsionSystem (ℓ) M`
  has components `reductionActionIso` (`reductionTowerActionIso_hom_app`).
  Naturality in `m` is checked after cancelling `reductionπ`: both sides are
  `quotientMap (ℓ) m`, by `reductionπ_map` and the published
  `quotientMap_transition`.
- `mono_powSMul_action_iff`: `powSMul ℓ 1 M` is a monomorphism if and only if
  `x ↦ (ℓ : R) • x` is injective on `M.V`. `Action.forget` preserves and
  reflects monomorphisms and carries `powSMul` to `powSMul` (`map_powSMul`); in
  `ModuleCat` monomorphisms are the injective maps, and `powSMul ℓ 1` is
  `x ↦ ℓ • x` (`powSMul_moduleCat_hom_apply`).
- `mono_powSMul_latticeAction`: let `K` be a commutative `R`-algebra, `V` a
  `K`-module with compatible `R`-module structure, `ρ` an action of `G` on
  `V` by `K`-linear automorphisms and `Λ` an `R`-submodule of `V` stable
  under `ρ`. If `(ℓ : K)` is a unit, multiplication by `ℓ` is a monomorphism
  on the published `latticeAction ρ Λ`. If `ℓ • x = ℓ • y` in `Λ`, the same
  holds in `V`, where `ℓ` acts through `K`, and the unit `ℓ` cancels.

## Representations

- `actionToRep_additive`: Mathlib's functor
  `Rep.ActionToRep R G : Action (ModuleCat R) G ⥤ Rep R G` is additive; both
  sides of `F (f + g) = F f + F g` have the same underlying linear map.
- `mono_powSMul_actionToRep` (instance): if multiplication by `ℓ` is a
  monomorphism on `M`, it is one on the representation attached to `M`,
  since the functor carries `powSMul` to `powSMul` (`map_powSMul`) and, being
  an equivalence in Mathlib, preserves monomorphisms.
- `reductionTowerActionToRepIso ℓ M` is the published `reductionTowerCompIso`
  for `Rep.ActionToRep R G`: the representations attached to `M / ℓ ^ m M`
  form the tower of `(Rep.ActionToRep R G).obj M`. Through it the published
  results on reductions of representations apply to the lattices below.

## Harris's lattice

- `isUnit_natCast_of_ratAlgebra ℓ K`: a nonzero natural number is a unit in
  every `ℚ`-algebra `K`, as the image of a nonzero rational number.

For the Harris section, `A` is a finite-dimensional `ℚ`-algebra with Worker
13's involution `σ : AlgebraInvolution ℚ A`, `L` a number field, `W` an
`L`-module and `ρ` an algebraic representation of `σ.baseChange L` on `W`, as
in the published `HarrisLattice`; `p` is a finite place of `ℚ` and `ℓ` a
nonzero natural number (`[NeZero ℓ]`). With `W` finite over `L` and a compact
open level `U` of `σ.FiniteAdelicPoints`, Worker 57's `harrisLattice ρ p U` is
a submodule over `HarrisCoefficientIntegers L p`, the product of the
valuation rings at the places of `L` above `p`, of Harris's coefficient module
`(L ⊗_ℚ ℚ_p) ⊗_L W`; it is a full lattice for `L ⊗_ℚ ℚ_p` and stable under the
action `ρ.harrisAdelic p` of the subgroup `U.subgroup`.
`harrisLatticeAction ρ p U` is the restricted action.

- `mono_powSMul_harrisLatticeAction` (instance): multiplication by `ℓ` is a
  monomorphism on `harrisLatticeAction ρ p U`, by
  `mono_powSMul_latticeAction` with `K = L ⊗_ℚ ℚ_p`, a `ℚ`-algebra.
- `harrisReductionSystem ℓ ρ p U` is `reductionSystem ℓ` of
  `harrisLatticeAction ρ p U`: the `ℓ`-divisible system `{𝓛 / ℓ ^ m 𝓛}` in
  `Action (ModuleCat (HarrisCoefficientIntegers L p)) U.subgroup`.
- `harrisReductionSystemTowerIso ℓ ρ p U`: its tower is isomorphic to
  `torsionSystem (ℓ)` of `harrisLatticeAction ρ p U`, by
  `reductionTowerActionIso`.

## One place of the coefficient field

Here `l` is a finite place of `L` above `p`, `U` a subgroup of
`σ.FiniteAdelicPoints`, and `Λ` is Worker 57's
`StableCoefficientLattice ρ p l U`: a full lattice over the valuation ring
`CoefficientIntegers l` in `L_l ⊗_L W`, where `L_l` is the completion
`FiniteCompletion L l`, stable under `U`.

- `isUnit_natCast_finiteCompletion ℓ`: `ℓ` is a unit in `L_l`, as the image
  of a nonzero element of `L`.
- `mono_powSMul_stableCoefficientLattice_action` (instance): multiplication
  by `ℓ` is a monomorphism on `Λ.action`, by `mono_powSMul_latticeAction` with
  `K = L_l`.
- `stableLatticeReductionSystem ℓ Λ` is `reductionSystem ℓ Λ.action`, the
  `ℓ`-divisible system `{Λ / ℓ ^ m Λ}` in
  `Action (ModuleCat (CoefficientIntegers l)) U`.
- `stableLatticeReductionSystemTowerIso ℓ Λ`: its tower is isomorphic to the
  published `Λ.system (ℓ)` (which is `torsionSystem (ℓ) Λ.action`), by
  `reductionTowerActionIso`. The ideal is `(ℓ)`, not the maximal ideal of
  `CoefficientIntegers l`; at a place ramified over `ℓ` the two differ.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned pages):

- §3, printed p.306 (one-based PDF page 8): "`L_v = L ⊗_ℚ ℚ_v`" for a place
  `v` of `ℚ`, so `L_ℓ` is in general a finite product of finite extensions of
  `ℚ_ℓ`.
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in
  `W(L)`." (The printed `W(L)`; the lattice is an `𝒪`-lattice, and the
  published `harrisLattice` places it in `W(L_ℓ) = (L ⊗_ℚ ℚ_ℓ) ⊗_L W`.)
- §3, printed p.308 (one-based PDF page 10): the coefficients at level `m`
  are `𝒪/ℓ^m𝒪` ("`D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)`").
- §4, printed p.311 (one-based PDF page 13): "Let the `K_ℓ`-modules `(ρ, W)`
  and `𝓛 = 𝓛_W` be as in §3; let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m`
  forms an inverse system of `𝒪`-modules".

We read `𝒪_m` as `𝒪/ℓ^m𝒪`, so that `𝓛_m = 𝓛/ℓ^m𝓛` by the published
`ReductionAdic`. In Harris, `ℓ` is a rational prime and the place of the
coefficients is the place `ℓ` of `ℚ`; here `p` is any finite place of `ℚ` and
`ℓ` any nonzero natural number, and the constructions do not require `p` to
be the place of `ℓ`. (If `ℓ` is a unit in the coefficient ring, every level
`m ≥ 1` is zero; this remark is not formalized.) Harris's level `K_ℓ` and
coefficient ring `𝒪` are represented by Worker 57's level `U` and
`HarrisCoefficientIntegers L p`, as in the published `HarrisLattice`; this
module adds no modelling choice beyond taking the ideal `(ℓ)`.

With this reading, `harrisReductionSystem ℓ ρ p U` is Harris's inverse system
`{𝓛_m}` for the published lattice, with the additional `ℓ`-divisible-system
structure of (2.1) (section 2, printed p.304) proved in the published
`Reduction` module. Harris states only that the `𝓛_m` form an inverse system;
the hypothesis needed for the divisible structure, that multiplication by `ℓ`
is injective on the lattice, is proved here from invertibility of `ℓ` in
`L ⊗_ℚ ℚ_p`. The comparisons with the published torsion systems, the
injectivity criterion and the transport to representations, with their
proofs, are ours. The module is derived.

## Scope

The module compares the cokernel towers with the published quotient towers
and builds `ℓ`-divisible systems from the published lattices; it does not
construct lattices or prove their existence (Worker 57's `harrisLattice`
supplies one). `stableLatticeReductionSystem` treats one place `l` of `L`;
the reductions of `harrisLattice` are not compared with the product of those
at the places above `p`. The module does not construct the sheaves `𝓛̃_m` or
`W̃` of p.311, and makes no statement about cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
