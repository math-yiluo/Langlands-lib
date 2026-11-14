# Spreading injectivity of an obstruction map from a flat field point

Module `Langlands.Cohomology.ModuleComplex.ObstructionInjectivitySpread`, namespace
`Langlands.Cohomology.ModuleComplex.ObstructionInjectivity`. This is a supporting module of the
proof of Murre's condition (F8) for the two-axis class presheaf. It is internal: it is a variant
of the published `ObstructionCone.openStatement` (module `ObstructionConeOpenProof`), and it uses
the same model complex and spreading argument.

## The property `InjVanishes`

Let `A` be a commutative ring, `(C, d)` an `ℕ`-indexed family of `A`-modules with maps
`d i : C i → C (i + 1)`, `Q` an `A`-module, `z ∈ C 2 ⊗[A] Q` and `M` an `A`-module.
`InjVanishes C d z M` means:

> for every `c ∈ C 1 ⊗[A] M` and every `ψ : Q →ₗ[A] M` with
> `(d 1 ⊗ M)(c) + (C 2 ⊗ ψ)(z) = 0`, we have `ψ = 0`.

If `z` is a cocycle, this says that the map `Hom_A(Q, M) → H²(C ⊗ M)`, `ψ ↦ [ψ_* z]`, is
injective. The Lean definition states only the displayed condition. It does not mention
cohomology.

Why not use `openStatement` directly: its property `HOneVanishes` also requires a first
cohomology group of the cone to vanish. In the application, `H¹(C ⊗ M)` need not vanish, so
only the injectivity part is wanted.

## Transfer along a model (section `Transfer`)

Let `φ : (K, dK) → (C, d)` be a chain map, `zh ∈ K 2 ⊗ Q` and `w ∈ C 1 ⊗ Q` with
`(φ 2 ⊗ Q)(zh) = z + (d 1 ⊗ Q)(w)`.

- `injVanishes_model`: `InjVanishes C d z M` implies `InjVanishes K dK zh M`. Given
  `(dK 1 ⊗ M)(ch) + ψ_* zh = 0`, apply `φ 2 ⊗ M`. Using `Transfer.rTensor_chain` and
  `Transfer.rTensor_lTensor`, the element `(φ 1 ⊗ M)(ch) + ψ_* w` satisfies the condition
  for `C`. Hence `ψ = 0`.
- `injVanishes_of_model`: suppose `(dK 2 ⊗ Q)(zh) = 0` and `Transfer.CohIso K C dK d φ M`
  holds, that is, `φ ⊗ M` is injective on cohomology. Then `InjVanishes K dK zh M` implies
  `InjVanishes C d z M`. Given `(d 1 ⊗ M)(c) + ψ_* z = 0`, the cocycle `ψ_* zh` of `K ⊗ M`
  maps to the coboundary of `ψ_* w - c`. Injectivity on second cohomology (the first component
  of `CohIso`, at index `1`) gives `c₀` with `(dK 1 ⊗ M)(c₀) = ψ_* zh`. Then `-c₀` and `ψ`
  satisfy the condition for `K`, so `ψ = 0`.

## The injectivity model (section `Model`)

Let `p : G₀ → Q` and `g : G₁ → G₀` be maps and `z₀ ∈ K 2 ⊗ G₀`. The published
`ObstructionCone.Model.b dK g z₀ : G₀^∨ × K 1 → G₁^∨ × K 2` is the second map of the published
model. The new first map is

- `aZ dK : ker (dK 1) → G₀^∨ × K 1`, `x ↦ (0, x)`.

Its version with coefficients in `M` is `aZM dK M : ker (dK 1) ⊗ M → Hom(G₀, M) × (K 1 ⊗ M)`,
`x ↦ (0, (ι ⊗ M)(x))`, where `ι` is the inclusion of the kernel.

- `aZ_comp`: `Model.b dK g z₀ ∘ₗ aZ dK = 0`. The second component of `b (0, x)` is
  `0 + dK 1 x = 0`.
- `ladder_aZ`: for finite projective `G₀`, `G₁`, the published `Model.termEquiv` identifies
  `aZ dK ⊗ M` with `aZM dK M`.
- `exact_rTensor_iff`: with this and the published `Model.ladder_b`, middle exactness of
  `aZ ⊗ M`, `b ⊗ M` is equivalent to middle exactness of `aZM dK M`, `Model.bM dK g z₀ M`.
  The proof uses Mathlib's `Function.Exact.iff_of_ladder_linearEquiv`.

## Exactness and injectivity (section `Exactness`)

Assume `p` is surjective and `p.lTensor (K 2) z₀ = zh`.

- `injVanishes_of_exact`: if `p ∘ₗ g = 0` and `aZM dK M`, `Model.bM dK g z₀ M` are exact at
  the middle, then `InjVanishes K dK zh M`. Given `(dK 1 ⊗ M)(ch) + ψ_* zh = 0`, the pair
  `(ψ ∘ p, ch)` lies in the kernel of `bM`. Hence it equals `(0, _)`, so `ψ ∘ p = 0`, and
  `ψ = 0` because `p` is surjective.
- `exact_of_injVanishes`: if `Function.Exact g p` and `M` is flat, then
  `InjVanishes K dK zh M` implies middle exactness of `aZM dK M`, `Model.bM dK g z₀ M`.
  Let `(w, γ)` lie in the kernel of `bM`. From `w ∘ g = 0`, `w` factors as `ψ ∘ p` through
  `Q ≅ G₀ / range g` (`Function.Exact.linearEquivOfSurjective`). The second component gives
  the condition for `(γ, ψ)`. So `ψ = 0`, hence `w = 0` and `(dK 1 ⊗ M)(γ) = 0`. By
  flatness of `M`, `ker (dK 1) ⊗ M → K 1 ⊗ M → K 2 ⊗ M` is exact
  (`Module.Flat.rTensor_exact`), so `γ` comes from `ker (dK 1) ⊗ M`. The converse inclusion
  holds because `dK 1` vanishes on its kernel.

## Main theorem `exists_injVanishes_spread`

Let `A` be noetherian, `(C, d)` a complex (`d (i+1) ∘ d i = 0`) of flat `A`-modules that is
bounded (`C i` subsingleton for `i > n`), with `ker (d 0)` finite and every cohomology group
`ker (d (i+1)) / range (d i)` finite. Let `Q` be a finite `A`-module, `z ∈ C 2 ⊗ Q` with
`(d 2 ⊗ Q)(z) = 0`, and let `k` be a field with an `A`-algebra structure that is flat over `A`.
If `InjVanishes C d z k`, then there is `g : A` with `algebraMap A k g ≠ 0` such that
`InjVanishes C d z M` holds for every `A`-module `M` on which `m ↦ g • m` is bijective.

Proof, as implemented:

1. The published `boundedFlatComplexProjective` gives a bounded complex `(K, dK)` of finite
   projective modules and a chain map `φ : K → C` that is a quasi-isomorphism in its
   elementwise sense. `QuasiIsoModule.rTensor_quasiIso` then gives
   `Transfer.CohIso K C dK d φ N` for every `A`-module `N`.
2. `Transfer.exists_transfer` (with the zero map `Q → Q` and zero correction) gives a cocycle
   `zh ∈ K 2 ⊗ Q` and `w` with `(φ 2 ⊗ Q)(zh) = z + (d 1 ⊗ Q)(w)`. By
   `injVanishes_model`, `InjVanishes K dK zh k`.
3. Choose a surjection `p : A^{n₀} → Q`. Since `A` is noetherian, `ker p` is finite, so a
   surjection `A^{n₁} → ker p` gives `g : A^{n₁} → A^{n₀}` with `Function.Exact g p`. Lift
   `zh` to `z₀ ∈ K 2 ⊗ A^{n₀}`.
4. `exact_of_injVanishes` at the flat module `k`, followed by `exact_rTensor_iff` and the
   published `exact_baseChange_of_exact_rTensor`, gives middle exactness of the base changes
   to `k` of `aZ dK` and `Model.b dK g z₀`.
5. The published `ExactSpread.exists_exact_rTensor_spread`, applied with `aZ_comp`, gives
   `g₀ : A` with `algebraMap A k g₀ ≠ 0` such that the tensored model is exact at the middle
   for every module on which `g₀` acts bijectively.
6. For such `M`, `exact_rTensor_iff` and `injVanishes_of_exact` give
   `InjVanishes K dK zh M`, and `injVanishes_of_model` (with `CohIso` at `M`) gives
   `InjVanishes C d z M`.

## Change of base ring (section `Reduction`)

Let `P → A` be a ring map, `N` a `P`-module and `M` an `A`-module that is also a `P`-module
compatibly. `red A N M : (A ⊗[P] N) ⊗[A] M ≃ₗ[A] M ⊗[P] N` is Mathlib's `TensorProduct.comm`
followed by `AlgebraTensorModule.cancelBaseChange`; `red_tmul`: `(a ⊗ n) ⊗ m ↦ (a • m) ⊗ n`.

- `red_rTensor_baseChange`: for `v : N → N'`, `red ∘ ((v ⊗ A) ⊗ M) = (M ⊗ v) ∘ red`.
- `red_lTensor`: for `ψ : Q →ₗ[A] M`, `red ∘ ((A ⊗ N) ⊗ ψ) = (ψ ⊗ N) ∘ red`, with `ψ` viewed
  as `P`-linear.
- `InjVanishesRed C d zP M`, for a family `(C, d)` of `P`-modules, a `P`-module `Q`,
  `zP ∈ Q ⊗[P] C 2` and a `P`-module `M`: every `c ∈ M ⊗[P] C 1` and `P`-linear `ψ : Q → M`
  with `(M ⊗ d 1)(c) + (ψ ⊗ C 2)(zP) = 0` have `ψ = 0`. This is `InjVanishes` over `P` with the
  coefficients written on the left.
- `exists_baseChange_iff`: for a family `(C, d)` over `P`, `z ∈ (A ⊗ C 2) ⊗[A] Q` and
  `ψ : Q →ₗ[A] M`, a solution `c` of `((d 1 ⊗ A) ⊗ M)(c) + ψ_* z = 0` exists if and only if a
  solution `c' ∈ M ⊗[P] C 1` of `(M ⊗ d 1)(c') + (ψ ⊗ C 2)(red z) = 0` exists. The two are
  related by `red`.
- `injVanishes_baseChange_iff`: if `P → A` is surjective, `InjVanishes` of the base change of
  `(C, d)` to `A` with obstruction `z` and coefficients `M` is equivalent to
  `InjVanishesRed C d (red A (C 2) Q z) M`. Surjectivity makes every `P`-linear map `A`-linear
  (Mathlib's `LinearMap.extendScalarsOfSurjective`).
- `rTensor_baseChange_eq_zero_of_red`: if `z ∈ (A ⊗ N) ⊗[A] Q` and `z₁ ∈ (A₁ ⊗ N) ⊗[A₁] Q`
  have the same image under `red` and `(v ⊗ A) ⊗ Q` kills `z`, then `(v ⊗ A₁) ⊗ Q` kills `z₁`.

Combining two instances of `injVanishes_baseChange_iff`: for two surjections `P → A` and
`P → A₁` and obstruction cochains with the same image under `red`, `InjVanishes` over `A` and
over `A₁` are equivalent. No separate theorem states this. The proof of (F8) applies the two
instances directly, with `A = Λ/I`, `A₁ = Λ/t` and coefficient modules killed by `t`.

## Provenance and inputs

Published Library inputs: `boundedFlatComplexProjective`, `QuasiIsoModule.rTensor_quasiIso`,
`Transfer.exists_transfer`, `Transfer.rTensor_chain`, `Transfer.rTensor_lTensor`,
`Transfer.CohIso`, `ObstructionCone.Model.b`, `Model.bM`, `Model.termEquiv`, `Model.ladder_b`,
`exact_baseChange_of_exact_rTensor` and `ExactSpread.exists_exact_rTensor_spread`. Everything
else is Mathlib. The statement is a linear-algebra form of the generic-injectivity part of
the argument behind The Stacks Project, Artin's Axioms, Lemma 98.23.4 (Tag 07YN). It is
adapted here to an obstruction map with arbitrary coefficient module.
