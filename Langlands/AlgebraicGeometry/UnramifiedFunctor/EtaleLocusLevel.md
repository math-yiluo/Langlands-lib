# Levels and local data

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusLevel`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusStalk` and Mathlib's `Mathlib.RingTheory.HopkinsLevitzki`.

Fix `R`, `F`, an `R`-algebra `R'`, an ideal `𝔍` of `R'`, and
`ξ ∈ F(chart R R' 𝔍)`, the element over `Spec (R'/𝔍)`. Write `B = R'/𝔍`.

## Elements and morphisms (section `ElemEquiv`)

- `elemEquiv_congr`: elements attached by `Charts.elemEquiv` to morphisms with
  the same underlying scheme morphism agree. The two structure morphisms `t`
  and `t'` are then equal, since each is that morphism followed by the
  structure morphism of `Y'`.
- `left_eq_of_elemEquiv_eq`: conversely, if `t = t'`, equal elements come from
  morphisms with the same underlying scheme morphism (`elemEquiv` is a
  bijection).

## Levels

For a ring map `ρ : R' → D`, `levelMap R ρ : Spec D ⟶ Spec R` is the morphism
induced by `ρ ∘ algebraMap R R'`. A `Level F ρ` consists of a scheme `X`, a
morphism `q : X ⟶ Spec D` that is locally of finite type and formally
unramified, and a representation `e` of the base change of `F` along
`levelMap R ρ` by `q`. Elements of `F(T)`, for `T` over `Spec R` with structure
morphism `Spec δ ≫ levelMap R ρ`, correspond to morphisms `h : T.left ⟶ X`
with `h ≫ q = Spec δ`.

## Local data

A `LocalDatum R 𝔍 ρ w L`, for a point `w` of `Spec B` and a local ring `L`,
consists of:

- ring maps `ℓ : B → L` and `δ : D → L` with `ℓ ∘ mk_𝔍 = δ ∘ ρ` (`comm`);
- a structure morphism `f : Spec L ⟶ Spec R`, equal to `Spec` of
  `ℓ ∘ mk_𝔍 ∘ algebraMap` (`hf`);
- `comap_eq`: `ℓ⁻¹(𝔪_L) = w`;
- `univ`, the universal property: for every local ring `C`, ring maps
  `γ : B → C` and `δ' : D → C` with `γ ∘ mk_𝔍 = δ' ∘ ρ` and `γ⁻¹(𝔪_C) = w`,
  there is a local map `μ : L → C` with `μ ∘ ℓ = γ` and `μ ∘ δ = δ'`;
- `gen`: every element of `L` has the form `δ(a)/δ(s)` with `δ(s)` a unit.

`hom_ext`: ring maps out of `L` agreeing on `δ(D)` are equal, by `gen`.
`hT` checks that `Spec δ ≫ levelMap R ρ = f`.

Given a level `Lv` and a datum `d`, the construction is as follows.

- `ζ = F(homU ℓ f)(ξ) ∈ F(Spec L)`.
- `mor`: the morphism `Spec L ⟶ X` over `Spec D` attached to `ζ`.
- `pt`: the point of `X` given by `ξ`, the image of the closed point.
- `ψ = Scheme.stalkClosedPointTo mor : Λ → L`, where `Λ = 𝒪_{X,pt}`. It is a
  local map, and `mor_left` gives `mor = Spec ψ ≫ X.fromSpecStalk pt`.
- `θ = structMap q pt : D → Λ`.

Basic facts:

- `θ_ψ` / `δ_eq` / `ψ_θ_apply`: `ψ ∘ θ = δ`.
- `ψ_surjective`: write `l = δ(a)/δ(s)` (`gen`). Then `θ(s)` is a unit
  because `ψ` is local, and `l = ψ(θ(a) θ(s)⁻¹)`.
- `ker_ψ_le_maximalIdeal`: `ker ψ ⊆ 𝔪_Λ`.
- `map_ζ`: the restriction of `ζ` along `k : T ⟶ Spec L` is the element
  attached to `k.left ≫ mor` (by `elemEquiv_naturality'`).
- `exists_stalkHom`: a morphism `h : Spec C ⟶ X` from a local ring with
  `h ≫ q = Spec δ'`, sending the closed point to `x`, is
  `Spec χ ≫ X.fromSpecStalk x` for a local `χ` with `structMap q x ≫ χ = δ'`.

## The local dictionary

`stalk_kill` (Murre's lifting argument on local rings). Let `F` satisfy strong
(F5). Let `χ : Λ → A` be local, with `A` local artinian, and suppose
`KillAt ξ w A (χ ∘ θ ∘ ρ)`. Then `χ ∘ θ ∘ ρ` kills `𝔍`, and `χ = μ ∘ ψ` for a
local `μ : L → A`.

Proof. Let `𝔪 = 𝔪_A`, which is nilpotent. Since `ker ψ ⊆ 𝔪_Λ` and `χ` is
local, `mk_𝔪 ∘ χ` factors as `μ₀ ∘ ψ` with `μ₀ : L → A/𝔪` local. The following
is a lifting problem for `ξ` at `w` over `A`:

- `u₀ = homU (μ₀ ∘ ℓ)`, which sends every point to `w` by `comap_eq`;
- `v`, the element attached to `Spec χ ≫ X.fromSpecStalk pt`.

Its two restrictions agree by `map_ζ` and `elemEquiv_congr`, because
`Spec μ₀ ≫ mor` and `Spec(mk_𝔪) ≫ Spec χ ≫ fromSpecStalk` have the same
underlying morphism. `KillAt` gives the first claim. Then `χ ∘ θ ∘ ρ`
descends to `γ : B → A` with `γ⁻¹(𝔪) = w`, and `univ` gives
`μ : L → A`. The elements `F(homU γ)(ξ)` and `v` agree after reduction modulo
`𝔪`, so they are equal by strong (F5). Translating back,
`Spec μ ≫ mor = Spec χ ≫ fromSpecStalk`, and
`specMap_fromSpecStalk_injective` gives `μ ∘ ψ = χ`.

`killAt_of_van`. If `θ(ρ(𝔍)) = 0`, then `KillAt ξ w A (δ' ∘ ρ)` holds for every
local artinian `A` and `δ' : D → A`. Given a lifting problem:

- write `u₀ = Spec γ₀`;
- `univ` applied to `A/J` gives a local `μ₀ : L → A/J`;
- let `h : Spec A ⟶ X` be the morphism attached to `v`.

Comparing elements over `Spec (A/J)` gives `Spec(mk_J) ≫ h = Spec μ₀ ≫ mor`.
Hence `h` sends the closed point to `pt`. By `exists_stalkHom`,
`δ' = χ ∘ θ` for a local `χ`, and `δ'(ρ(j)) = χ(θ(ρ(j))) = 0` for `j ∈ 𝔍`.

`van_of_killAt`. Suppose `D` is noetherian and `KillAt ξ w A (δ' ∘ ρ)` holds
for all such `A` and `δ'`. Then `θ(ρ(j)) = 0` for every `j ∈ 𝔍`.

Proof. `X` is locally noetherian, being locally of finite type over
`Spec D`, so `Λ` is noetherian. For each `N`, `Λ/𝔪_Λ^{N+1}` is local
artinian, and `stalk_kill` with the quotient map shows
`θ(ρ(j)) ∈ 𝔪_Λ^{N+1}`. Krull's intersection theorem
(`Ideal.iInf_pow_eq_bot_of_isLocalRing`) gives `θ(ρ(j)) = 0`.

`ker_ψ_le`. For noetherian `D`, `ker ψ ⊆ θ(ρ(𝔍)) Λ`.

Proof. Write `K = ker ψ` and `𝔍Λ = θ(ρ(𝔍))Λ`. Then `𝔍Λ ⊆ K`, because
`ψ(θ(ρ(j))) = ℓ(mk j) = 0`. Put `Λ' = Λ/(𝔍Λ + K²)`, a local ring. Its
induced map `γ : B → Λ'` satisfies `γ⁻¹(𝔪) = w`, because `Λ' → L` is a local
surjection through which `γ` gives `ℓ`. `univ` gives `σ : L → Λ'`. The two
maps `σ ∘ ψ` and the quotient map `Λ → Λ'`:

- agree on `D`;
- agree modulo the square-zero ideal `K Λ'`, by `hom_ext`.

They are equal because `θ` is formally unramified
(`structMap_formallyUnramified`, `lift_unique`). Hence
`K ⊆ 𝔍Λ + K² ⊆ 𝔍Λ + 𝔪_Λ K`, and Nakayama's lemma
(`Submodule.le_of_le_smul_of_le_jacobson_bot`) gives `K ⊆ 𝔍Λ`.
