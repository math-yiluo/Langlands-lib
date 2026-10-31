# Equivariant functions on double cosets

Author: Worker 61. Built on Mathlib's representation theory
(`Representation.coind`, `Representation.coindV`, `Representation.invariants`,
`Representation.IntertwiningMap`, `Representation.ofQuotient`,
`Representation.IsTrivial`, `Rep.coindFunctor`, `Rep.resFunctor`,
`Rep.invariantsFunctor` and their limit-preservation instances) and on
Worker 13's published `Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`, the smooth part of an algebraic
representation as an object of the published category `Langlands.SmoothRep`).

The module defines a generic algebraic version of the functional equations
of Harris's spaces of `ℓ`-adic automorphic forms on a totally definite
group, and its basic structure: functoriality in the coefficients, the
comparison with coinduction, right translation and change of normal level.
It does not specialize to Harris's groups, adelic points, levels or
coefficient systems.

## Conventions

`R` is a commutative ring, `Γ` and `G` are groups, `ι : Γ →* G` is a group
homomorphism and `K` is a subgroup of `G`. A representation `ρ` of `K` on an
`R`-module `V` is Mathlib's `Representation R K V`. Elements of a subgroup are
coerced to `G` silently below. The ring, groups and carriers have independent
universes `uR`, `uΓ`, `uG` and `t`.

## Forms

- `forms ι K ρ : Submodule R (G → V)`: the functions `f : G → V` with
  `f (ι γ * g) = f g` for all `γ : Γ`, `g : G` (left invariance under
  `ι Γ`) and `f (g * k) = ρ k⁻¹ (f g)` for all `g : G`, `k : K`. Both
  conditions are linear in `f`. `mem_forms` unfolds membership.
- `formsEquivInvariants ι K ρ`: an `R`-linear equivalence between
  `forms ι K ρ` and the invariants under `Γ` of Mathlib's coinduced
  representation `Representation.coind K.subtype ρ` composed with `ι`.
  Mathlib's coinduction along `K.subtype` is the module of functions
  `f' : G → V` with `f' (k * h) = ρ k (f' h)` for `k : K`, `h : G`, and `G`
  acts by right translation `(x • f') h = f' (h * x)`. The equivalence sends
  `f` to `f' h = f h⁻¹` and back by the same formula. The two functional
  equations correspond under inversion: `f (g * k) = ρ k⁻¹ (f g)` at
  `g = h⁻¹`, `k⁻¹` becomes `f' (k * h) = ρ k (f' h)`, and invariance of `f'`
  under right translation by `ι γ` becomes `f (ι γ⁻¹ * g) = f g`, which is
  left invariance at `γ⁻¹`.

## Functoriality in the coefficients

- `formsMap R φ`: for an intertwining map `φ : ρ.IntertwiningMap σ`,
  postcomposition `f ↦ φ ∘ f` maps `forms ι K ρ` linearly to `forms ι K σ`.
  `formsMap_apply_coe` records the formula.
- `formsFunctor R ι K : Rep.{t} R K ⥤ ModuleCat.{max uG t} R`: a
  representation `A` goes to `forms ι K A.ρ`, a morphism to `formsMap`.
  Identity and composition laws hold by definition.
- `formsFunctorIso R ι K`: a natural isomorphism from `formsFunctor R ι K`
  to `Rep.coindFunctor R K.subtype ⋙ Rep.resFunctor ι ⋙
  Rep.invariantsFunctor R Γ` with components `formsEquivInvariants`;
  naturality holds by definition.
- An instance `PreservesLimits (formsFunctor.{max uG t} R ι K)`, stated for
  representations with carriers in `Type (max uG t)`. It is transported along
  `formsFunctorIso` from the composite, which preserves limits by Mathlib's
  instances: coinduction is a right adjoint of restriction
  (`Rep.resCoindAdjunction`, at carrier universe `max uG t`), restriction
  preserves limits, and invariants are a right adjoint of the trivial
  representation functor. In particular the functor of forms is left exact.

## Right translation

`H` is a group with a homomorphism `ψ : H →* G` and
`hψ : ∀ h k, ψ h * k = k * ψ h` (the image of `ψ` commutes elementwise with
`K`).

- `rightTranslation ι K ρ ψ hψ : Representation R H (forms ι K ρ)`:
  `(h • f) g = f (g * ψ h)` (`rightTranslation_apply_coe`). Left invariance
  is preserved since left and right translation commute;
  `f (g * ψ h * k) = f (g * k * ψ h)` by `hψ` gives the `K`-equation.
- `formsRepFunctor R ι K ψ hψ : Rep.{t} R K ⥤ Rep.{max uG t} R H`: forms with
  this action; `formsMap` intertwines it, by definition.
- `smoothFormsFunctor R ι K ψ hψ`, for a topological group `H`: the
  composite of `formsRepFunctor` with the published
  `SmoothRep.smoothPartFunctor`, sending `A` to the smooth vectors of forms
  (the forms fixed by some open subgroup of `H` under right translation) as a
  smooth representation of `H`. It is an abbreviation.

## Change of level

`K' ≤ K` (`hle`) are subgroups of `G` with `K'.subgroupOf K` normal in `K`,
and `ρ` is a representation of `K`; `ρ.comp (Subgroup.inclusion hle)` is its
restriction to `K'`.

- `levelAction ι ρ hle : Representation R K (forms ι K' (ρ.comp
  (Subgroup.inclusion hle)))`: `(k • f) g = ρ k (f (g * k))`
  (`levelAction_apply_coe`). For `k' : K'`, write
  `g * k' * k = g * k * m` with `m = k⁻¹ * k' * k ∈ K'` by normality; then
  `ρ k (f (g * k * m)) = ρ k (ρ m⁻¹ (f (g * k))) = ρ k'⁻¹ (ρ k (f (g * k)))`,
  so the `K'`-equation is preserved. It is a group action since
  `ρ (a * b) (f (g * a * b)) = ρ a (ρ b (f ((g * a) * b)))`.
- An instance `Representation.IsTrivial` for `levelAction ι ρ hle` composed
  with the inclusion of `K'.subgroupOf K`: for `k ∈ K'` the `K'`-equation
  gives `ρ k (f (g * k)) = ρ k (ρ k⁻¹ (f g)) = f g`.
- `levelQuotientAction ι ρ hle`: the induced representation of
  `K ⧸ K'.subgroupOf K`, Mathlib's `Representation.ofQuotient`.
- `levelInvariantsEquiv ι ρ hle`: an `R`-linear equivalence between the
  invariants of `levelAction ι ρ hle` and `forms ι K ρ`, keeping the
  underlying function. If `ρ k (f (g * k)) = f g` for all `k : K`, applying
  `ρ k⁻¹` gives `f (g * k) = ρ k⁻¹ (f g)`; conversely a form of level `K`
  restricts to a form of level `K'` that is invariant.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3, printed p.306 (one-based PDF page 8):
"Let `K ⊂ GJ(𝔸^f)` be an open compact subgroup,
`_K S(GJ) = GJ(ℚ)\GJ(𝔸)/GJ_∞ × K`. More generally, if `U ⊂ GJ(𝔸^f)` is any
closed subgroup, we let `_U S(GJ) = lim_{K ⊃ U} _K S(GJ)`, the limit over
open compact subgroups `K` containing `U`. Let `(ρ, W)` denote a
finite-dimensional algebraic representation of `GJ`, rational over the
number field `L = L(ρ)`. [...] In what follows, `K` is as above, `ℓ` is a
finite prime in `ℚ`, `K^ℓ = K ∩ GJ^ℓ`, and all functions are taken to be
continuous."

Printed p.307 (one-based PDF page 9): "If `L'` is an `L_ℓ` algebra, we
define (3.3) `𝒜_ℓ(GJ, ρ, K)(L') = {f : _{K^ℓ}S(GJ) → W(L'_ℓ) | f(gk) =
ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ GJ_ℓ}`. Here the standing continuity
hypothesis needs to be specified. We assume `f ∈ 𝒜_ℓ(GJ, ρ, K)(L')` to be
locally constant on `GJ(𝔸^{f,ℓ})`; continuity of `f` in `G_ℓ` is guaranteed
by the functional equation." Later on the page: "In what follows, we assume
`K = K^ℓ × K_ℓ`, where `K_ℓ = K ∩ GJ_ℓ`."

Printed p.308 (one-based PDF page 10): "(3.7) `𝒜_ℓ(GJ, 𝓛_W, K) = {f :
_{K^ℓ}S(GJ) → 𝓛_W | f(gk) = ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ G_ℓ}`, with
the continuity hypothesis as above. [...] More generally, we can let `𝓛` be
any continuous `K_ℓ`-module; then `𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy with
(3.7), still makes sense. [...] Let `𝓛` be a free `𝒪/ℓ^m𝒪`-module of finite
order with a continuous action of `K_ℓ`, which we suppose to factor through
the quotient group `K_{ℓ,n} = K_ℓ/K_ℓ(n)`. Then there is a canonical
isomorphism (3.8) `𝒜_ℓ(GJ, 𝓛, K) ≅ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}`."
Here `K(n) = K_ℓ(n) × K^ℓ` for normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`.

Section 4, printed p.311 (one-based PDF page 13): "Proposition 4.10. There is
a spectral sequence of `𝒪`-modules (4.10.1) `E_2^{i,j} =
Ext^i(H_c^{2(n-1)-j}(M̆_N, L_ℓ(n-1)), 𝒜_ℓ(GJ, ρ, H)) ⇒ H^{i+j}(S̄_{K(N)},
W̃)`. Here `Ext^i` denotes the `i`-th derived functor of `Hom` in the category
of smooth `L_ℓ[GJ]-modules`."

How the module relates to these definitions (an explanation, not
formalized):

- Harris's `_{K^ℓ}S(GJ)` is the case `U = K^ℓ` of the limit `_U S(GJ)`. We
  read its points as the double cosets `GJ(ℚ)\GJ(𝔸)/GJ_∞ × K^ℓ` (this
  identification of the limit is not proved here), so that a function on it
  is a function on `GJ(𝔸)` that is left invariant under `GJ(ℚ)` and right
  invariant under `GJ_∞ × K^ℓ`. With `G = GJ(𝔸)`, `ι` the inclusion of
  `GJ(ℚ)`, the level `GJ_∞ × K^ℓ × K_ℓ` and `ρ` the inflation of the
  `K_ℓ`-representation along the projection to `K_ℓ`, the single equation `f (g * k) = ρ k⁻¹ (f g)` of
  `forms` contains both the right invariance and Harris's equation
  `f(gk) = ρ(k_ℓ)^{-1} f(g)`; our convention `ρ k⁻¹` is Harris's. Harris
  writes the coefficient group as `K ∩ GJ_ℓ` (and `K ∩ G_ℓ` in (3.7)); the
  generic `ρ` is any representation of the level subgroup, which covers
  Harris's "any continuous `K_ℓ`-module" `𝓛` and arbitrary coefficient rings.
- `forms` imposes no continuity condition. For Harris's open compact `K`,
  the level `GJ_∞ × K^ℓ × K_ℓ` is open in `GJ(𝔸)`, and for continuous `ρ`
  every function satisfying the equations is locally constant in the
  prime-to-`ℓ` variable and continuous, in line with Harris's remark that
  continuity in `G_ℓ` is guaranteed by the functional equation; this is not
  proved here. For a level that is not open, the continuity condition is a
  genuine restriction that `forms` does not impose.
- `levelInvariantsEquiv` is the invariants step of (3.8), with the action of
  `K_{ℓ,n}` read as right translation combined with the action on the
  coefficients: Harris does not write out the action, and we take
  `(k • f) g = ρ k (f (g * k))`. When `ρ` is trivial on the smaller level
  `K'`, the forms of level `K'` for the restriction of `ρ` are the
  `𝓛`-valued functions that are right invariant under `K'`. Their
  identification with Harris's tensor product `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛`
  (for his finite free `𝓛`) is not included.
- `formsFunctorIso` and the limit-preservation instance are internal
  generalizations: Harris states no comparison with coinduction.
- `smoothFormsFunctor` is motivated by (4.10.1), whose `Ext` is taken in
  smooth `L_ℓ[GJ]`-modules. It takes the smooth vectors of all forms under
  right translation; no identification with Harris's `𝒜_ℓ(GJ, ρ, H)` or
  its module structure in (4.10.1) is claimed, and no `Ext` groups or
  spectral sequences are formed.

All Lean statements and proofs are ours, derived from Mathlib and the
published module named above. Worker 13 (first executor of task 23471a9e)
and Worker 2 (owner of the global automorphic branch) reported no overlap,
and Worker 2 agreed with the namespace `Langlands.Shimura.EquivariantForms`.

## Scope

The module does not define `GJ`, its adelic or rational points,
`_K S(GJ)`, compact open levels, `ℓ`-adic coefficient systems or lattices,
or Harris's continuity conditions, and it does not compare `forms` with the
published global automorphic modules (`Langlands.Automorphic`). It proves
none of Harris's comparisons beyond the invariants step of (3.8), and it
constructs no cohomology, `Ext` groups or spectral sequences.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published module named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
