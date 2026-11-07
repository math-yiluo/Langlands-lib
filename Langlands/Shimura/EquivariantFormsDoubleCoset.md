# Forms restricted to double cosets

Author: Worker 61. Built on the published
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`, `levelAction`,
`levelAction_apply_coe`) and
`Langlands.Representation.Induction.PermutationDual` (Worker 61:
`functionRepresentation`, `permutationDualEquiv`), with the published
`permutation` of `Langlands.Representation.Induction.PermutationModule`.
From Mathlib it uses double coset spaces (`DoubleCoset.Quotient`,
`DoubleCoset.mk`, `DoubleCoset.eq`, `DoubleCoset.mk_out_eq_mul`,
`DoubleCoset.mk_mem_mul`, `DoubleCoset.mk_mul_mem`, `DoubleCoset.out_eq'`),
quotient groups (`QuotientGroup.eq`, `QuotientGroup.induction_on`),
invariants (`Representation.invariants`), trivial and Hom representations
(`Representation.trivial`, `Representation.linHom`) and equivalences of
representations (`Representation.Equiv`).

The module shows that a form of `Langlands.Shimura.EquivariantForms` is
determined by its values at representatives of the double cosets, which
are invariant under the stabilizers. For forms with trivial coefficients,
when the stabilizers lie in the level, it identifies the forms of a smaller
normal level with functions on the quotient of the levels, compatibly with
right translation. This is a generic algebraic version of Harris's
restriction to double cosets (3.10) and (4.7). No group, level or
coefficient system of Harris is specialized here.

## Conventions

`R` is a commutative ring, `Γ` and `G` are groups, `ι : Γ →* G` is a group
homomorphism and `K` is a subgroup of `G`. `ρ` is a representation of `K` on
an `R`-module `V`. As in the published module, `forms ι K ρ` is the
`R`-submodule of functions `f : G → V` with `f (ι γ * g) = f g` and
`f (g * k) = ρ k⁻¹ (f g)` for `γ : Γ`, `g : G`, `k : K`. Elements of
subgroups are coerced to `G` silently below. For a class `x` of a quotient,
`x.out` is the representative chosen by Mathlib (`Quotient.out`, by
choice). The universes of `R`, `Γ`, `G` and `V` are independent.

## Stabilizers

- `DoubleCosets ι K` (an abbreviation): Mathlib's
  `DoubleCoset.Quotient ι.range K`, the double coset space `ι Γ \ G / K`.
- `doubleCosetStabilizer ι K y : Subgroup K`, written `Δ_y`: the elements
  `k : K` with `ι γ * y = y * k` for some `γ : Γ` (`mem_doubleCosetStabilizer`,
  true by definition). If `ι γ * y = y * a` and `ι δ * y = y * b`, then
  `ι (γ * δ) * y = y * (a * b)` and `ι γ⁻¹ * y = y * a⁻¹`, so this is a
  subgroup. It is the stabilizer of the class of `y` in `ι Γ \ G` under right
  translation by `K` (an explanation; this module has no action on
  `ι Γ \ G`).
- `mul_inv_mem_doubleCosetStabilizer`: if
  `ι γ₁ * y * k₁ = ι γ₂ * y * k₂`, then `k₂ * k₁⁻¹ ∈ Δ_y`, with the element
  `γ₂⁻¹ * γ₁` of `Γ`.
- `exists_eq_mul_out_mul g`: every `g : G` is `ι γ * y * k` for the
  representative `y` of the double coset of `g`, some `γ : Γ` and some
  `k : K` (from Mathlib's `DoubleCoset.mk_out_eq_mul`).
- `outFactor ι K g : K`: a `k` as in `exists_eq_mul_out_mul`, chosen by
  `Exists.choose`; `exists_eq_mul_out_mul_outFactor` states that it works.

## Restriction to the representatives

- `forms_apply_mul_mul`: `f (ι γ * y * k) = ρ k⁻¹ (f y)` for a form `f`.
- `apply_mem_invariants`: the value `f y` of a form lies in the invariants
  of `ρ` restricted to `Δ_y`. If `ι γ * y = y * k`, then
  `f y = f (ι γ * y) = f (y * k) = ρ k⁻¹ (f y)`, so `ρ k (f y) = f y`.
- `apply_inv_eq_of_mem_invariants`: for a `Δ_y`-invariant vector `v`, if
  `ι γ₁ * y * k₁ = ι γ₂ * y * k₂`, then `ρ k₁⁻¹ v = ρ k₂⁻¹ v`, since
  `v = ρ (k₂ * k₁⁻¹) v` by `mul_inv_mem_doubleCosetStabilizer`.
- `DoubleCosetFamilies ι K ρ` (an abbreviation): the dependent functions
  assigning to each double coset `x` a vector in the invariants of `ρ`
  restricted to `Δ_{x.out}`.
- `doubleCosetLift ι K ρ φ : G → V`, for such a family `φ`:
  `g ↦ ρ (outFactor ι K g)⁻¹ (φ x)` with `x` the double coset of `g`.
  `doubleCosetLift_eq`: for every decomposition `g = ι γ * x.out * k` the
  value is `ρ k⁻¹ (φ x)`; by `apply_inv_eq_of_mem_invariants` it does not
  depend on the decomposition. `doubleCosetLift_mem`: the lift is a form;
  left translation by `ι γ₀` and right translation by `k₀` change the
  decomposition to `ι (γ₀ * γ) * x.out * k` and `ι γ * x.out * (k * k₀)`.
- `doubleCosetEquiv ι K ρ : forms ι K ρ ≃ₗ[R] DoubleCosetFamilies ι K ρ`:
  restriction to the representatives, `f ↦ (x ↦ f x.out)`
  (`doubleCosetEquiv_apply_coe`, a simp lemma true by definition), with
  inverse `doubleCosetLift`. `doubleCosetEquiv_symm_apply_coe`: the form
  attached to a family `φ` takes the value `ρ k⁻¹ (φ x)` at
  `ι γ * x.out * k`.

## Levels with trivial coefficients

Now `N ≤ K` (`hle`) is a second subgroup of `G`.
`(Representation.trivial R K R).comp (Subgroup.inclusion hle)` is the
trivial representation of `N` on `R`, so the forms of level `N` with
trivial coefficients are the functions `f : G → R` with
`f (ι γ * g) = f g` and `f (g * n) = f g` for `n : N`.

- `doubleCosetStabilizer_le_iff ι hle`: all stabilizers lie in `N`,
  `∀ g, doubleCosetStabilizer ι K g ≤ N.subgroupOf K`, if and only if for
  all `g : G` and `k : K`, the equality of the classes of `g * k` and `g` in
  `ι Γ \ G / N` implies `k ∈ N`. Forward: Mathlib's `DoubleCoset.eq` writes
  `g = ι γ * (g * k) * n` with `n : N`, so `k * n ∈ Δ_g ≤ N` and `k ∈ N`.
  Backward: if `ι γ * g = g * k`, the class of `g * k` is the class of `g`.
  Normality of `N` is not needed here.

From here on `N.subgroupOf K` is a normal subgroup of `K`, which is what the
published `levelAction` needs. For the trivial representation,
`levelAction ι (Representation.trivial R K R) hle` is right translation,
`(k • f) g = f (g * k)`.

- `trivialForms_apply_mul`: `f (g * n) = f g` for a form `f` of level `N`
  with trivial coefficients and `n : N`.
- `trivialForms_apply_mul_inv_eq`: if `a⁻¹ * b ∈ N`, then
  `f (y * a⁻¹) = f (y * b⁻¹)`; normality gives `a * b⁻¹ ∈ N`.
- `levelDoubleCosetFun ι hle f : K ⧸ N.subgroupOf K → DoubleCosets ι K → R`:
  the class of `k` goes to `x ↦ f (x.out * k⁻¹)`, well defined by the
  previous item (`levelDoubleCosetFun_mk`, a simp lemma true by
  definition). `levelDoubleCosetMap ι hle` is the same as an `R`-linear map.

The remaining declarations assume
`hΔ : ∀ g : G, doubleCosetStabilizer ι K g ≤ N.subgroupOf K`.

- `levelDoubleCosetLift ι φ : G → R`, for
  `φ : K ⧸ N.subgroupOf K → DoubleCosets ι K → R`:
  `g ↦ φ [(outFactor ι K g)⁻¹] x` with `x` the double coset of `g`.
  `levelDoubleCosetLift_eq ι hΔ φ`: for every decomposition
  `g = ι γ * x.out * k` the value is `φ [k⁻¹] x`; two decompositions differ
  by an element of `Δ_{x.out} ≤ N`. `levelDoubleCosetLift_mem ι hle hΔ φ`: the
  lift is a form of level `N` with trivial coefficients; for right
  translation by `n : N` the class `[(k * n)⁻¹] = [n⁻¹ * k⁻¹]` equals
  `[k⁻¹]` by normality.
- `levelDoubleCosetLinearEquiv ι hle hΔ`: the `R`-linear equivalence from
  the forms of level `N` with trivial coefficients to
  `K ⧸ N.subgroupOf K → DoubleCosets ι K → R`, with forward map
  `levelDoubleCosetMap` and inverse `levelDoubleCosetLift`. For the left
  inverse, write `g = ι γ * x.out * k`; then `f (x.out * k) = f g`.
- `levelDoubleCosetEquiv ι hle hΔ`: an equivalence of representations of
  `K` from `levelAction ι (Representation.trivial R K R) hle` to the
  published `functionRepresentation` of `K` on functions
  `K ⧸ N.subgroupOf K → (DoubleCosets ι K → R)` with `K` acting trivially on
  the values, `(k₀ • φ) q = φ (k₀⁻¹ • q)`. The linear equivalence is
  `levelDoubleCosetLinearEquiv`. It intertwines: both sides send `f`, `[k]`
  and `x` to `f (x.out * k⁻¹ * k₀)`, since
  `(k₀⁻¹ * k)⁻¹ = k⁻¹ * k₀`. `levelDoubleCosetEquiv_apply_mk` (simp, true
  by definition) and `levelDoubleCosetEquiv_symm_apply_coe` (the form
  attached to `φ` takes the value `φ [k⁻¹] x` at `ι γ * x.out * k`) record
  the formulas.
- `levelDoubleCosetHomEquiv ι hle hΔ`: `levelDoubleCosetEquiv` followed by
  the inverse of the published `permutationDualEquiv`, an equivalence of
  representations of `K` from the level action to
  `(permutation R K (K ⧸ N.subgroupOf K) R).linHom (Representation.trivial R K (DoubleCosets ι K → R))`,
  the representation on `Hom_R(R[K ⧸ N], DoubleCosets ι K → R)`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned
pages):

- printed p.307 (one-based PDF page 9): "In what follows, we assume
  `K = K^ℓ × K_ℓ`, where `K_ℓ = K ∩ GJ_ℓ`. We also assume `K^ℓ` is
  sufficiently small so that (3.6) `K_ℓ` acts without fixed points on
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ`."
- printed p.308 (one-based PDF page 10): "we may take
  `D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` be the `𝒪/ℓ^m𝒪`-module of continuous
  `𝒪/ℓ^m𝒪`-valued functions on `K_ℓ`, with `K_ℓ` acting by right
  translation. Fix a lattice of normal congruence subgroups
  `K_ℓ(n) ⊂ K_ℓ`, [...] Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`." Then
  "(3.9) `GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ · K^ℓ γ_j K_ℓ`. Then
  hypothesis (3.6) implies that restriction to the double cosets in (3.9)
  defines an isomorphism (3.10)
  `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⥲ [D_m(K_ℓ)^N]^{K_ℓ(n)}`. The right-hand side is
  just the sum of `N` copies of the module `D_m(K_{ℓ,n})` of
  `𝒪/ℓ^m𝒪`-valued functions on `K_{ℓ,n}`."
- printed p.310 (one-based PDF page 12): "We strengthen (3.6) by assuming
  that `K = K^{ℓ,p} × K_ℓ × K_p` and that `K^{ℓ,p}` is sufficiently small so
  that (4.5) `K_ℓ × C_p` acts without fixed points on
  `GJ(ℚ)\GJ(𝔸)/K_∞ · K^{ℓ,p}`. Let `H_p` be an open normal pro-`p` subgroup
  of `C_p` contained in `K_p`, and let `H(m) = K^{ℓ,p} × K_ℓ(m) × H_p`
  [...] (4.6) `GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^M GJ(ℚ) · K_∞ · K^{ℓ,p} γ_j K_ℓ × K_p`"
  (`C_p` is a fixed maximal compact subgroup of `GJ_p` containing `K_p`);
- printed p.311 (one-based PDF page 13): "analogous to (3.9), and
  hypothesis (4.5) implies that restriction to the double cosets in (4.6)
  defines an isomorphism (4.7)
  `𝒜_ℓ(GJ, 𝒪_m, H(m)) ⥲ [D_m(K_ℓ × C_p)^M]^{K_ℓ(m) × H_p}`. The right-hand
  side of (4.7) is the sum of `M` copies of the group
  `D_m(K_{ℓ,m} × C_p/H_p)` of `𝒪_m`-valued functions on
  `K_{ℓ,m} × C_p/H_p`. Via the duality between functions and group rings,
  this is canonically isomorphic to
  `Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`, and thus the decomposition (4.6)
  yields a canonical isomorphism (4.8)".

How the module relates to these statements (an explanation, not
formalized). As in the published `EquivariantForms.md`, read `G = GJ(𝔸)`,
`ι` the inclusion of `GJ(ℚ)`, and Harris's `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n))` as the
forms of level `K_∞ · K(n)` with the trivial representation on
`R = 𝒪/ℓ^m𝒪`.

- `DoubleCosets ι K` for the level `K_∞ · K` is the set of double cosets in
  (3.9), and Harris's `γ_j` play the role of the representatives `x.out`.
  `doubleCosetEquiv` is restriction to the double cosets for an arbitrary
  representation `ρ` of the level; the value at each representative `y` is
  constrained only by invariance under the stabilizer `Δ_y`.
- (3.6) and the hypothesis `hΔ`: `K_ℓ` acts on `GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ` by
  right translation since it commutes with `K_∞ · K^ℓ`, and the action has
  no fixed points if `[g k_ℓ] = [g]` implies `k_ℓ = 1`. Take the level
  `K_∞ · K^ℓ × K_ℓ` for `K` and `N' = K_∞ · K^ℓ`. For `k = k' k_ℓ` with
  `k' ∈ N'`, the classes of `g k` and `g k_ℓ` modulo `N'` agree, and
  `k ∈ N'` if and only if `k_ℓ = 1`. So (3.6) is the right-hand side of
  `doubleCosetStabilizer_le_iff` for `N'`, that is, `Δ_g ≤ K_∞ · K^ℓ` for all
  `g`. It implies `hΔ` for the level `N = K_∞ · K(n)` of (3.10), since
  `K_∞ · K^ℓ ≤ N`; (3.6) is stronger than `hΔ` for `N`.
- (3.10): for `N = K_∞ · K(n)`, the quotient `K ⧸ N` is
  `K_ℓ/K_ℓ(n) = K_{ℓ,n}`, and functions with values in
  `DoubleCosets ι K → R` are `N`-tuples of functions on `K_{ℓ,n}`, Harris's
  `N` copies of `D_m(K_{ℓ,n})`. Harris does not write out the restriction
  map; we read it as `F_j(k) = f(γ_j k)` on `K_ℓ`, right invariant under
  `K_ℓ(n)`, with `K_ℓ` acting by right translation. Our
  `levelDoubleCosetEquiv` sends `f` to `[k] ↦ (x ↦ f (x.out * k⁻¹))`, that
  is, to `F_j(k⁻¹)`, so that `K` acts on left cosets `K ⧸ N` by left
  multiplication as in the published `functionRepresentation`. Composition
  with inversion turns right translation `(k₀ • F)(k) = F(k k₀)` into
  `(k₀ • φ)[k] = φ [k₀⁻¹ k]`, so the two conventions give isomorphic
  representations. On the forms the action is right translation, the
  published `levelAction` for trivial coefficients.
- (4.5)-(4.7): the right-hand side of (4.7) consists of functions on
  `K_ℓ × C_p`, so we read (4.7) as the instance with the level
  `K_∞ · K^{ℓ,p} × K_ℓ × C_p` for `K` and `N = K_∞ · H(m)`, which is normal
  because `K_ℓ(m)` is normal in `K_ℓ` and `H_p` in `C_p`. By the argument
  above, (4.5) is the stabilizer condition for `N' = K_∞ · K^{ℓ,p}` and
  implies `hΔ` for `N`, and `K ⧸ N` is `K_{ℓ,m} × C_p/H_p`. Harris writes
  the double cosets (4.6) with `K_ℓ × K_p`; we do not address how his `M`
  classes compare with the classes for `K_ℓ × C_p`.
- `levelDoubleCosetHomEquiv` is the duality between functions and group
  rings quoted after (4.7), applied to the functions on `K ⧸ N` with values
  in `DoubleCosets ι K → R`. With `M` double cosets,
  `Hom_R(R[K ⧸ N], R^M)` is canonically isomorphic to Harris's
  `Hom(𝒪_m[K_{ℓ,m} × C_p/H_p]^M, 𝒪_m)`; this identification is not
  formalized. The duality itself is the
  published `permutationDualEquiv`.

The definitions, statements and proofs are ours, derived from Mathlib and
the published modules named above; the facts are standard. Worker 13 (first
executor of task 23471a9e) reported that this unit does not overlap their
work.

## Scope

The module does not specialize to Harris's groups, adelic points or levels
(such as the published `Langlands.Shimura.DefiniteForms`), and it does not
decompose levels as products `K^ℓ × K_ℓ` or identify `K ⧸ N` with
`K_{ℓ,n}`. It does not prove that the double coset spaces are finite and
imposes no continuity conditions (Harris's `D_m(K_ℓ)` consists of continuous
functions). The level comparison is stated for trivial coefficients only;
coefficient modules `𝓛` as in (3.8) and (3.11), and the `K_ℓ`-invariants
and coefficients `𝓛_m` of (4.8), are not treated.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
