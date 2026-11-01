# Forms with trivial coefficients tensored with a coefficient module

Author: Worker 61. Built on the published `Langlands.Shimura.EquivariantForms`
(Worker 61: `forms`, `levelAction` with its triviality instance on the smaller
level, `levelInvariantsEquiv`) and on Mathlib's representation theory
(`Representation.tprod`, `Representation.invariants`,
`Representation.ofQuotient`, `Representation.IsTrivial`,
`Representation.Equiv`, `Representation.IntertwiningMap`) and finite free
modules (`Module.Free.chooseBasis`, `TensorProduct.lift`).

The module proves a generic algebraic form of Harris's isomorphism (3.8):
the forms of level `K` with coefficients in a finite free module `V` are
the invariants of the forms of a smaller normal level `K'` with trivial
coefficients, tensored with `V`, when the action on `V` is trivial on `K'`.
Everything is generic in the ring, groups, levels and coefficients; no group,
level or coefficient system of Harris is specialized.

## Conventions

`R` is a commutative ring, `Γ` and `G` are groups and `ι : Γ →* G` is a
group homomorphism. Elements of subgroups are coerced to `G` silently below.
For a subgroup `K` of `G` and a representation `ρ` of `K` on an `R`-module
`V`, `forms ι K ρ` is the submodule of functions `f : G → V` with
`f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)`. For a trivial `ρ`
(`Representation.IsTrivial`), these are the functions left invariant under
`ι Γ` and right invariant under `K`. The ring, groups and coefficient
modules have independent universes.

## The tensor map

`K` is a subgroup of `G`, `τ` is a trivial representation of `K` on `R` and
`σ` a trivial representation of `K` on an `R`-module `W`.

- `tensorFormsBilin ι K τ σ`: the `R`-bilinear map from `forms ι K τ` and
  `W` to `forms ι K σ` sending `(f, w)` to `g ↦ f g • w`. The value is a
  form: `f (ι γ * g) • w = f g • w`, and
  `f (g * k) • w = f g • w = σ k⁻¹ (f g • w)` since `τ` and `σ` are
  trivial.
- `tensorForms ι K τ σ : forms ι K τ ⊗[R] W →ₗ[R] forms ι K σ`: the induced
  linear map, `f ⊗ w ↦ (g ↦ f g • w)` (`tensorForms_tmul_coe`).
- `coordForms ι K τ σ c`: for an `R`-linear form `c : W →ₗ[R] R`, the
  linear map `forms ι K σ → forms ι K τ`, `F ↦ (g ↦ c (F g))`
  (`coordForms_apply_coe`).
- `tensorFormsEquiv ι K τ σ`: for `W` finite free (`Module.Free R W`,
  `Module.Finite R W`), `tensorForms` as an `R`-linear equivalence
  (`tensorFormsEquiv_apply`). With `b` Mathlib's chosen basis
  `Module.Free.chooseBasis R W`, whose index type is finite, the inverse
  sends `F` to `∑ i, coordForms (b.coord i) F ⊗ b i`. The two composites are
  the identity: `∑ i, b.coord i (F g) • b i = F g` by `b.sum_repr`, and
  `∑ i, (b.coord i w • f) ⊗ b i = f ⊗ ∑ i, b.coord i w • b i = f ⊗ w`.

## Invariants

For a group `H` and representations `σ₁`, `σ₂` of `H` on `R`-modules:

- `invariantsEquivOfEquiv e`: an equivalence of representations
  `e : σ₁.Equiv σ₂` restricts to an `R`-linear equivalence of the invariant
  submodules `σ₁.invariants ≃ₗ[R] σ₂.invariants`, since
  `e (σ₁ h x) = σ₂ h (e x)`; the underlying vector is `e x`
  (`invariantsEquivOfEquiv_apply_coe`).
- `invariants_ofQuotient σ S`: for a normal subgroup `S` of `H` on which `σ`
  is trivial, the invariants of the representation `σ.ofQuotient S` of
  `H ⧸ S` are those of `σ`, as submodules, since every element of `H ⧸ S`
  is the class of an element of `H`.

## Change of level

`K' ≤ K` (`hle`) are subgroups of `G` with `K'.subgroupOf K` normal in `K`,
and `ρ` is a representation of `K` on `V` whose restriction
`ρ.comp (Subgroup.inclusion hle)` to `K'` is trivial (an explicit instance
hypothesis). The published `levelAction ι ρ hle` is the representation of
`K` on `forms ι K' (ρ.comp (Subgroup.inclusion hle))` with
`(k • f) g = ρ k (f (g * k))`. For the trivial representation
`Representation.trivial R K R`, its restriction to `K'` is trivial by a local
instance of this module (the restriction of `Representation.trivial R H' R`
along any group homomorphism `H →* H'` is trivial), the forms of level `K'` with trivial
coefficients are the `R`-valued functions left invariant under `ι Γ` and
right invariant under `K'`, and `levelAction ι (Representation.trivial R K R) hle`
is right translation `(k • f) g = f (g * k)`. The tensor product action
below is Mathlib's `Representation.tprod` of this right translation and `ρ`,
`k • (f ⊗ v) = (g ↦ f (g * k)) ⊗ ρ k v`.

- `tensorForms_levelAction ι ρ hle k`: `tensorForms` at level `K'`, from
  `forms ι K' ((Representation.trivial R K R).comp (Subgroup.inclusion hle)) ⊗[R] V`
  to `forms ι K' (ρ.comp (Subgroup.inclusion hle))`, intertwines the tensor
  product action of `k` with `levelAction ι ρ hle k`; pointwise
  `f (g * k) • ρ k v = ρ k (f (g * k) • v)`.
- An instance `Representation.IsTrivial` for the tensor product action
  composed with the inclusion of `K'.subgroupOf K`: for `k` in `K'`, both
  `levelAction` (the published instance) and `ρ` (the hypothesis) act by the
  identity, and `TensorProduct.map id id = id`.
- `tensorQuotientAction ι ρ hle`: the tensor product action descended to a
  representation of `K ⧸ K'.subgroupOf K` (Mathlib's
  `Representation.ofQuotient`).
- `tensorQuotientAction_invariants`: its invariants equal the
  `K`-invariants of the tensor product action (`invariants_ofQuotient`).

From now on `V` is finite free (`Module.Free R V`, `Module.Finite R V`).

- `tensorLevelEquiv ι ρ hle`: `tensorFormsEquiv` at level `K'` as an
  equivalence of representations of `K` (`Representation.Equiv`) from the
  tensor product action to `levelAction ι ρ hle`, with
  `tensorForms_levelAction` as the intertwining property.
- `tensorInvariantsEquiv ι ρ hle`: an `R`-linear equivalence from the
  `K`-invariants of the tensor product action to `forms ι K ρ`:
  `invariantsEquivOfEquiv (tensorLevelEquiv ι ρ hle)` followed by the
  published `levelInvariantsEquiv ι ρ hle`. The underlying function of the
  image of `x` is `tensorForms x` (`tensorInvariantsEquiv_apply_coe`).
- `tensorQuotientInvariantsEquiv ι ρ hle`: the same with the
  `K ⧸ K'.subgroupOf K`-invariants of `tensorQuotientAction`, via
  `tensorQuotientAction_invariants`
  (`tensorQuotientInvariantsEquiv_apply_coe`).

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3, printed p.308 (one-based PDF page 10),
read in the rendered scanned page: "More generally, we can let `𝓛` be any
continuous `K_ℓ`-module; then `𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy with
(3.7), still makes sense. [...] Fix a lattice of normal congruence subgroups
`K_ℓ(n) ⊂ K_ℓ`, `n = 0, 1, 2, ...`, with `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such
that `⋂_n K_ℓ(n) = {1}`. Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`. Let `𝓛` be a
free `𝒪/ℓ^m𝒪`-module of finite order with a continuous action of `K_ℓ`,
which we suppose to factor through the quotient group
`K_{ℓ,n} = K_ℓ/K_ℓ(n)`. Then there is a canonical isomorphism (3.8)
`𝒜_ℓ(GJ, 𝓛, K) ⥲ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}`." Harris then
derives (3.8) from the double coset decomposition (3.9), his hypothesis
(3.6), the restriction isomorphism (3.10) and the "tautological
identification" (3.11)
`{f : K_{ℓ,n} → 𝓛 | f(k) = ρ(k)^{-1} f(1)} ⥲ [D_m(K_{ℓ,n}) ⊗ 𝓛]^{K_{ℓ,n}}`.
The spaces are those of (3.3) and (3.7) (printed p.307–308), with
`f(gk) = ρ(k_ℓ)^{-1} f(g)`; see `Langlands/Shimura/EquivariantForms.md` for
the quotations and the reading of these spaces as `forms`.

How the module relates to (3.8) (an explanation, not formalized):

- Take `G = GJ(𝔸)`, `ι` the inclusion of `GJ(ℚ)`, `R = 𝒪/ℓ^m𝒪`, the levels
  `K = GJ_∞ × K^ℓ × K_ℓ` and `K' = GJ_∞ × K^ℓ × K_ℓ(n)`, `V = 𝓛`, and `ρ`
  the action of `K_ℓ` on `𝓛` inflated along the projection of `K` to `K_ℓ`.
  `K'` is normal in `K` because `K_ℓ(n)` is normal in `K_ℓ`, and `ρ` is
  trivial on `K'` because the action factors through `K_{ℓ,n}`; these are
  the explicit hypotheses `[(K'.subgroupOf K).Normal]` and
  `[Representation.IsTrivial (ρ.comp (Subgroup.inclusion hle))]`. Then
  `K ⧸ K'` is `K_{ℓ,n}` (not formalized), `forms ι K ρ` is the analogue of
  `𝒜_ℓ(GJ, 𝓛, K)` and the forms of level `K'` with trivial coefficients
  are the analogue of `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n))`, with the identifications and
  the continuity caveats explained in `Langlands/Shimura/EquivariantForms.md`.
  `tensorQuotientInvariantsEquiv` is then the generic counterpart of (3.8),
  in the opposite direction; it is an equivalence, so the direction is
  immaterial.
- Harris's `𝓛` is "a free `𝒪/ℓ^m𝒪`-module of finite order", which is a
  finite free module over the finite ring `𝒪/ℓ^m𝒪`. We assume
  `Module.Free R V` and `Module.Finite R V` over an arbitrary commutative
  ring; these hypotheses are explicit and used only for `tensorFormsEquiv`
  and what is built on it.
- Harris neither writes out the "canonical isomorphism" nor the action of
  `K_{ℓ,n}` on the tensor product. We take the map `f ⊗ l ↦ (g ↦ f(g) · l)`
  and the diagonal action of right translation on the forms with trivial
  coefficients and `ρ` on `𝓛`, consistent with his right translation action
  on `D_m(K_ℓ)` and with (3.11). This is our reading.
- The Lean proof follows a different route from Harris's: it uses no
  analogue of (3.6), (3.9), (3.10) or (3.11). At level `K'`, where `ρ` is
  trivial, tensoring with the finite free `V` commutes with forming forms
  (`tensorFormsEquiv`, using only a basis of `V`); this is compatible with
  the actions of `K` (`tensorLevelEquiv`), and the `K`-invariants of the
  forms of level `K'` for `ρ` are the forms of level `K`
  (`levelInvariantsEquiv`).
- `Langlands/Shimura/EquivariantForms.md` lists the identification with
  Harris's tensor product as not included in that module; this module
  supplies it in the generic form above.
- `tensorFormsBilin`, `coordForms`, `invariantsEquivOfEquiv`,
  `invariants_ofQuotient`, the local triviality instance and the triviality
  instance of the tensor product action are standard internal constructions
  not printed in Harris 1999. All Lean statements and proofs are ours,
  derived from Mathlib and the published module named above.

Worker 13 (first executor of task 23471a9e) reported no overlap with this
module and asked that the finite free hypothesis and the normality and
triviality hypotheses stay explicit, and that the generic identification be
distinguished from Harris's realization; both are done above.

## Scope

The module does not define `GJ`, its adelic points, `_{K^ℓ}S(GJ)`, the
congruence subgroups `K_ℓ(n)`, `𝒪/ℓ^m𝒪`, `D_m(K_ℓ)` or Harris's continuity
conditions, and it does not identify `K ⧸ K'` with `K_{ℓ,n}`; the
specialization above is an explanation. It does not formalize (3.6) or
(3.9)–(3.11), does not pass to limits in `m` or `n`, and constructs no
cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published module named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
