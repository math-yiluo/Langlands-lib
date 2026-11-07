# Harris's definite forms restricted to double cosets

Author: Worker 61. Built on the published
`Langlands.Shimura.DefiniteForms` (Worker 61: `ellAdicForms`,
`ellAdicRep`), `Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`, `doubleCosetStabilizer`, `doubleCosetStabilizer_le_iff`,
`doubleCosetEquiv`, `levelDoubleCosetEquiv`),
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`, `levelAction`)
and `Langlands.Representation.Induction.PermutationDual` (Worker 61:
`functionRepresentation`), and on Worker 57's similitude groups
(`AlgebraInvolution.FiniteAdelicPoints`, `finiteAdelicDiagonal`,
`finiteLocalMap`) and algebraic coefficients
(`AlgebraicRepresentation.actVia`). From Mathlib it uses images, preimages
and kernels of subgroups (`Subgroup.map`, `Subgroup.comap`,
`MonoidHom.ker`, `MonoidHom.subgroupMap`, `Subgroup.subgroupOf`), quotient
groups (`QuotientGroup.mk'`, `QuotientGroup.quotientMulEquivOfEq`,
`QuotientGroup.quotientKerEquivOfSurjective`), double cosets
(`DoubleCoset.mk`), invariants (`Representation.invariants`) and linear
equivalences of function spaces (`LinearEquiv.funCongrLeft`,
`LinearEquiv.piCongrRight`, `Submodule.topEquiv`).

The module applies the generic restriction to double cosets of
`EquivariantFormsDoubleCoset` to the spaces of Harris's §3 for the
similitude group of an algebra with involution. It defines Harris's levels
`K^ℓ`, `K_ℓ` and `K(n)`, his hypothesis (3.6) and his forms (3.7) with
coefficients in a representation of `K_ℓ`, and proves the isomorphisms of
restriction to double cosets: for arbitrary coefficients, and in the form
(3.10) for the congruence levels `K(n)` with trivial coefficients.

## Conventions

`σ : AlgebraInvolution ℚ A` is an involution of a `ℚ`-algebra `A`, finite
dimensional (`[Module.Finite ℚ A]`). `σ.FiniteAdelicPoints` is the group of
points of its similitude group over the finite adeles (Harris's
`GJ(𝔸^f)`), the rational points `σ.similitudes` (Harris's `GJ(ℚ)`) embed by
`σ.finiteAdelicDiagonal`, and `σ.finiteLocalMap ℓ` is the `ℓ`-component
map `g ↦ g_ℓ` to the points over the completion `ℚ_ℓ`, for a finite place
`ℓ` of `ℚ`. `K` is a subgroup of `σ.FiniteAdelicPoints`. Elements of
subgroups are coerced silently below, and `x.out` is Mathlib's chosen
representative of a class `x`. As in the published module, `forms ι K ρ`
consists of the functions `f` with `f (ι γ * g) = f g` and
`f (g * k) = ρ k⁻¹ (f g)`.

## Transport of function representations

This section is generic, in the namespace `Langlands.Induction`.

- `functionRepresentationCongr σ σ' f hσ e he`: for a group homomorphism
  `f : G →* G'`, representations `σ` of `G` and `σ'` of `G'` on the same
  `R`-module `W` with `σ g = σ' (f g)` (`hσ`), and a bijection `e : X ≃ Y`
  between a `G`-set and a `G'`-set with `e (g • x) = f g • e x` (`he`), the
  equivalence of representations of `G` from the published
  `functionRepresentation σ X` to `functionRepresentation σ' Y` restricted to
  `G` along `f`. The linear equivalence is `F ↦ F ∘ e.symm`
  (`functionRepresentationCongr_apply`, true by definition). It intertwines
  because `e.symm ((f g)⁻¹ • y) = g⁻¹ • e.symm y`.

## Levels and the hypothesis (3.6)

- `primeToLevel σ ℓ K` (Harris's `K^ℓ`): `K ⊓ ker (σ.finiteLocalMap ℓ)`,
  the elements of `K` with trivial `ℓ`-component (`mem_primeToLevel`, true
  by definition; `primeToLevel_le`: it lies in `K`).
- `localLevel σ ℓ K`: the image of `K` under `σ.finiteLocalMap ℓ`, a
  subgroup of the `ℓ`-adic points. `localLevelMap σ ℓ K : K →* localLevel σ ℓ K`
  is `k ↦ k_ℓ` (`localLevelMap_apply_coe`, a simp lemma true by definition),
  surjective (`localLevelMap_surjective`).
- `mem_primeToLevel_subgroupOf`: `k : K` lies in `K^ℓ` (as a subgroup of
  `K`) if and only if `k_ℓ = 1`. `primeToLevel_subgroupOf`: `K^ℓ` is the
  kernel of `localLevelMap`, hence normal in `K` (an instance).
- `LocalLevelFree σ ℓ K : Prop` (Harris's (3.6)): for all
  `g : σ.FiniteAdelicPoints` and `k : K`, if `g * k` and `g` have the same
  class in `GJ(ℚ) \ GJ(𝔸^f) / K^ℓ` (Mathlib's `DoubleCoset.mk` for the range
  of `σ.finiteAdelicDiagonal` and `K^ℓ`), then `k_ℓ = 1`.
- `localLevelFree_iff`: `LocalLevelFree σ ℓ K` holds if and only if every
  stabilizer `doubleCosetStabilizer σ.finiteAdelicDiagonal K g` (the
  published `Δ_g`, the `k : K` with `γ g = g k` for some rational `γ`) lies
  in `K^ℓ`. This is the published `doubleCosetStabilizer_le_iff` for
  `N = K^ℓ` together with `mem_primeToLevel_subgroupOf`.

## Forms with coefficients in a representation of `K_ℓ` (3.7)

Here `ρ` is a representation of `localLevel σ ℓ K` on an `R`-module `V`,
for a commutative ring `R`.

- `ellModuleForms σ ℓ K ρ` (an abbreviation, Harris's `𝒜_ℓ(GJ, 𝓛, K)`):
  `forms σ.finiteAdelicDiagonal K (ρ.comp (localLevelMap σ ℓ K))`, the
  functions `f : σ.FiniteAdelicPoints → V` with `f (γ g) = f g` for
  rational `γ` and `f (g k) = ρ(k_ℓ)⁻¹ (f g)` for `k : K`.
- `ellModuleForms_trivial` (true by definition): for the trivial
  representation of `K_ℓ` on `R` these are the generic `forms` for the
  trivial representation of `K`.
- `comp_localLevelMap_eq_one`: `ρ(k_ℓ) = 1` for `k ∈ K^ℓ`, since
  `k_ℓ = 1`.
- `invariants_eq_top ρ h g`: under `h : LocalLevelFree σ ℓ K`, the
  invariants of `ρ(·_ℓ)` restricted to `Δ_g` are all of `V`, because
  `Δ_g ≤ K^ℓ` acts trivially.
- `ellModuleFormsEquiv σ ℓ h`: under (3.6), the `R`-linear equivalence
  from `ellModuleForms σ ℓ K ρ` to the functions
  `DoubleCosets σ.finiteAdelicDiagonal K → V` on `GJ(ℚ) \ GJ(𝔸^f) / K`,
  `f ↦ (x ↦ f x.out)` (`ellModuleFormsEquiv_apply`, a simp lemma true by
  definition). It is the published `doubleCosetEquiv`, whose target assigns
  to each double coset `x` a `Δ_{x.out}`-invariant vector, followed by
  `invariants_eq_top` in each coordinate.

## `ℓ`-adic coefficients

Here `ρ` is an algebraic representation of the scalar extension of the
similitude group to a field `L` on an `L`-vector space `W`, `S` is an
`L`-algebra and `φ : ℚ_ℓ → S` is a `ℚ`-algebra map, as for the published
`ellAdicForms`.

- `localRep σ ℓ ρ φ K : Representation S (localLevel σ ℓ K) (S ⊗[L] W)`:
  Worker 57's `ρ.actVia φ` on the `ℓ`-adic points, as linear maps,
  restricted to `K_ℓ`.
- `ellAdicForms_eq_ellModuleForms` (true by definition): the published
  `ellAdicForms σ ρ ℓ φ K` (Harris's `𝒜_ℓ(GJ, ρ, K)(S)`, (3.3)) equals
  `ellModuleForms σ ℓ K (localRep σ ℓ ρ φ K)`, since the published
  `ellAdicRep` is `ρ.actVia φ` composed with `σ.finiteLocalMap ℓ`.
- `ellAdicFormsEquiv σ ℓ ρ φ h`: under (3.6), `ellModuleFormsEquiv` for
  `localRep`, an `S`-linear equivalence from `ellAdicForms σ ρ ℓ φ K` to
  `DoubleCosets σ.finiteAdelicDiagonal K → S ⊗[L] W`, `f ↦ (x ↦ f x.out)`
  (`ellAdicFormsEquiv_apply`).

## Congruence levels (3.10)

Here `H` is a subgroup of `localLevel σ ℓ K` (Harris's `K_ℓ(n)`).

- `congruenceLevel σ ℓ K H` (Harris's `K(n)`): the elements `k` of `K` with
  `k_ℓ ∈ H`, as a subgroup of `σ.FiniteAdelicPoints`;
  `congruenceLevel_le`: it lies in `K`.
- `congruenceLevel_subgroupOf`: as a subgroup of `K` it is the preimage of
  `H` under `localLevelMap`. `primeToLevel_le_congruenceLevel`:
  `K^ℓ ≤ K(n)`, since `1 ∈ H`.
- `doubleCosetStabilizer_le_congruenceLevel σ ℓ h H g`: under (3.6),
  `Δ_g ≤ K^ℓ ≤ K(n)`.

From here on `H` is normal in `K_ℓ`. Then `K(n)` is normal in `K` (an
instance, by `congruenceLevel_subgroupOf`).

- `congruenceQuotientEquiv σ ℓ K H : K ⧸ K(n) ≃* K_ℓ ⧸ H`, `[k] ↦ [k_ℓ]`
  (`congruenceQuotientEquiv_mk`, a simp lemma true by definition): the
  composite `K → K_ℓ → K_ℓ ⧸ H` is surjective with kernel `K(n)`.
- `levelForms_eq_ellModuleForms` (true by definition): the forms of level
  `K(n)` with trivial coefficients `R` on which the published `levelAction`
  acts are `ellModuleForms σ ℓ (congruenceLevel σ ℓ K H)` for the trivial
  representation, Harris's `𝒜_ℓ(GJ, R, K(n))`.
- `congruenceLevelEquiv σ ℓ H h`: under (3.6), an equivalence of
  representations of `K` from `levelAction σ.finiteAdelicDiagonal
  (Representation.trivial R K R) (congruenceLevel_le σ ℓ K H)` (right
  translation `(k • f) g = f (g * k)` on the forms of level `K(n)`) to the
  published `functionRepresentation` of `K_ℓ` on the functions
  `K_ℓ ⧸ H → (DoubleCosets σ.finiteAdelicDiagonal K → R)`, with `K_ℓ`
  acting trivially on the values, `(a • φ) q = φ (a⁻¹ • q)`, restricted to
  `K` along `localLevelMap`. It is the published `levelDoubleCosetEquiv` for
  the level `N = K(n)`, with the stabilizer hypothesis from
  `doubleCosetStabilizer_le_congruenceLevel`, followed by
  `functionRepresentationCongr` along `congruenceQuotientEquiv`; the
  equivariance `[k * k'] ↦ k_ℓ • [k'_ℓ]` holds because `localLevelMap` is a
  homomorphism. `congruenceLevelEquiv_apply_mk`: the image of `f` takes the
  value `f (x.out * k⁻¹)` at `[k_ℓ]` and `x`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker
61 read the rendered scanned pages.

- Printed p.306 (one-based PDF page 8), as quoted in the published
  `DefiniteForms.md`: "`K` is as above, `ℓ` is a finite prime in `ℚ`,
  `K^ℓ = K ∩ GJ^ℓ`".
- Printed p.307 (one-based PDF page 9): "(3.3) `𝒜_ℓ(GJ, ρ, K)(L') =
  {f : _{K^ℓ}S(GJ) → W(L'_ℓ) | f(gk) = ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸),
  k ∈ K ∩ GJ_ℓ}`." Later: "In what follows, we assume `K = K^ℓ × K_ℓ`,
  where `K_ℓ = K ∩ GJ_ℓ`. We also assume `K^ℓ` is sufficiently small so that
  (3.6) `K_ℓ` acts without fixed points on `GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ`. Let `𝒪`
  denote the ring of integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable
  `𝒪`-lattice in `W(L)`. Then we can define"
- Printed p.308 (one-based PDF page 10): "(3.7) `𝒜_ℓ(GJ, 𝓛_W, K) =
  {f : _{K^ℓ}S(GJ) → 𝓛_W | f(gk) = ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸),
  k ∈ K ∩ G_ℓ}`, with the continuity hypothesis as above. [...] More
  generally, we can let `𝓛` be any continuous `K_ℓ`-module; then
  `𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy with (3.7), still makes sense. [...]
  Fix a lattice of normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`,
  `n = 0, 1, 2, ...`, with `⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such that
  `⋂_n K_ℓ(n) = {1}`. Let `K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`." Then, after
  (3.8): "Indeed, write (3.9) `GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ ·
  K^ℓ γ_j K_ℓ`. Then hypothesis (3.6) implies that restriction to the double
  cosets in (3.9) defines an isomorphism (3.10)
  `𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⥲ [D_m(K_ℓ)^N]^{K_ℓ(n)}`. The right-hand side is
  just the sum of `N` copies of the module `D_m(K_{ℓ,n})` of
  `𝒪/ℓ^m𝒪`-valued functions on `K_{ℓ,n}`." Here
  `D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` is the module of continuous functions on
  `K_ℓ` with `K_ℓ` acting by right translation, and
  `K_{ℓ,n} = K_ℓ/K_ℓ(n)`.

How the module relates to these statements (an explanation, not
formalized):

- Adelic setting. As in the published `DefiniteForms.md`, Harris's
  functions on `GJ(𝔸)` right invariant under `GJ_∞` (and `K_∞`) are read as
  functions on `GJ(𝔸^f)`, so `GJ(ℚ)\GJ(𝔸)/K_∞ · K^ℓ` becomes
  `GJ(ℚ) \ GJ(𝔸^f) / K^ℓ`.
- Levels. Harris assumes `K = K^ℓ × K_ℓ`; this product decomposition is
  not formalized and not assumed. `primeToLevel` is Harris's
  `K^ℓ = K ∩ GJ^ℓ` for any `K`, reading `GJ^ℓ` as the finite adelic points
  with trivial `ℓ`-component. Harris's `K_ℓ = K ∩ GJ_ℓ` lies in `GJ(𝔸^f)`;
  our `localLevel` is a subgroup of the `ℓ`-adic points. For a product `K`,
  the `ℓ`-component map identifies `K ∩ GJ_ℓ` with `localLevel`, and
  `k = k^ℓ k_ℓ`; for general `K` the image can be larger than
  `K ∩ GJ_ℓ`. Likewise `congruenceLevel` is `K_ℓ(n) × K^ℓ` for a product
  `K`, and `congruenceQuotientEquiv` identifies `K ⧸ K(n)` with Harris's
  `K_{ℓ,n}`. We take a single normal subgroup `H`; the tower in `n`, its
  intersection and its openness are not formalized.
- (3.6). For a product `K`, right translation by `k_ℓ ∈ K_ℓ` commutes with
  `K^ℓ`, so `K_ℓ` acts on `GJ(ℚ) \ GJ(𝔸^f) / K^ℓ`, and the class of `g * k`
  equals the class of `g k_ℓ`. "Without fixed points" means that
  `[g k_ℓ] = [g]` implies `k_ℓ = 1`, which is `LocalLevelFree`. For general
  `K`, the normal subgroup `K^ℓ` of `K` acts trivially, so `K ⧸ K^ℓ`, which
  `localLevelMap` identifies with `localLevel`, still acts on
  `GJ(ℚ) \ GJ(𝔸^f) / K^ℓ` by right translation; `LocalLevelFree` is stated
  with right translation by `k : K` and this action is not constructed.
- (3.3) and (3.7). Harris's functions on `_{K^ℓ}S(GJ)` with
  `f(gk) = ρ(k_ℓ)^{-1} f(g)` for `k ∈ K ∩ GJ_ℓ` are, for a product `K`, the
  functions with `f(gk) = ρ(k_ℓ)^{-1} f(g)` for all `k ∈ K`, since `K^ℓ`
  acts trivially; this is the reading of the published `ellAdicForms`, and
  `ellModuleForms` takes the same functional equation for any
  representation `ρ` of `K_ℓ` on any `R`-module `𝓛` ("any continuous
  `K_ℓ`-module"). Harris's `𝓛_W` is a lattice in `W(L)`; we do not
  formalize lattices here, and `ellAdicForms_eq_ellModuleForms` covers the
  coefficients `W(S)` of (3.3). No continuity is imposed, on `𝓛` or on
  the forms.
- Restriction to double cosets. Harris states it for (3.10) only.
  `ellModuleFormsEquiv` is the same restriction for the forms (3.7) with
  arbitrary coefficients: under (3.6) a form is an arbitrary function on
  the double cosets `GJ(ℚ) \ GJ(𝔸^f) / K` of (3.9), Harris's `γ_j` playing
  the role of the representatives `x.out`. This general version is ours.
- (3.10). `levelForms_eq_ellModuleForms` identifies the source of
  `congruenceLevelEquiv` with `𝒜_ℓ(GJ, R, K(n))`; Harris takes
  `R = 𝒪/ℓ^m𝒪`. Under (3.6), `congruenceLevelEquiv` identifies it with the
  functions on `K_ℓ ⧸ K_ℓ(n) = K_{ℓ,n}` with values in the functions on the
  `N` double cosets, Harris's sum of `N` copies of `D_m(K_{ℓ,n})`, and with
  `[D_m(K_ℓ)^N]^{K_ℓ(n)}`, the `K_ℓ(n)`-invariant functions on `K_ℓ` for
  right translation. As explained in the published
  `EquivariantFormsDoubleCoset.md`, Harris does not write out the
  restriction map; we read it as `F_j(k) = f(γ_j k)`, while our map sends
  `f` to `[k_ℓ] ↦ (x ↦ f (x.out * k⁻¹))`, the convention of the published
  `functionRepresentation` (left translation of the argument); composition
  with inversion relates the two. On the right-hand side `K` acts through
  `k ↦ k_ℓ`; on the forms it acts by right translation.

The definitions, statements and proofs are ours, derived from Mathlib and
the published modules named above. Worker 13 (first executor of task
23471a9e) reported that this unit does not overlap their work.

## Scope

The module does not decompose levels as products `K^ℓ × K_ℓ`, does not
embed `GJ_ℓ` into `GJ(𝔸^f)`, and imposes no openness, compactness or
continuity conditions (Harris's `D_m(K_ℓ)` consists of continuous
functions). It does not prove that the double coset spaces are finite. It
does not treat the lattices `𝓛_W`, the base change isomorphism after (3.7),
the isomorphisms (3.8) and (3.11) with tensor products and
`K_{ℓ,n}`-invariants, or the towers in `n` and `m`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
