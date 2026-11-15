# Forward descent of the absence of a zero-value jump

Module `Langlands.Geometry.Building.UnramifiedZeroJumpForwardDescent`, namespace
`Langlands.Geometry.Building` (the main theorems are in `MaximalUnramified`).

This module proves the forward direction of `UnramifiedZeroJumpFieldComparisonStatement`, in
contrapositive form and for an abstract family of root functions over `K = F^ur` that satisfies
three hypotheses (H1)–(H3). The theorem `MaximalUnramified.unramifiedZeroJump_forwardDescent`
has exactly the type of the hypothesis `hfwd` of
`unramifiedZeroJumpFieldComparison_of_galoisDescent` (module
`UnramifiedZeroJumpFieldComparisonAssembly`). That assembly derives the target statement from
`hfwd` and the descent principle `hdesc` of Task 6754. It shows that the torus restriction
`ψ x` of a Galois-fixed point satisfies (H1)–(H3).

## Setting and notation

- `F` is a nonarchimedean local field, `K = inertiaFixedField F` its maximal unramified
  extension, `b = algebraBaseMap F K`, and `Aut(K/F) = K ≃ₐ[F] K`. `valuation F` is the
  Library valuation on `K` (`MaximalUnramified.valuation`).
- `G` is an affine smooth `F`-group, `iS : S → G` a split torus whose underlying morphism is a
  monomorphism, and `S_K`, `G_K`, `j_K iS`, `α_K` are the base changes along `b`.
- `U_c(k)` is `rootGroupPoints i c`. `U_{2c}(k)` is `doubleRootGroupPoints i c`: the
  root group of `2c` if `2c` is a root, and `{1}` otherwise (KP before Definition 6.3.4).
- `IsRootFiltrationJump i y c 0` is the published predicate
  `¬ (rootFiltration i y c 0 ⊆ {g ∈ U_c | 0 < y c g} * U_{2c})`, i.e. KP's
  `U_{c,y,0} ⊈ U_{c,y,0+} · U_{2c}`.
- `ψ : RootFunctionFamily S_K G_K` is a family of root functions over `K`, and
  `fieldRestrict ψ` is its restriction to `F`-points:
  `(fieldRestrict ψ) α g = ψ α_K (rationalExtend g)`.
- The three hypotheses on `ψ` at `α_K` (the same as in `hdesc`):
  - (H1) for `g, h ∈ U_{α_K}(K)`: `min (ψ g) (ψ h) ≤ ψ (g h⁻¹)`;
  - (H2) for `σ ∈ Aut(K/F)` and `g ∈ U_{α_K}(K)`: `ψ (σ g) = ψ g`, where `σ g` is
    `rationalConjugate F K G σ g`;
  - (H3) for `t` in `characterValuationKernel (valuation F) S_K` (points of `S_K` at which
    every rational character has valuation one), with image `T` in `G_K(K)`, and
    `g ∈ U_{α_K}(K)`: `ψ (T g T⁻¹) = ψ g`.

## Declarations

### `doubleRootGroupPoints_le_rootGroupPoints`

`U_{2a}(k) ≤ U_a(k)` for every character `a` over any field. If `2a` is a root, this is the
published `RelativeRoot.subgroup_nsmul_le`. Otherwise `U_{2a}(k)` is trivial.

### `exists_finite_fixing_rationalPoint`

For fields `k ⊆ K` with `K/k` algebraic and an affine `k`-group `G` of finite type, every
rational point `g` of `G_K` is fixed by `rationalConjugate k K G σ` for all `σ` in the fixing
subgroup of some finite-dimensional intermediate field `E`. This is the one-point case of the
published `TwistedGeneratorReduction.exists_finite_fixing_rationalPoints`, with the same proof:
apply `IdentityComponent.exists_finite_fixing_algHoms` to the coordinate algebra homomorphism of
`g` (`GaloisPoint.coordinates` after `baseChangeCoeffEquiv`), then use
`baseChangeCoeffEquiv_rationalConjugate` and `GaloisPoint.coordinates_conjugate`.

It is restated here so that this module does not import
`UnramifiedTwistedChamberThroughFixedPointReduction`, which transitively imports
`UnramifiedOmegaGaloisStable`. That module declares an anonymous
`local instance : NontriviallyNormedField F` with the auto-generated name
`MaximalUnramified.instNontriviallyNormedField_langlands`. A draft of the descent module
`UnramifiedZeroJumpGaloisDescent` once declared an instance with the same auto-generated name,
and a module importing both would not compile. The published version names its instances
explicitly, but this module keeps the smaller import set. The final proof of the target
statement imports this module together with the descent module.

### `MaximalUnramified.not_isRootFiltrationJump_fieldRestrict_of_linearization`

Hypotheses: `iS` with `Mono iS.hom.hom.left`, `hS : IsSplitTorus S.toGrp`, `α ∈ relativeRoots
iS`, `hlin : RootGroupLinearization iS α (valuation F)`, a family `ψ` with (H1)–(H3), and
`hK : ¬ IsRootFiltrationJump (j_K iS) ψ α_K 0`.
Conclusion: `¬ IsRootFiltrationJump iS (fieldRestrict ψ) α 0`.

`RootGroupLinearization` (module `RootGroupLinearization`, Task 6754) provides maps
`q : G_K(K) → K^n` and `e : G_K(K) → K^m` and an integer `d`, such that:
- for `x ∈ U_{α_K}(K)`, `q x = 0` if and only if `x ∈ U_{2α_K}(K)`;
- `e` is additive and injective on `U_{2α_K}(K)`;
- `U_{α_K}(K)` is `Aut(K/F)`-stable, and `q` and `e` are semilinear;
- for each unit `c` of `K` with `valuation F c = 1` there is a point `t` of the
  character-valuation kernel of `S_K` whose image `T` normalizes `U_{α_K}(K)` and satisfies
  `q(T x T⁻¹) = c^d q(x)` and `e(T x T⁻¹) = c² e(x)`.

The proof does not use additivity of `q`, the value of `d`, or the Galois-fixedness of `T`.

Proof. Assume `IsRootFiltrationJump iS (fieldRestrict ψ) α 0` and derive a contradiction by
showing the inclusion `rootFiltration ⊆ {g ∈ U_α | 0 < ψ} * U_{2α}(F)`. Let `g ∈ U_α(F)` with
`(fieldRestrict ψ) α g ≥ 0`. By `rootFiltration_fieldRestrict`, `g_K = rationalExtend g`
lies in `U_{α_K,ψ,0}`. By `hK`, `g_K = u z` with `u ∈ U_{α_K}(K)`, `ψ u > 0`, and
`z ∈ U_{2α_K}(K)`.

Preliminaries from (H1): `ψ 1 > 0` (from `ψ 1 ≥ ψ u`). For `x, y ∈ U_{α_K}(K)` of positive
value, `x⁻¹` and `x y` have positive value. `U_{2α_K}(K) ≤ U_{α_K}(K)`, and
`U_{2α_K}(K)` is `Aut(K/F)`-stable: for `x ∈ U_{2α_K}(K)`, `q(σ x) = σ(q x) = 0`.

- **`2α` is not a root.** Then `2α_K` is not a root
  (`mem_roots_baseChange_iff`, together with `2 • α_K = (2 • α)_K`), so `z = 1` and
  `g_K = u`. Hence `g = g · 1` with `(fieldRestrict ψ) α g = ψ u > 0`.
- **`2α` is a root.** Then `2α_K` is a root and `U_{2α_K}(K) = U_{(2α)_K}(K)`.
  1. `B = {y ∈ U_{2α_K}(K) | ψ y > 0}` is a subgroup of `G_K(K)` (preliminaries).
     It is `Aut(K/F)`-stable by (H2).
  2. `hsq`: for a unit `c` of valuation one and `x ∈ B`, take the point `T` attached to `c`
     and set `y = T x T⁻¹`. Then `y ∈ U_{α_K}(K)` and `q y = c^d q x = 0`, so
     `y ∈ U_{2α_K}(K)`. Also `ψ y = ψ x > 0` by (H3), and `e y = c² e x`.
  3. Since `g_K` is `Aut(K/F)`-fixed (`rationalConjugate_rationalExtend`),
     `z σ(z)⁻¹ = u⁻¹ σ(u)` for every `σ`. This lies in `U_{2α_K}(K)` and has positive value by
     (H2) and the preliminaries. So `w₀ = z⁻¹` satisfies `w₀⁻¹ σ(w₀) ∈ B`.
  4. `exists_finite_fixing_rationalPoint` gives a finite-dimensional `E₀ ≤ K` whose fixing
     subgroup fixes `z⁻¹`.
  5. `exists_fixed_mul_of_unitSquare_scaling` (module `UnramifiedTraceCosetDescent`), applied
     with the action `rationalConjugateAction F K G`, `B`, the coordinates `e`, `hsq`, `E₀`
     and `w₀ = z⁻¹`, gives `b₁ ∈ B` such that `w = z⁻¹ b₁` is `Aut(K/F)`-fixed.
  6. `w ∈ U_{(2α)_K}(K)`. By `exists_mem_rootGroupPoints_of_galoisFixed` (module
     `UnramifiedFixedPointRootDescent`, Task 6754; `2α ≠ 0`), `w = rationalExtend z₀` with
     `z₀ ∈ U_{2α}(F)`. Because `2α` is a root, `U_{2α}(F)` is
     `doubleRootGroupPoints iS α`.
  7. `g = (g z₀) · z₀⁻¹`, where `z₀⁻¹ ∈ U_{2α}(F)` and `g z₀ ∈ U_α(F)`
     (`doubleRootGroupPoints_le_rootGroupPoints`). Its value is
     `ψ ((g z₀)_K) = ψ (u z z⁻¹ b₁) = ψ (u b₁) > 0`.

The declaration needs `set_option synthInstance.maxHeartbeats 400000` for the scalar action of
`K` on `Fin m → K`.

### `MaximalUnramified.unramifiedZeroJump_forwardDescent`

The statement is universally quantified over `F`. For a nonarchimedean local field `F`, a
connected reductive `F`-group `G` (`hG : IsConnectedReductive G`, whose fields give the affine
and smooth instances), a maximal split torus `iS` (`hiS : IsMaximalSplitTorus iS`; the
monomorphism instance is `mono_of_isMaximalSplitTorus hiS`), a root `α ∈ relativeRoots iS`,
and a family `ψ` with (H1)–(H3):

```
¬ IsRootFiltrationJump (j_K iS) ψ α_K 0 →
  ¬ IsRootFiltrationJump iS (fieldRestrict ψ) α 0
```

The binder text is the verbatim `hfwd` hypothesis of
`unramifiedZeroJumpFieldComparison_of_galoisDescent`, so that theorem's `hfwd` argument is
closed by this declaration.

Proof: `hS` is `hiS.isSplitSubtorus.1`. The opposite-factor-pair property of `iS` comes from
`RelativeRoot.exists_oppositeFactorPair_of_componentReductivity` with the published
`RelativeRoot.kernelCentralizerComponentReductive`, as in
`unramifiedZeroJumpLiftMultipliable_of_fieldComparison`. With it, `rootGroupLinearization`
(module `RootGroupLinearizationProof`, Task 6754) gives
`RootGroupLinearization iS α (valuation F)`. The previous theorem then concludes.

## Relation to the literature

The target statement is internal. Its Markdown explains that it follows from Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 9.4.28, at a fixed point. The proof
here follows the forward-direction sketch in that Markdown, "Expected proof": factor
`g_K = u z`, observe that `σ ↦ z σ(z)⁻¹` is a cocycle with values in the positive-value part
of `U_{2α_K}(K)`, and kill it by Galois descent. The descent step (Hilbert 90 for a vector group
with coefficients in a Galois-stable subring that contains a trace-one element) is the
Library's `TraceCocycleDescent` / `GaloisStableSubringTrace`. The proof does not use KP's
parahoric group schemes.
