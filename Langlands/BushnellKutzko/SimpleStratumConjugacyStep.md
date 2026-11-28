# The induction step in the proof of BK93 (2.6.1)

Source: Bushnell–Kutzko (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`,
proof of (2.6.1), printed pp. 84–86 (PDF pp. 96–98). The step uses (2.4.1)(i), (ii)(c)
and (iii), printed p. 65, (1.5.8), printed p. 44, and (2.2.1), printed p. 51.

## Definitions and results

- `IsPureElement 𝓛 n β` (internal notation): `β` is the element of a pure stratum on `𝓛`
  with first integer `n`. Purity does not depend on the level `r`.
  `IsPureElement.stratum` forms `[𝓛,n,r,β]` for any `r < n`. `IsPureElement.isPure_stratum`
  states that it is pure.
- `exists_simple_approx`: assuming `PureStratumSimpleApproximationStatement` (BK93
  (2.4.1)(i)), a pure element `β` has, at every level `r < n`, a pure element `γ` with
  `k₀(γ) < −r` (so `[𝓛,n,r,γ]` is simple) and `β − γ ∈ 𝔓^{−r}`.
- `exists_conj_step`: assume (2.4.1)(i). Let `β₁, β₂` be pure elements on `𝓛` with the
  same `n`, `t < n`, and `β₂ − β₁ ∈ 𝔓^{−t}`. If some `g` carries an element of
  `β₂ + 𝔓^{1−t}` into `β₁ + 𝔓^{1−t}`, then a unit `u` of `𝔄` satisfies
  `u β₂ u⁻¹ ∈ β₁ + 𝔓^{1−t}`.

## Proof of `exists_conj_step`

The proof follows the source.

1. By (2.4.1)(i), `[𝓛,n,t,β₁]` is equivalent to a simple stratum `Γ = [𝓛,n,t,γ]`. Let
   `E = F[γ]`, with a tame corestriction `s` (`tameCorestriction`), and `b_i = β_i − γ`.
   `E` is a nonarchimedean local field by its spectral structures
   (`LocalField.FiniteExtension`). The chain `C` over `𝒪[E]` is
   `𝓛.extensionChain` transferred along `subfieldIntegerEquiv`. It has the same lattices
   as `𝓛`, so `x ∈ C.endFiltration k` exactly when `x.restrictScalars F ∈ 𝔓^k`.
   By the image property of tame corestrictions, `s(𝔓^k) ⊆ C.endFiltration k`.
2. **The derived cosets are pure or null over `E`.** For each `i`, (2.4.1)(i) gives a
   simple `[𝓛,n,t−1,γ_i]` with `β_i − γ_i ∈ 𝔓^{1−t}`, so `s(b_i) ≡ s(γ_i − γ)` modulo
   `C.endFiltration (1−t)`. If `k₀(γ_i) < −t`, then `[𝓛,n,t,γ_i]` is simple and
   equivalent to `Γ`. (2.4.1)(ii)(c) (`simpleStratumCorestrictionCongruence`) gives
   `δ ∈ E` with `s(γ − γ_i) ≡ δ`, and the derived coset is that of the scalar `−δ`
   (`pureOrNull_of_scalar`). Otherwise `k₀(γ_i) = −t`. Then (2.4.1)(iii)
   (`criticalDerivedStratum`) gives a simple stratum over `E` equivalent to the derived
   stratum `[𝔅,t,t−1,s(γ_i − γ)]`. Its chain has the lattices of `𝓛`, so it is pure on `C`
   (`LatticeChain.valuation_congr`, `LatticeChain.mem_stabilizer_congr`), and
   `pureOrNull_of_isPure` applies. In the source, both cases appear as "(2.4.1)(ii), (iii)
   now show that … is equivalent to either a simple stratum or the null stratum".
3. **Intertwining in `B`.** `exists_centralizer_intertwining` writes the intertwining
   element as `(1+y)δ(1+z)` with `δ` commuting with `γ`. Since `E = F[γ]`, `δ` and `δ⁻¹`
   are `E`-linear (`exists_restrictScalars_of_commute`), giving a unit `δ_E` of
   `End_E(V)`. Applying `s`, which kills commutators with `γ` and is a `(B,B)`-bimodule
   map, shows that `δ_E` carries `s(w − γ) ∈ s(b₂) + 𝔔^{1−t}` into `s(b₁) + 𝔔^{1−t}`.
4. **The case `t − 1` over `E`.** `exists_conj_of_pureOrNull` for the local field `E` and
   the chain `C` gives a unit `x_E` of the relative order with
   `x_E s(b₂) x_E⁻¹ ≡ s(b₁)`. This covers the three cases of the source, including the
   exclusion of the mixed case by (2.6.2). Its restriction `x` is a unit of `𝔄` commuting
   with `γ`. So `b = x b₂ x⁻¹ − b₁ ∈ 𝔓^{−t}` has `s(b) ∈ 𝔔^{1−t}`.
5. **(2.2.1).** `PureApproximation.exists_conj_sub_mem` writes `b` as a commutator with
   `γ` modulo `𝔓^{1−t}`, as in (1.4.10), and gives `g' ∈ U¹(𝔄)` with
   `g'(γ + b)g'⁻¹ ≡ γ + p` and `p ∈ 𝔓^{1−t}`. As `g' ≡ 1` and `b₁ ∈ 𝔓^{−t}`,
   `g' b₁ g'⁻¹ ≡ b₁`. Hence `u = g' x` satisfies `u β₂ u⁻¹ ≡ γ + b₁ = β₁` modulo
   `𝔓^{1−t}`.
