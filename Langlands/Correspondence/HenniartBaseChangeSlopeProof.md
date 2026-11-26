# Slopes under weak cyclic base change: proof

The module `Langlands.Correspondence.HenniartBaseChangeSlopeProof` proves

```lean
theorem Langlands.Henniart.baseChangeSlope : BaseChangeSlopeStatement.{uK, uV}
```

for independent universe levels `uK` (p-adic fields) and `uV` (representations). The
statement is in `Langlands.Correspondence.HenniartNumericalDescentStatement`: assuming the
supercuspidal twist Swan bound `SupercuspidalTwistSwanBoundStatement`, for every cyclic
prime-degree step `S` (`M/L`, with `L = S.base`, `M = S.top`), every `Ch` with
`IsWeakCyclicBaseChange S Ch`, every supercuspidal class `π` of rank `n = k + 1` over `L`
with Swan exponent `s ≤ n x`, every constituent `ρ` of `Ch k π` has Swan exponent at most
`(ρ.1 + 1) ψ_{M/L}(x)`, where `ψ_{M/L} = S.herbrandPsi`.

This is the supercuspidal case of Henniart, *La conjecture de Langlands locale numérique
pour GL(n)* (Ann. Sci. ÉNS 1988), Proposition 6.7 (registered source
`henniart-1988-numerical`), and the route note's Lemma `lem:slopebc`
(`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`, lines 1136–1148).
The Lean proof follows the route note's argument; the local facts it uses are proved in
this module from published results of the Library, as listed below.

## Notation

Write `ℓ = S.degree = [M : L]`, `e = S.ramificationIndex`, `f = S.residueDegree`,
`d = S.differentExponent`, `c = S.wildDifferentExponent = d - e + 1`, `Ξ = S.normCharacters`,
`sw` for `supercuspidalSwanExponent`, and `ηπ` for
`supercuspidalCharacterTwist S.base k η π`.

## Auxiliary results proved in the module

**Herbrand functions** (namespace `Langlands.Ramification.Padic`, for any finite Galois
extension of p-adic fields with supplied data `T`):

- `lowerGroupOrder_le_zero`: `|G_i| ≤ |G_0|`.
- `herbrandPhi_le_self`: `φ(u) ≤ u` for `u ≥ 0`, from the floor formula
  `herbrandPhi_floor` and `|G_i| ≤ |G_0|`; hence `le_herbrandPsi_self`: `v ≤ ψ(v)` for `v ≥ 0`.
- `herbrandPhi_of_single_break`: if the Galois group has order `ℓ` and
  `G_i = ⊤` for `i ≤ t`, `G_i = ⊥` for `i > t`, then `φ(u) = t + (u - t)/ℓ` for `u ≥ t`,
  again from `herbrandPhi_floor`.

**Characters trivial on a subgroup of prime index** (`Langlands.Henniart.Numerical`):

- `exists_eval_determines`: for a subgroup `N` of prime index `ℓ` of a commutative group
  `G`, the quotient `G/N` is cyclic; for a lift `a` of a generator, a homomorphism
  `G →* ℂˣ` trivial on `N` is determined by its value at `a`, which is an `ℓ`-th root
  of unity.
- `supercuspidalSwanExponent_eq_of_hasSupercuspidalSwan`: a finite conductor witness for
  Swan exponent `s` gives `sw π = s`.

**Cyclic steps** (`Langlands.Henniart.Numerical.CyclicPrimeStep`):

- `degree_eq_card`, `degree_prime`: `ℓ` is the order of `Gal(M/L)`
  (`IsGalois.card_aut_eq_finrank`), hence prime; `isAbelianGalois`: `M/L` is abelian
  (a group of prime order is cyclic).
- `top_ramificationIndex`: `e_M = e · e_L` for the absolute ramification indices, from
  `LocalClassField.ramificationIndex_mul_ord_relative_algebraMap` at a uniformizer of `L`.
- `ramificationIndex_mul_residueDegree`: `e f = ℓ`, from the above and
  `PadicField.ramificationIndex_mul_extensionResidueDegree` (`e_M f = ℓ e_L`).
- `unramified_or_totallyRamified`: since `ℓ` is prime, either `e = 1, f = ℓ` or
  `e = ℓ, f = 1`.
- `le_herbrandPsi`: `x ≤ ψ_{M/L}(x)` for `x ≥ 0`.
- `normSubgroup_index`: `[L^× : N_{M/L}(M^×)] = ℓ`, by
  `LocalClassField.NormUnitImage.normSubgroup_index_eq_finrank`.
- `exists_eval_normCharacters`, `normCharacters_finite_ncard`: applying
  `exists_eval_determines` to the norm subgroup, `η ↦ η(a)` is injective on `Ξ` with values
  in the `ℓ`-th roots of unity, so `Ξ` is finite with at most `ℓ` elements.
- `one_mem_normCharacters`, `pow_mem_normCharacters`, `exists_pow_eq_of_ne_one`: `Ξ`
  contains `1` and is closed under powers; if `η₀ ∈ Ξ` and `η₀ ≠ 1`, then `η₀(a)` is a
  primitive `ℓ`-th root of unity, so every `η ∈ Ξ` equals `η₀ ^ j` for some `j`.
- `characterSwanExponent_le_of_unitFiltration_le`: if the unit level `U_L^m` lies in the
  norm group, every `η ∈ Ξ` has Swan exponent at most `m - 1`, by
  `TopologicalData.multiplicativeConductor_le_iff_unitFiltration_le_ker`.
- `characterSwanExponent_eq_zero_of_unramified`: if `e_L = e_M`, then
  `LocalClassField.unramifiedUnitNorms` at level `0` puts all units of `L` in the norm
  group, so every `η ∈ Ξ` has Swan exponent `0`.
- `exists_break_of_totallyRamified`: if `e_M = ℓ e_L`,
  `LocalClassField.primeTotallyRamifiedBreak` gives the single lower break `t`. Then
  `LocalClassField.primeRamifiedNormReduction` puts `U_L^{t+1}` in the norm group, so every
  `η ∈ Ξ` has Swan exponent at most `t`; `LocalClassField.primeRamifiedDifferent` gives the
  different `𝔭_M^{(t+1)(ℓ-1)}`, so `d = (t+1)(ℓ-1)` (powers of the maximal ideal are
  distinct, `Ideal.pow_right_strictAnti`); and `herbrandPhi_of_single_break` together with
  `le_herbrandPsi_self` gives `ψ_{M/L}(x) ≥ x + (ℓ - 1) max(0, x - t)` for `x ≥ 0`.
- `conductor_galoisConjugate`, `supercuspidalSwanExponent_galoisConjugate`: the conjugate
  `Π^g` (`S.galoisConjugate`) has the same conductor and Swan exponent as `Π`, by
  `Conductor.firstFixedLevel_comp_fieldEquiv` for the entrywise action of `g`.

## Proof of `baseChangeSlope`

Fix the data of the statement. Since `s ≥ 0` and `s ≤ n x`, `x ≥ 0`.

*Twists.* For every character `η`, the twist Swan bound gives
`sw(ηπ) ≤ max(s, n · sw(η))`; for `η = 1`, `ηπ = π` (`supercuspidalTwist_one`) and
`sw(1π) = s`.

*The total Swan exponent.* Let `Σ` be the sum of `sw` over the multiset `Ch k π`. Since `Ξ`
is finite, the `finsum` in (W4) is the sum over `Ξ`, so
`f Σ = ∑_{η ∈ Ξ} sw(ηπ) - f c n`. The proof shows `Σ ≤ n ψ_{M/L}(x)`:

- *Unramified step* (`e = 1`, `f = ℓ`). Every `η ∈ Ξ` has Swan exponent `0`, so
  `sw(ηπ) ≤ s`, and `∑_{η ∈ Ξ} sw(ηπ) ≤ |Ξ| s ≤ ℓ s`. Here `c = d ≥ 0`, so `ℓ Σ ≤ ℓ s`,
  `Σ ≤ s ≤ n x ≤ n ψ_{M/L}(x)`.
- *Totally ramified step* (`e = ℓ`, `f = 1`), with break `t`. Every `η ∈ Ξ` satisfies
  `sw(ηπ) ≤ B := max(s, n t)`, and `c = (t+1)(ℓ-1) - ℓ + 1 = t (ℓ - 1)`. Splitting off
  `η = 1`, `∑_{η ∈ Ξ} sw(ηπ) ≤ s + (|Ξ| - 1) B ≤ s + (ℓ - 1) B`, so
  `Σ ≤ s + (ℓ - 1)(B - n t)`. If `s ≤ n t` this is `Σ ≤ s ≤ n x ≤ n ψ_{M/L}(x)`. If
  `s > n t`, then `x > t` and `ψ_{M/L}(x) ≥ x + (ℓ - 1)(x - t)`, so
  `Σ ≤ s + (ℓ - 1)(s - n t) ≤ n x + (ℓ - 1)(n x - n t) ≤ n ψ_{M/L}(x)`.

*The constituents.* If no `η ∈ Ξ` other than `1` fixes `π`, (W3a) gives
`Ch k π = {⟨k, τ⟩}`, so `ρ = ⟨k, τ⟩` and `sw τ = Σ ≤ (k + 1) ψ_{M/L}(x)`. Otherwise some
`η₀ ≠ 1` in `Ξ` fixes `π`; every `η ∈ Ξ` is a power `η₀ ^ j`, and
`supercuspidalTwist_twist` shows that `η₀ ^ j` fixes `π` as well, so (W3b) applies:
`ℓ ∣ n` and `Ch k π` is the Galois orbit of a class `τ₁` of rank `k₁ + 1 = n / ℓ`. All
members of the orbit have the Swan exponent of `τ₁`, so `Σ = ℓ · sw τ₁`, and
`ℓ · sw τ₁ ≤ n ψ_{M/L}(x) = ℓ (k₁ + 1) ψ_{M/L}(x)` gives the bound for `ρ = ⟨k₁, τ₁^g⟩`.

The proof uses no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
