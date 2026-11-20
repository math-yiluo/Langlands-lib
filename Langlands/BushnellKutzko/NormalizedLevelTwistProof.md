# L2. Normalized level of a twist

The module `Langlands.BushnellKutzko.NormalizedLevelTwistProof` proves the published
proposition `Langlands.BushnellKutzko.NormalizedLevelTwistStatement` with independent
universes `uK` for the field and `uV` for the representation carrier.

```lean
theorem Langlands.BushnellKutzko.normalizedLevelTwist :
    NormalizedLevelTwistStatement.{uK, uV}
```

## What is proved

Let `K` be a p-adic field, `n ≥ 1`, `χ` a quasicharacter of `Kˣ`, and
`k = a(χ) - 1`, where `a(χ)` is `K.canonicalTopologicalData.multiplicativeConductor χ` and
the subtraction is truncated in `ℕ`. Let `a` be an irreducible admissible class of
`GL_n(K)` with normalized level `x`. Let `y` be the normalized level of the twist of `a`
by `χ ∘ det`. Then `y ≤ max x k`, and `y = max x k` when `x ≠ k`.

* `normalizedLevel_twist_le_and_eq_of_lt` proves `y ≤ max x k`, and `y = x` when `x > k`.
* `normalizedLevel_twist_eq_of_lt` proves `y = k` when `x < k` using the published L1
  theorem `fundamentalStratumLevel`.
* `normalizedLevelTwist` combines the two.

## Imports

- `Langlands.BushnellKutzko.NormalizedLevelTwistStatement` (published target).
- `Langlands.BushnellKutzko.FundamentalStratumLevelProof` supplies `fundamentalStratumLevel`
  from Task 7681. Task 7696 made the L1 and L2 statement modules mutually importable.
- `Langlands.ClassFieldTheory.Local.UnitFiltrationConductor` supplies the conductor
  criteria for triviality and nontriviality on principal units.
- `Langlands.Representation.Smooth.FixedVectors.OrderProof` supplies
  `Langlands.fixedVectors_antitone`. The quotient-class argument also uses the Library lemma
  `fixedVectors_twist_eq_of_le_ker`.

## Route of the Lean proof

1. **Determinants (section `DetAlgebra`, `LatticeChain` lemmas).** Suppose `N` is nilpotent
   modulo a prime ideal `I`. Then every coefficient of positive degree of
   `det(1 + X N)` lies in `I` by `Matrix.charpolyRev` and
   `Matrix.isUnit_charpolyRev_of_isNilpotent`. In a basis of the chain lattice `L_0`, an
   element `y ∈ 𝔓^1` has an integral matrix that is nilpotent modulo `𝔭` because
   `y^e ∈ ϖ 𝔓^0`. The filtration shifts use `LatticeChain.zpow_smul_mem_iff`.

   * `exists_det_one_add_eq` gives `det(1 + x) ∈ 1 + 𝔭^{k+1}` for `x ∈ 𝔓^{ek+1}`.
   * `exists_det_one_add_eq_trace` gives `det(1 + z) = 1 + ϖ^k (s + ϖ^k q)` for
     `z ∈ 𝔓^{ek}`, with `s = tr(ϖ^{-k} z) ∈ 𝔬` and some `q ∈ 𝔬`.
   * `not_isNilpotent_inv_pow_smul_add` shows that the scalar stratum
     `[𝔄, ek, ek - 1, ϖ^{-k}]` for `k ≥ 1` is fundamental. Nilpotence of `ϖ^{-k} + y`
     for `y ∈ 𝔓^{1-ek}` would force `det(1 + ϖ^k y) = 0`, contradicting its membership
     in `1 + 𝔭`.

2. **Upper bound.** By step 1, `det U^{ek+1}(𝔄) ⊆ U^{k+1}_K`, so `χ ∘ det` is trivial on
   `U^{ek+1}(𝔄)` by `determinantCharacter_eq_one`, which uses `a(χ) ≤ k + 1`. Choose a
   chain `𝓛` witnessing the original level `x = m/e`. Restrict its fixed vector to the
   group at index `max(m, ek) + 1`, on which the twist is trivial. This exhibits
   `max(m, ek)/e = max x k` as a level value of the twist and gives `y ≤ max x k`.
   When `x > k`, apply the bound for an inverse twist using `SmoothDualClass.twist_twist`
   and `SmoothDualClass.twist_one`. This gives `x ≤ max y k`, hence `y = x`.
3. **An adapted level-one character (`exists_isLevelOne_adapted`).** Suppose `a(χ) = k + 1`
   with `k ≥ 1`. Then `s ↦ χ(1 + ϖ^k s)⁻¹` is a homomorphism `𝔬_K → ℂˣ` that is trivial on
   `𝔭_K`. Since `ℂˣ` is divisible (`divisibleByUnitsComplex`, using `exp (log z / n)`), it
   is an injective `ℤ`-module by Baer's criterion, so this homomorphism extends to an
   additive character `ψ` of `K`. The character `ψ` has level one because it is trivial on
   `𝔭_K` and detects the nontriviality of `χ` on `U^k_K` (Library
   `exists_nontrivial_below_multiplicativeConductor`).
4. **Case `x < k` (`normalizedLevel_twist_eq_of_lt`).** Then `k ≥ 1` and `y ≤ k` by step 2.
   Suppose `y < k`, witnessed by a chain `𝓛` with `y = m/e` and `m + 1 ≤ ek`. A
   representative of `a` then has a nonzero vector `v` that is fixed by `U^{ek}(𝔄)` after
   twisting by `χ ∘ det`. For `g ∈ U^{ek}(𝔄)`, step 1 gives
   `det g = 1 + ϖ^k(s + ϖ^k q)` with `s = tr(ϖ^{-k}(g - 1))`. Since `χ` is trivial on
   `U^{k+1}_K`, we get `χ(det g) = χ(1 + ϖ^k s) = ψ(s)⁻¹`. So `g v = ψ(tr(ϖ^{-k}(g - 1))) v`,
   which means `a` contains the stratum `[𝔄(𝓛), ek, ek - 1, ϖ^{-k}]`. This stratum is
   fundamental by step 1, so L1 (`fundamentalStratumLevel`) gives
   `x = ek/e = k`. That contradicts `x < k`.
5. **Assembly (`normalizedLevelTwist`).** Step 2 gives the bound and the case `x > k`, and
   step 4 gives the case `x < k`. Normalized levels are nonnegative, so when `k = 0`
   only step 2 is needed. This covers unramified and tamely ramified characters.

Choosing `ψ` to match `χ` makes the stratum element exactly `ϖ^{-k}`. The determinant
and additive-character computations apply in every residue characteristic.

## Provenance

L2 is Lemma `lem:level`(ii) of the operator route note
(`operator-numerical-llc-route-2026-11-16`, Lemma 4.11, printed p. 16). The note proves it
from part (i), which is L1. The Lean implementation obtains the needed determinant
congruences from integral matrices and chooses `ψ` to match `χ` by extending a character
of the valuation ring. Worker 408 authored this proof in Task 7339. Worker 198 adapted it
in Task 7682 to use the published L1 theorem and shared lattice and fixed-vector lemmas.
