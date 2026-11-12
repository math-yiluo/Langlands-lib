# Proof that normalized `Φ⁻` preserves unitarizability

Author: Worker 4876 (proof). Submitted by Worker 112 for Task 5634
(`a8033d39-4d44-4cc0-a1f9-955b70f21a0f`).

This module proves the published proposition
`Langlands.Derivative.MirabolicPhiMinusUnitarity` (module
`Langlands.Representation.Derivative.MirabolicPhiMinusUnitarityStatement`,
statement candidate `b9c07414-c672-4213-9268-3111335c5b0e`, by Worker 596). The
statement pair is imported unchanged.

## Main declaration

```lean
theorem Langlands.Derivative.Mirabolic.mirabolicPhiMinusUnitarity.{uF, uV}
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicPhiMinusUnitarity.{uF, uV} F T
```

The universes `uF` and `uV` are independent. There are no further premises,
instances or universe equalities. Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

In words: for every unitary additive character `ψ`, every `m : ℕ` and every
smooth complex representation `X` of `P_(m+2)` (`mirabolic (m + 1)`) with carrier
in `Type (max uF uV)`, if `X` has an invariant positive definite Hermitian form,
then so does normalized `Φ⁻ X`, a representation of `P_(m+1)`.

## Provenance and route

The statement is the forward half of Bernstein 1984, §9.3(ii) (printed p. 97):
invariant positive forms on `X` restrict to the open-orbit part `E₀`, and these
correspond to invariant positive forms on the fiber `Φ⁻ X`. The Lean proof does
not use the sheaf model `E₀` or Bernstein's correspondence. It builds the form on
`Φ⁻ X` directly by the twisted radical integral already used in the Library for
Bernstein–Zelevinsky pairings
(`MirabolicMinusPairingTransferProof`, `MirabolicPhiMinusNondegeneratePairing`),
and proves positivity by a character average. The proof route is internal; only
the statement is taken from the source.

Notation: `⟪·, ·⟫` is the given invariant form on `X`, `u(c)` the radical element
with coordinates `c ∈ F^(m+1)`, `θ_ψ(u(c)) = ψ(c_last)`, and `X(V)` the radical
relations `span {u x - x}`, written `relations ρ (radical (m + 1) F.Carrier) 1`
and carrying the representation `radicalPart ρ`.

## Proof

1. **Descent of a Hermitian form** (`descended_eq`, `descendedCore`,
   `descendedCore_inner`). If `I : V → V → ℂ` is additive and conjugate-linear in
   the first variable, Hermitian, vanishes when the second argument lies in the
   kernel of a surjection `q : V → Q`, has `0 ≤ re I(x, x)`, and `I(x, x) = 0`
   implies `q x = 0`, then `I` descends to an `InnerProductSpace.Core` on `Q`
   with `⟪q x, q y⟫ = I(x, y)`.

2. **Hermitian forms as pairings** (`conjPairing`, `conjPairing_invariant`,
   `isSmooth_conjRep`, `restrictForm`). A Hermitian form is the bilinear pairing
   `β(y, x̄) = ⟪x, y⟫` of `V` with its conjugate space `ConjSpace V`; an invariant
   form gives an invariant pairing of `ρ` with the conjugate representation,
   which is smooth when `ρ` is. An invariant positive form restricts to a stable
   submodule.

3. **The form on the coinvariants** (`exists_coinvariantCore`). Let `ξ` be a
   smooth representation of `P_(m+2)` with an invariant positive form `b` whose
   radical coefficients `c ↦ ⟪y, u(c) x⟫` are supported in a lattice box for all
   `x, y`. Then the coinvariant space of `ξ` for `(radical, θ_ψ)` has an inner
   product `B` with `B(h·x, h·y) = |det h| B(x, y)` for the successor action of
   `h ∈ P_(m+1)`. The proof sets, with `μ` the additive Haar measure on
   `F^(m+1)`,

   `I(x, y) = ∫ ψ(-c_last) ⟪x, u(c) y⟫ dμ(c)`

   (the Library's `transferForm` for the pairing `conjPairing b`), and checks the
   hypotheses of step 1 for the quotient map `mk`:
   * Hermitian: conjugating the integrand and substituting `c ↦ -c`
     (`integral_conj`, `integral_neg_eq_self`, invariance of `b` under `u(-c)`);
   * kernel: `transferIntegral_radical_left` gives
     `I(x, u(d) y) = ψ(d_last) I(x, y)`, so `I(x, ·)` kills the `θ_ψ`-relations
     (`relations_le_ker_iff`);
   * positivity and definiteness: given `x`, choose `N` with
     `⟪x, u(c) x⟫ = 0` off the box `latticeBox T (m + 1) N`, and let `x'` be the
     `θ_ψ`-average of `x` over the radical box `radicalBox T m N`
     (`characterAverage`). Then `x' ≡ x` in the coinvariants
     (`sub_characterAverage_mem`), `u(d) x' = ψ(d_last) x'` on the box
     (`Compact.averageMap_mem_fixedVectors`), and `⟪x', u(c) x'⟫ = 0` off the box
     (through `apply_characterAverage` and `orbitMean_mem`, using the support of
     `⟪x, u(·) x⟫`). Hence the integrand for `I(x', x')` is the indicator of the
     box times `⟪x', x'⟫` (`integral_indicator_const`), so
     `I(x, x) = I(x', x') = vol(box) ⟪x', x'⟫` with `vol(box) > 0`. This gives
     `0 ≤ re I(x, x)`, and `I(x, x) = 0` forces `x' = 0`, so the class of `x` is
     zero;
   * covariance: `transferIntegral_levi` with exponent `s = 0` and the Haar
     scaling `padicScalarHaarScaling` / `haarMeasure_map_matrix` give
     `I(h·x, h·y) = |det h| I(x, y)` for the successor action, which is the Levi
     action of `h` viewed in `GL_(m+1)`: the last row of `h ∈ P_(m+1)` is the
     last unit vector, so `(h c)_last = c_last` (`mulVec_last`) and the character
     in the integrand is unchanged.

4. **Compact support on `X(V)`** (`restrictForm_radical_support`). On the radical
   relations of a smooth `X`, the radical coefficients of the restricted form have
   compact support: this is the Library's `exists_coefficient_support_of_mem`
   applied to `conjPairing b` with `s = 0`.

5. **Transport to `Φ⁻ X`** (`coreComap`, `radicalPartEquiv`,
   `radicalPartEquiv_symm_mk`, `radicalPartEquiv_symm_mk_successor`,
   `exists_phiMinusCore`). The inclusion `X(V) ⊆ X` induces a linear isomorphism
   of coinvariants `Φ⁻ X(V) ≅ Φ⁻ X` (`radicalPartMap`, bijective by
   `radicalPartMap_injective` and `radicalPartMap_surjective`). Step 3 for
   `ξ = radicalPart X` and the restricted form, with step 4 as the support
   hypothesis, gives an inner product on `Φ⁻ X(V)`; pulled back along the inverse
   isomorphism, it is an inner product `B` on the coinvariants of `X` with
   covariance `|det h|` under the successor action
   (`exists_mk_radicalRelations_eq` represents each class by an element of
   `X(V)`; `relations_stable` shows that the successor action preserves the
   relation between representatives).

6. **Normalization** (`phiMinusCharacter_conj_mul_mul`, final theorem). Normalized
   `Φ⁻ X` acts on the same coinvariant space by the descended successor action
   times `|det h|^(-1/2)` (`phiMinus_action`; every vector is a class by
   `phiMinusQuotient_surjective`). For the inner product `B` of step 5,
   `B(h·a, h·a') = conj(|det h|^(-1/2)) |det h|^(-1/2) |det h| B(a, a') = B(a, a')`,
   so `B` with this invariance is an `InvariantPositiveForm` on normalized
   `Φ⁻ X`, which is `IsUnitarizable`.

## Remarks

The zero representation needs no separate case: `InnerProductSpace.Core` on the
zero space exists. No finite-length, admissibility or homogeneity hypothesis is
used.
