# The conductor–discriminant formula: proof

This module proves `Langlands.Ramification.Padic.FiniteConductorDiscriminantStatement`
(`ConductorDiscriminantStatement`):

```lean
theorem finiteConductorDiscriminant : FiniteConductorDiscriminantStatement.{uK, uM, uι}
```

with the statement's level parameters in its order.

## Proof outline

1. **The regular character** (generic, `sum_finrank_mul_artinConductor`). For a finite group `G`
   acting faithfully on a Noetherian local ring `R`, let `δ(g) = |G|` for `g = 1` and `0`
   otherwise. It is a class function, and its pairing with an irreducible character `χ` is
   `|G|⁻¹ χ(1⁻¹) |G| = χ(1)`. By completeness of the irreducible characters
   (`FiniteRep.CharacterCompleteness.eq_sum_pairing_smul`), `δ = Σ_χ χ(1) χ`. The Artin functional is
   linear and takes the value `a(χ)` on `χ` (`artinFunctional_character`), so
   `Σ_χ χ(1) a(χ) = artinFunctional(δ) = |G_0|⁻¹ Σ_g i_G(g)(δ(1) − δ(g)) = (|G|/|G_0|) Σ_g i_G(g)
   = [G:G_0] Σ_g i_G(g)`.
2. **Depths and Hilbert's exponent** (`sum_lowerDepth_eq`). If `G_N = 1`, `Σ_g i_G(g)` (the term
   `g = 1` is `0`) is `Σ_{g≠1}` of the number of `i < N` with `g ∈ G_i`
   (`lowerCount_eq_lowerDepth`), which is `Σ_{i<N} (|G_i| − 1)`
   (`TopLayer.sum_lowerDepth_erase_one`, `LocalFactor/DeligneHenniartTopLayerDifferent`).
3. **Residue degree** (`inertiaDeg_eq_index`). `G` is a Galois group of `O_M` over `O_K`
   (`TopLayer.isGaloisGroup_integers`), `m_M` is the only prime over `m_K`, and Mathlib's fundamental
   identity `#primes · e · f = |G|` (`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`)
   with `e = |inertia| = |G_0|` (`Ideal.card_inertia_eq_ramificationIdxIn`,
   `TopLayer.lowerRamificationGroup_zero_eq_inertia`) gives `f · |G_0| = |G| = [G:G_0] · |G_0|`, so
   `f = [G:G_0]`.
4. **Clause 1.** Hilbert's formula `𝔇_{M/K} = m_M ^ D`, `D = Σ_{i<N}(|G_i| − 1)`
   (`TopLayer.differentIdeal_eq_maximalIdeal_pow`) and the discriminant–different relation
   `𝔡 = m_K ^ (f D)` (`LocalField.DiscriminantDifferent.span_discr_eq_maximalIdeal_pow`,
   `LocalField/DVRDiscriminantDifferentProof`, applied to `O_K → O_M`; the finiteness, integral
   closure and residue-separability inputs are those of the Hilbert formula's proof:
   `LocalClassField.UniverseZero.relativeIntegerStructure`, finite residue fields), with `f = [G:G_0]`.
5. **Clause 2.** `∏_χ (m_K^{a(χ)})^{χ(1)} = m_K^{Σ_χ a(χ) χ(1)}`, and by steps 1 and 2 (for the integer
   action, where the generic Artin expression is the p-adic one and equals the exponent,
   `artinExponent_cast`) `Σ_χ χ(1) a(χ) = [G:G_0] D`; clause 1 with any `N` such that `G_N = 1`
   (`exists_lowerRamificationGroup_eq_bot`) concludes.

## Declarations, in order

- `Langlands.Ramification.sum_finrank_mul_artinConductor (R G) [Fintype (FiniteRep.IrreducibleClass G)] :
  ∑ a, (finrank ℂ a.out : ℂ) * ((artinConductor R G a.out.ρ : ℚ) : ℂ) =
    ((lowerGroup R G 0).index : ℂ) * ∑ g, (lowerDepth R G g : ℂ)`
  (`R` a Noetherian local ring with a faithful action of the finite group `G`).
- `Langlands.Ramification.Padic.sum_lowerDepth_eq (TM) [Fintype G] {N} (hN : lowerRamificationGroup TM K.Carrier N = ⊥) :
  ∑ g, Ramification.lowerDepth TM.Integers G g = ∑ i ∈ Finset.range N, (lowerGroupOrder TM K.Carrier i - 1)`
  (with the integer action).
- `Langlands.Ramification.Padic.inertiaDeg_eq_index (TK TM) [IsGalois K.Carrier M.Carrier] :
  (maximalIdeal TM.Integers).inertiaDeg TK.Integers = (inertia TM K.Carrier).index`.
- `Langlands.Ramification.Padic.finiteConductorDiscriminant : FiniteConductorDiscriminantStatement`.

## Literature

Serre, *Local Fields*, GTM 67, 1979: IV §1 Proposition 4 (Hilbert's formula), printed p. 64;
VI §2, the proof of Proposition 4 (`a_G(1) = f v_L(𝔇) = v_K(𝔡)`), printed p. 101; VI §3, Corollaries 1
and 2 of Proposition 6, printed p. 104. Serre obtains Corollary 2 from Proposition 6 (b) for
`ψ = 1_H`, `H = {1}`, through the transitivity of the discriminant; the Library's proof computes the
Artin conductor of the regular character directly and uses Hilbert's formula and the
discriminant–different relation instead. Serre, *Linear Representations of Finite Groups*, GTM 42,
1977, §2.4, Proposition 5 and its Corollaries 1–2 (the regular character `r_G = Σ_χ χ(1) χ`),
printed p. 18.
