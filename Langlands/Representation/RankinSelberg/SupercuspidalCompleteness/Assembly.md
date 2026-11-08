# Assembly of Whittaker completeness against products of supercuspidals

Internal module for the proof of
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`.

## The pairing input

`DeltaPairingStatement` is a proposition definition. It uses the same data and instance context
as the target statement:
- `p`, `F` with its canonical topology, `ψ`, `n`;
- the Borel structures and a quotient measure `μ` compatible with `generalLinearHaar` and
  `unipotentHaar`.

For every smooth representation `π` of `GL_(n+1)(F)` on a carrier `E`, and every bilinear form
`β` on `GelfandGraevFunctions ψ n × E` that is invariant under `G`, it provides
`ℓ' ∈ glInverseFunctionals ψ n π` such that

`β x e = ∫ whittakerProductIntegrand ψ (toWhittaker ψ n x) (coefficientMap π ℓ' e) dμ`.

This is the identification of invariant pairings with the compactly induced representation:
`Hom_G(Π, (c-Ind_N^G ψ)^∨) = Hom_N(Π, ψ̄)`, realized by delta functions on `N K` for small
compact open `K`. It is proved as `deltaPairing` in `DeltaPairingGL`.

## Generic dual pairing

The generic lemmas use these data:
- an intertwiner `Tf : ρ → π0`;
- an equivalence `e : π0^∨ ≃ κ` of representations, where `π0^∨` is the smooth contragredient.

From them:
- `dualPairing ρ π0 κ Tf e x φ = e⁻¹(φ)(Tf x)` is bilinear;
- `dualPairing_invariant` shows it is `G`-invariant;
- `dualPairing_self` gives `dualPairing x (e λ) = λ(Tf x)`.

`cast_rep_prop` transports properties of a representation of `GL_a` along an equality `a = b`.

## Main theorem

`supercuspidalProductCompleteness_of hJ hδ : SupercuspidalProductCompletenessStatement.{uF, uW}`
holds for `hJ : GelfandGraevJacquetStatement` and `hδ : DeltaPairingStatement.{uF, max uF uW}`.

The proof argues by contradiction. Let `H ≠ 0` satisfy the hypotheses.
1. Write `H = toWhittaker h` (`exists_toWhittaker_eq`).
2. `exists_frobenius_ne_zero` gives `B`, supercuspidal blocks `A i` and
   `Tf : c-Ind_N^G ψ → Π0 = normalizedProductInduced B (A i)` with `Tf h ≠ 0`.
3. Choose a smooth functional `λ` of `Π0` with `λ(Tf h) ≠ 0`
   (`CompactSplitting.exists_smooth_functional_ne_zero`, using
   `GeneralLinear.compactOpen_cofinal`).
4. The smooth dual of `Π0` is equivalent to the normalized product of the contragredients
   (`Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv`).
   Rewriting the block sizes as `m i + 1`
   (`RankinSelberg.Padic.normalizedProductInducedEquiv_of_sizes`) identifies it with
   `Π = F.canonicalNormalizedProductInduced (succBlockShape m hm) τ`, where `τ i` is the
   contragredient of `A i`.
5. Each `τ i` qualifies as a test block:
   - it is smooth (`isSmooth_smoothContragredient`);
   - it is irreducible (`CompactSplitting.isIrreducible_smoothContragredient`);
   - it is supercuspidal (`GeneralLinear.isSupercuspidal_smoothContragredient`).
   Its carrier lies in universe `uW`.
6. `dualPairing` gives a `G`-invariant pairing `β` on `c-Ind_N^G ψ × Π` with
   `β(h, φ0) = λ(Tf h) ≠ 0`, where `φ0` is the image of `λ`.
7. `DeltaPairingStatement` writes `β(h, φ0)` as the integral of `H` against the coefficient
   function of `φ0` for some inverse-character functional `ℓ'` of `Π`. The hypothesis of the
   target, applied to this test, says the integral vanishes. This is a contradiction.
