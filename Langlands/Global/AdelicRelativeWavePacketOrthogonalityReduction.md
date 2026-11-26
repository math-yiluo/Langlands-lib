# Orthogonality of non-associate relative wave packets on `[G]`: the transfer from `G(F) \ G(𝔸)`

Module `Langlands.Global.AdelicRelativeWavePacketOrthogonalityReduction` proves that
`Langlands.Global.RelativeWavePacketOrthogonalityStatement` (module
`Langlands.Global.AdelicSpectralDecompositionReduction`) follows from the orthogonality of wave
packets of non-associate parabolics on `G(F) \ G(𝔸)` and three further propositions. It proves
none of these premises.

| Declaration | Kind | Provenance |
| --- | --- | --- |
| `RelativeWavePacketOrthogonalityTransferStatement` | statement | derived: the implication proved below |
| `ambientProfileQuotientLift_eq_of_descent` | theorem (proved) | internal |
| `relativeWavePacketOrthogonality_of_inputs` | theorem (proved) | the passage from `G(F) \ G(𝔸)` to `[G]` |
| `relativeWavePacketOrthogonalityTransfer` | theorem (proved) | proves `RelativeWavePacketOrthogonalityTransferStatement` |
| `relativeWavePacketOrthogonality_of_innerProduct` | theorem (proved) | the same, from Lapid's Proposition 2 |

## The statement

`RelativeWavePacketOrthogonalityTransferStatement` is the implication

`NonAssociateWavePacketOrthogonalityStatement → EisensteinRegularParameterStatement.{0} →
LeftCosetSpace.ProductQuotientMeasureStatement.{0, 0, 0} → RelativeWavePacketDescentStatement →
RelativeWavePacketOrthogonalityStatement`.

Its premises are:

1. `NonAssociateWavePacketOrthogonalityStatement` (module
   `Langlands.Global.AdelicNonAssociateWavePacketOrthogonality`): Lapid 2011, Proposition 2, with
   `Ω(P, P') = ∅`. Wave packets of non-associate presented parabolics over all of `i𝔞_P^*` and
   `i𝔞_{P'}^*` (`IsParabolicWavePacket`) are in `L²(G(F) \ G(𝔸))` and orthogonal there. That
   module derives it from `WavePacketInnerProductStatement`
   (`nonAssociateWavePacketOrthogonality_of_innerProduct`).
2. `EisensteinRegularParameterStatement` (module
   `Langlands.Global.AdelicEisensteinRegularParameterStatement`): every region of `R`-regular
   parameters of a presented parabolic is nonempty.
3. `LeftCosetSpace.ProductQuotientMeasureStatement` (module
   `Langlands.Global.LeftCosetProductMeasureStatement`): let `A`, `N` and `G` be groups with
   topologies, each carrying its Borel σ-algebra (`BorelSpace`), with `N` and `G` second
   countable topological groups; let `H ≤ N` and `Γ ≤ G` be discrete subgroups and
   `E : A × N ≃ G` an isomorphism of topological groups with `E(a, n) ∈ Γ` exactly when `a = 1`
   and `n ∈ H`; let `μA` on `A` and `μN` on `N` be s-finite and `μG` a measure on `G` invariant
   under left multiplication by `Γ`, such that `E` is measure preserving from `μA × μN` to `μG`.
   Then the induced homeomorphism `Γ \ G ≃ A × (H \ N)`, `[E(a, n)] ↦ (a, [n])`, is measure
   preserving from the count-normalized quotient of `μG` (`discreteQuotientMeasure`) to the
   product of `μA` and the count-normalized quotient of `μN`.
4. `RelativeWavePacketDescentStatement` (module
   `Langlands.Global.AdelicRelativeWavePacketDescentStatement`): a relative wave packet `Θ` is
   left invariant under `A_G G(F)` and `Θ([g].out) = Θ(g)` for the representatives of `[G]`.

Premises 2–4 enter only through the transfer from `G(F) \ G(𝔸)` to `[G]`.

## Proof (as implemented)

`ambientProfileQuotientLift_eq_of_descent`: if `Θ([g].out) = Θ(g)` for every `g`, the lift
`ambientProfileQuotientLift hG eG b (y ↦ Θ(y.out))` is `q ↦ profile(q.out) · Θ(q.out)`: write
`q = [q.out]` (`Quotient.out_eq`) and apply the representative formula (clause 2 of
`WavePacketProductPairingStatement`).

`relativeWavePacketOrthogonality_of_inputs` derives the target from premise 1, premise 4,
`WavePacketParabolicAmbientLiftStatement` and `WavePacketProductPairingStatement`. Given the data
of the target, with relative wave packets `Θ` of `P` and `Θ'` of `P'` whose representative
functions `f = Θ ∘ out` and `f' = Θ' ∘ out` are in `L²([G])`:

1. Take the chart `eG = ambientParameterChart hG` (module
   `Langlands.Global.AdelicRelativeAmbientParameterProduct`) and `b = spectralBump _` (module
   `Langlands.Global.AdelicSpectralBump`), smooth, compactly supported, with `b 0 = 1`, so `b ≠ 0`.
   The same `eG` and `b` serve both parabolics.
2. By `WavePacketParabolicAmbientLiftStatement`, `Φ = profile · Θ` and `Φ' = profile · Θ'` are wave
   packets of `P` and `P'` over `i𝔞_P^*` and `i𝔞_{P'}^*`.
3. By premise 1 and the hypothesis that no rational point and no `c : M' → M` satisfy
   `IsWeylConjugation p l p' l' w c`, `∫ Φ(q.out) · conj Φ'(q.out) dq = 0` on `G(F) \ G(𝔸)`, for the
   count-normalized quotient of Mathlib's Haar measure, which is `rationalQuotientHaarMeasure F G`.
4. By premise 4 and `ambientProfileQuotientLift_eq_of_descent`, the lifts of `f` and `f'` are
   `q ↦ Φ(q.out)` and `q ↦ Φ'(q.out)`. Clause 4 of `WavePacketProductPairingStatement` gives
   `0 = c · ∫_{[G]} f · conj f'` with `c > 0` (clause 1), so
   `∫_{[G]} Θ(y.out) · conj Θ'(y.out) dy = 0`.

`relativeWavePacketOrthogonalityTransfer` supplies the two remaining inputs from premises 2 and 3:
`wavePacketParabolicAmbientLift_of_regularParameter` (module
`Langlands.Global.AdelicWavePacketParabolicAmbientLiftProof`) gives
`WavePacketParabolicAmbientLiftStatement` from premise 2, and
`principalQuotientProductMeasure_of_productQuotientMeasure` (module
`Langlands.Global.AdelicPrincipalQuotientProductMeasureProof`) followed by
`wavePacketProductPairing_of_productMeasure` (module
`Langlands.Global.AdelicWavePacketProductPairingProof`) gives `WavePacketProductPairingStatement`
from premise 3.

`relativeWavePacketOrthogonality_of_innerProduct` replaces premise 1 by
`WavePacketInnerProductStatement`, through `nonAssociateWavePacketOrthogonality_of_innerProduct`.

The theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Relation to the sources

Lapid 2011 (`lapid-2011-asymptotic-inner-product-truncated-eisenstein`), §3, Proposition 2 and
(4), printed p.314 (PDF p.323), works on `G(F) \ G(𝔸)` with parameters in `i𝔞_P^*`; Arthur 2005
(`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`), Theorem 7.2(b), printed p.35
(PDF p.47), likewise. Getz–Hahn (2024) (`getz-hahn-2024-automorphic-representations`), §10.5,
printed pp.281–282 (PDF pp.293–294), works on `[G]` with parameters in `i(𝔞_M^G)^*`. The Markdown
of `Langlands.Global.AdelicSpectralDecompositionReduction`, section
`RelativeWavePacketOrthogonalityStatement`, describes the passage between them: tensor the
relative data with an ambient coefficient, so that the full wave packet is the relative one times
the Fourier transform of the coefficient, and factor the inner product on
`G(F) \ G(𝔸) ≅ A_G × [G]` (Getz–Hahn §2.6, Lemma 2.6.2 and (2.19)–(2.22), printed pp.68–69,
PDF pp.85–86). The proof above implements this passage with one nonzero coefficient `b`.
