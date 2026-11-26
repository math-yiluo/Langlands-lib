# The ambient character shift of Eisenstein series

Module `Langlands.Global.AdelicEisensteinAmbientShiftProof` proves the two clauses of
`Langlands.Global.EisensteinAmbientShiftStatement` (module
`Langlands.Global.AdelicEisensteinAmbientShiftStatement`). It proves the clause on the defining
sum outright. It proves the clause on meromorphic continuations from
`Langlands.Global.EisensteinRegularParameterStatement`, the nonemptiness of every
regular-parameter region, which it takes as a hypothesis and does not prove.

| Declaration | Kind | Content |
| --- | --- | --- |
| `eisensteinSeriesAmbientShift` | theorem (proved) | `EisensteinSeriesAmbientShiftStatement` |
| `eisensteinContinuationAmbientShift_of_regularParameter` | theorem (proved) | `EisensteinRegularParameterStatement → EisensteinContinuationAmbientShiftStatement` |
| `eisensteinAmbientShift_of_regularParameter` | theorem (proved) | `EisensteinRegularParameterStatement → EisensteinAmbientShiftStatement` |

The remaining declarations of the module are private lemmas of these proofs.

## The defining sum

`eisensteinSeriesAmbientShift`: for `ν ∈ X^*(G) ⊗ ℂ` with pullback `p*ν = parameterRestrict p ν`
to `X^*(P) ⊗ ℂ`, `hK.eisensteinSeries φ (λ + p*ν) g = g^ν · hK.eisensteinSeries φ λ g`, where
`g^ν = parameterPower F G ν g`.

Write `g = p(q) k` with `q ∈ P(𝔸)` and `k ∈ K` (`IsIwasawaCompact.exists_eq`). The character
logarithm of `G(𝔸)` vanishes on the compact subgroup `K`
(`characterLog_eq_zero_on_compactSubgroup`) and is compatible with `p`, so
`H_G(g) = realCharacterDualMap (H_P(g))`, where `H_P = hK.height`. The pairing identity
`complexParameterPairing_parameterRestrict` and `exp(a + b) = exp a · exp b` then give
`hK.heightPower (λ + p*ν) g = hK.heightPower λ g · g^ν`. The character logarithm vanishes on
`G(F)` (`characterLog_rational`), so `(γ g)^ν = g^ν` for every rational point `γ`. Hence every
term `hK.eisensteinTerm φ (λ + p*ν) g c` of the sum is `g^ν` times the corresponding term at
`λ`, and `tsum_mul_left` moves the common factor out of the sum. The identity holds for the
Library's unconditional `tsum`, so no convergence is needed.

## Meromorphic continuations

`eisensteinContinuationAmbientShift_of_regularParameter`: let `E` be meromorphic in linear
coordinates on `X^*(P) ⊗ ℂ` with holomorphy domain `D`, equal to `λ ↦ E(φ, λ)(g)` at the
`R`-regular points of `D`, and let `Re ν = 0`. Then `E(λ + p*ν) = g^ν E(λ)` whenever `λ` and
`λ + p*ν` both lie in `D`.

1. Choose the linear chart `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` of `Module.finBasis`; translation by
   `d = e⁻¹(p*ν)` corresponds to adding `p*ν`.
2. The set `O` of `s` with `e s` `R`-regular is open (`isOpen_setOf_isRegularParameter`), and it
   is nonempty by the hypothesis `EisensteinRegularParameterStatement`.
3. Regularity depends only on real parts, and `Re (λ + p*ν) = Re λ` because `Re ν = 0`
   (`parameterRealPart_pullback`). So for `s ∈ O` with `e s` and `e (s + d)` in `D`, both values
   of `E` are values of the defining sum, and the identity is `eisensteinSeriesAmbientShift`.
4. The private lemma `eq_translate_of_eqOn_open` extends this to every `s` with `s` and `s + d`
   in the holomorphy domain. The local denominators of `E ∘ e` give local denominators of its
   translate, by composition with the translation homeomorphism, and of `g^ν · (E ∘ e)`, by
   multiplying the numerators by the constant. The uniqueness theorem
   `eq_of_hasLocalDenominators` (module `Langlands.Analysis.Meromorphic.ContinuationUniqueness`)
   applied on the connected space `ℂⁿ` gives equality on the common holomorphy domain, from
   equality near a point of `O`.

Translation is an affine bijection of the whole parameter space, so no meromorphic function is
restricted to a subspace, and nothing is asserted about values of `E` outside `D`.

`eisensteinAmbientShift_of_regularParameter` pairs the two theorems.

## Sources

The terms, heights and parameter conventions are those of Bernstein–Lapid (2024)
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), §2.1 and §2.2 (2.1),
pp.190–191; the meromorphy conventions are their §3.1, p.192. The shift identity
`E(φ, λ + ν)(g) = e^{⟨ν, H_G(g)⟩} E(φ, λ)(g)` for `ν ∈ 𝔞_{G,ℂ}^*` is the identity recalled in the
Markdown of `Langlands.Global.AdelicSpectralDecompositionReduction`, section
`RelativeWavePacketOrthogonalityStatement`. The proofs above are derived from these conventions;
they do not use Bernstein–Lapid's continuation theorem.
