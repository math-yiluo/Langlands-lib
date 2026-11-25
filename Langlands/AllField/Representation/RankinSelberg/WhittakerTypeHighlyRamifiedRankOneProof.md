# Proof of highly ramified L-vanishing against a character of `GL_1`, every local field

Module `Langlands.AllField.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedRankOneProof`.

`Langlands.AllField.RankinSelberg.whittakerTypeHighlyRamifiedRankOneLVanishing.{uF,uV,uW}`
proves
[WhittakerTypeHighlyRamifiedRankOneLVanishingStatement](WhittakerTypeHighlyRamifiedRankOneStatement.md)
with no additional premises. This is JPSS 1983, Proposition (2.13), when the first
member is a representation of `GL_1`, over every nonarchimedean local field `F`,
including fields of positive characteristic. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Origin of the proof

The proof adapts the Library's p-adic proof
`Langlands.RankinSelberg.whittakerTypeHighlyRamifiedLVanishing` (module
`Langlands.Representation.RankinSelberg.WhittakerTypeHighlyRamifiedProof`; its Markdown
explains the route in detail and gives the literature provenance). The all-field port
of the Library produced a mechanical all-field version of that module. That version
was left out of the port because it uses `PrincipalUnitPowerCofinalityStatement`, whose all-field analogue is
false in positive characteristic. This module starts from that version and changes
only the conductor step, as follows.

Declarations kept from the p-adic proof, with the p-adic field and its canonical data
replaced by a field `F` with `T : LocalFieldData F` or with the instances
`[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` and the data
`⟨⟩ : LocalFieldData F` (definitionally `LocalFieldData.ofInstances F`). Their
statements and proofs are otherwise those of their originals of the same name in
`Langlands.RankinSelberg`:

- `exists_isPadicPairLPolynomial_quasicharacter_twist`,
  `determinantCharacter_rootCoordinates`;
- the equal-rank adapters `exists_equalRankRootExpansion_twist`,
  `exists_equalRankCompactRootExpansion_twist`, `exists_equalRank_ramified_laurent`;
- the zero-row unequal-rank adapters `exists_unequalRankZeroRowRootExpansion_twist`,
  `exists_unequalRankZeroRowCompactRootExpansion_twist`,
  `exists_unequalRankZeroRow_ramified_laurent`;
- `IsPadicPairLPolynomial.eq_one_of_laurent_equalRank`,
  `isPadicPairLPolynomial_twist_left_iff_right`,
  `exists_highlyRamified_symmetric_of_ordered`.

The field-independent helpers of the p-adic module, among them
`laurentContinuation_tensor_integral` and `normalizedGenerator_eq_one_of_laurent`,
are imported from it unchanged. The p-adic lemmas `isOpen_principalUnits` and
`quasicharacter_isOpen_ker` are not re-declared: the all-field
`isOfWhittakerType_quasicharacter_twist_iff` comes from the all-field
`RankOneTestReduction`. The other inputs are the all-field theorems
`Langlands.AllField.RankinSelberg.ramifiedFiniteFunctionMellin`,
`Langlands.AllField.RankinSelberg.symmetricLPolynomialExists` (both from the all-field
port), `Langlands.AllField.RankinSelberg.quotientIwasawaIntegration`,
`Langlands.AllField.RankinSelberg.modelAsymptoticTransfer` and
`Langlands.AllField.whittakerTypeAsymptotic` (from the Library's earlier
all-field modules), and the field-independent Library theorems `Langlands.RankinSelberg.finiteFunctionTensor`,
`Langlands.HarmonicAnalysis.rowTensorDecomposition` and
`Langlands.RankinSelberg.isOfWhittakerType_standard_iff_inverse`.

The declarations below are new or changed. The others with the suffixes `_rankOne` or
`_unitExponent` replace the general ones of the p-adic proof (without the suffix).

## The conductor step

`exists_uniform_ramified_tensor_integrals_unitExponent` is the p-adic
`exists_uniform_ramified_tensor_integrals` with the extra hypothesis that every
coordinate exponent `m i` equals `1`. Its scalar certificates (one level `b j i` for
each finite function `η j i`) are as in the original. The original obtained, from
`PrincipalUnitPowerCofinalityStatement`, a conductor bound making `χ^(m i)`
nontrivial on the principal units `U^(b j i)`. Here `m i = 1`, and
`LocalFieldData.exists_nontrivial_below_multiplicativeConductor` (module
`Langlands.AllField.HarmonicAnalysis.ConductorSupplement`) gives directly that a
quasicharacter `χ` of conductor at least `b j i + 1` is nontrivial on
`U^(b j i)`. Hence `A`, an upper bound of the finitely many `b j i + 1`, works for
every `χ` of conductor at least `A`. The rest of the proof is the original:
`laurentContinuation_tensor_integral` assembles the scalar certificates of
`χ^(m i)` into a convergence half-plane and a Laurent continuation of the tensor
integral.

`exists_uniform_ramified_finiteFamily_integrals_unitExponent` is the original
finite-family step under the same hypothesis `∀ i, m i = 1`: the finite-function
tensor theorem and the ramified finite-function Mellin theorem supply the scalar
certificates (the Mellin theorem's positive-exponent hypothesis holds since
`m i = 1`), and an upper bound of finitely many bounds is taken.

`exists_uniform_ramified_root_integrals_rankOne` is the root-coordinate step for the
torus of rank one only (hypothesis `n = 0`). The single root weight is
`i.val + 1 = 1`, so the previous lemma applies, with the Schwartz tensor premise
discharged by `rowTensorDecomposition F (0 + 1)`.

## Rank-one assembly

`exists_highlyRamified_ordered_pair_of_analytic_inputs_rankOne` is the original
ordered step for pairs whose smaller member is a representation of `GL_1` (hypothesis
`n = 0`). The larger member `π` of `GL_(r+1)` carries the twist. In equal rank
(`r = 0`) it applies `exists_equalRank_ramified_laurent`, in strict unequal rank
`exists_unequalRankZeroRow_ramified_laurent` with `r = 0 + (0 + k + 1)`, both with the
rank-one torus certificates of the previous section. As in the original, the common
L-polynomial `P` of each twisted pair, supplied by factor existence, satisfies
`P = 1` because the whole family of zeta values is Laurent
(`IsPadicPairLPolynomial.eq_one_of_laurent_equalRank`, respectively
`normalizedGenerator_eq_one_of_laurent`); substituting `P = 1` keeps the full
certificate, with the existence of a compatible quotient measure and validity for
every compatible quotient measure.

`exists_highlyRamified_symmetric_of_analytic_inputs_rankOne` treats the twisted
representation `π` of `GL_(0+1)` against `σ` of `GL_(n+1)` through
`exists_highlyRamified_symmetric_of_ordered`:

- if `n ≤ 0` (equal rank), the ordered step applies to `(π, σ)` with `π` twisted;
- if `0 < n`, the ordered step applies to `(σ, π)`, with the larger `σ` first and the
  rank-one `π` as smaller member. Factor existence for the twisted pair `(π ⊗ χ, σ)`,
  read in its smaller-first form, is moved to a certificate for `(σ ⊗ χ, π)` by
  `isPadicPairLPolynomial_twist_left_iff_right`, as in the original.

In both cases the smaller member has rank one, so the rank-one torus step suffices.

`whittakerTypeHighlyRamifiedRankOneLVanishing_of_analytic_inputs` supplies the
coefficient torus expansions of `π` and `σ` for the standard and inverse standard
characters (`modelAsymptoticTransfer` of `whittakerTypeAsymptotic`, at the universes
`.{uF,uV}` and `.{uF,uW}`, with `isOfWhittakerType_standard_iff_inverse`) and
`quotientIwasawaIntegration` at every rank. The final theorem
`whittakerTypeHighlyRamifiedRankOneLVanishing` applies it to
`symmetricLPolynomialExists`.

## Source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg Convolutions*
(1983), registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, Proposition (2.13),
printed page 404. Its proof writes the integrals as finite sums of torus integrals of
Schwartz functions against finite functions from a fixed finite set, and chooses the
twisting character so that every factor is ramified. With the first representation
of rank one, the torus has one coordinate and the twisting character occurs to the
first power, so a character of large conductor has this property in every
characteristic. The implemented proof follows this route through the Library
interfaces listed above.
