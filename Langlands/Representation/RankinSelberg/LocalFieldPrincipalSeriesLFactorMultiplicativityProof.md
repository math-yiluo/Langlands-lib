# Proof of L-factor multiplicativity for unramified principal series over every local field

Module `Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityProof`.

`Langlands.RankinSelberg.localFieldPrincipalSeriesLFactorMultiplicativity` proves
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesLFactorMultiplicativityStatement.{uF, uV}`
exactly: JPSS 1983, Theorem (3.1)(ii), over every nonarchimedean local field `F` of any
characteristic, for `π` of Whittaker type on `GL_(r+1)(F)` and the unramified principal
series `I(z)` of `GL_(n+1)(F)`. For every `z : Fin (n + 1) → ℂˣ` it gives the
L-polynomial `P` of `(π, I(z))`, the L-polynomials `Pi i` of the pairs `(π, χ_{z_i})`,
all for the relation `IsGeneralSymmetricLPolynomial q ψ abv ν`, and `Q : ℂ[X]`, `e : ℕ`
with `X ^ e * ∏ i, Pi i = Q * P`. It has no additional premises. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Proof

The proof applies the all-field theorem
`Langlands.AllField.RankinSelberg.lFactorMultiplicativity` (module
`Langlands.AllField.Representation.RankinSelberg.LFactorMultiplicativityProof`), the
all-field version of the Library's p-adic `Langlands.RankinSelberg.lFactorMultiplicativity`.
For a field `F` with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, a self-dual Haar measure `ν`, `π` of Whittaker type and
representations `σ_i` of Whittaker type of `GL_(m_i+1)(F)` (`i : Fin k`), it gives `P`
for `π` against the normalized induction
`(⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ`, the `Pi i` for
`(π, σ_i)` and the relation `X ^ e * ∏ i, Pi i = Q * P`. Its L-polynomials are those of
the all-field relation `Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν`.
By definition, this relation is `IsGeneralSymmetricLPolynomial` for the residue
cardinality `(LocalFieldData.ofInstances F).residueCardinality` and the absolute value
`normalizedAbsoluteValue (LocalFieldData.ofInstances F)` of the ambient data, and
`⟨⟩ : LocalFieldData F` is `LocalFieldData.ofInstances F` by definition.

Steps, after introducing the binders of the statement:

1. `AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances` (Library module
   `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction`)
   shows, from `hq`, `abv ϖ = q⁻¹` and `abv x = 1` on valuation units, that `abv` is
   `normalizedAbsoluteValue (LocalFieldData.ofInstances F)`; it is substituted. Also
   `q = (LocalFieldData.ofInstances F).residueCardinality` by `hq` and
   `AllField.RankinSelberg.residueCardinality_ofInstances`.
2. Apply `AllField.RankinSelberg.lFactorMultiplicativity` at universes `uF, uV, 0`
   (universe `0` for the block spaces `ℂ`) with `ψ`, the self-dual measure `⟨ν, hν⟩`,
   ranks `r`, `t = n`, `k = n + 1`, block sizes `m = fun _ => 0` (so that
   `succBlockShape m h` is the shape of `n + 1` blocks of size one), and the blocks
   `σ_i = rankOneCharacter (character hϖ (z i))`
   (`AllField.Conductor.UnramifiedPrincipalSeries.blocks hϖ n z`). Each `σ_i` is of
   Whittaker type by `AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType` applied
   to the continuous quasicharacter `χ_{z_i}`
   (`AllField.Conductor.UnramifiedPrincipalSeries.quasicharacter`). This gives `P`, `Pi`,
   their certificates, `Q`, `e` and the polynomial identity, which is the third clause
   unchanged.
3. For the first clause, `IsGeneralSymmetricLPolynomial.congr_equiv` (Library module
   `Langlands.Representation.RankinSelberg.GeneralPairLFactor`) transports L-polynomials
   along equivalences of the two representations: the identity on `π` and
   `AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv hϖ n hq z`, an
   equivalence of `I(z)` with the normalized induction of the blocks of step 2
   (module `Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction`,
   part of the all-field port). After rewriting `q` (step 1), the certificate
   `P` of step 2 applies.
4. The second clause is the certificate of `Pi i` of step 2 after rewriting `q`.

The instances `T2Space F` and `TotallyDisconnectedSpace F` of the statement are not
used. The Borel structure `borel F` of the statement is the one of the all-field
statements.

## The all-field theorem behind the proof

`Langlands.AllField.RankinSelberg.lFactorMultiplicativity` follows the Library's p-adic
proof: reduction to two blocks by induction in stages
([LFactorMultiplicativityProof](../../AllField/Representation/RankinSelberg/LFactorMultiplicativityProof.md)),
and the two-block theorem by the descent of JPSS Section 7
([TwoBlockLFactorMultiplicativityProof](../../AllField/Representation/RankinSelberg/TwoBlockLFactorMultiplicativityProof.md)).
Its modules are those of the all-field port of every module of this
development that involves the p-adic field, together with the following, ported
together with this module:

- [WhittakerTypeHighlyRamifiedRankOneStatement](../../AllField/Representation/RankinSelberg/WhittakerTypeHighlyRamifiedRankOneStatement.md)
  and
  [WhittakerTypeHighlyRamifiedRankOneProof](../../AllField/Representation/RankinSelberg/WhittakerTypeHighlyRamifiedRankOneProof.md):
  JPSS Proposition (2.13) when the first member is a representation of `GL_1`, over
  every local field. The Library's p-adic proof of the full proposition does not carry
  over to positive characteristic: it needs the powers `χ^i` of the twisting character,
  `i` up to the smaller rank, to be nontrivial on a fixed principal-unit group, which a
  large conductor does not guarantee in characteristic `p` when `p` divides `i`. With
  the first member of rank one only `χ^1` occurs.
- A change to the all-field modules `TwoBlockLConditionalAssembly` and
  `TwoBlockLVerifiedInputAssembly` of the port: their high-ramification
  hypothesis is this rank-one proposition instead of the full one. The descent uses it
  only with first member `rankOneCharacter 1`, so the proofs are unchanged (each
  module's Markdown describes the change).
- The ports of `TwoBlockLFactorMultiplicativityProof` and `LFactorMultiplicativityProof`,
  which the rest of the port left out because they depended on the full proposition.

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions* (1983),
registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, Theorem (3.1)(ii),
printed pages 404-405; Section 0.3 (printed page 375) allows any nonarchimedean local
field. The Markdown of the statement explains how its polynomial identity and the
upper-Borel principal series correspond to the source.
