# Proof of gamma multiplicativity for unramified principal series over every local field

Module `Langlands.Representation.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityProof`.

`Langlands.RankinSelberg.localFieldPrincipalSeriesGammaMultiplicativity` proves
`Langlands.RankinSelberg.LocalFieldPrincipalSeriesGammaMultiplicativityStatement.{uF, uV}`
exactly: JPSS 1983, Theorem (3.1)(i), over every nonarchimedean local field `F` of any
characteristic, for `π` of Whittaker type on `GL_(r+1)(F)` and the unramified principal
series `I(z)` of `GL_(n+1)(F)`. For every `z : Fin (n + 1) → ℂˣ` it gives gamma factors
`G i` of the pairs `(π, χ_{z_i})` whose product is a gamma factor of `(π, I(z))`, both for
the relation `IsGeneralSymmetricGammaFactor q ψ abv ν`. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Proof

The proof applies the all-field gamma multiplicativity theorem
`Langlands.AllField.RankinSelberg.gammaMultiplicativity` (module
`Langlands.AllField.Representation.RankinSelberg.GammaMultiplicativityProof`), the
all-field port of the Library's p-adic theorem `Langlands.RankinSelberg.gammaMultiplicativity`.
For a field `F` with instances `[TopologicalSpace F] [ValuativeRel F]
[IsNonarchimedeanLocalField F]`, a self-dual Haar measure `ν`, `π` of Whittaker type and
representations `σ_i` of Whittaker type of `GL_(m_i+1)(F)` (`i : Fin k`), it gives gamma
factors `G i` of the pairs `(π, σ_i)` whose product is a gamma factor of `π` against the
normalized product induction `(⟨⟩ : LocalFieldData F).normalizedProductInduced
(succBlockShape m h) σ`. Its gamma factors are those of the all-field relation
`Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor F ψ ν`. By definition, this
relation is `IsGeneralSymmetricGammaFactor` for the residue cardinality
`(LocalFieldData.ofInstances F).residueCardinality` and the absolute value
`normalizedAbsoluteValue (LocalFieldData.ofInstances F)` of the ambient data.
`⟨⟩ : LocalFieldData F` is `LocalFieldData.ofInstances F` by definition.

Steps, after introducing the binders of the statement:

1. `AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances` (Library module
   `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction`)
   shows, from `hq`, `abv ϖ = q⁻¹` and `abv x = 1` on valuation units, that `abv` is
   `normalizedAbsoluteValue (LocalFieldData.ofInstances F)`; it is substituted. Also
   `q = (LocalFieldData.ofInstances F).residueCardinality` by `hq` and
   `AllField.RankinSelberg.residueCardinality_ofInstances`.
2. Apply `AllField.RankinSelberg.gammaMultiplicativity` (universe `0` for the block
   spaces `ℂ`) with `ψ`, the self-dual measure `⟨ν, hν⟩`, ranks `r`, `t = n`, `k = n + 1`,
   block sizes `m = fun _ => 0` (so `succBlockShape m h` is
   `AllField.Conductor.UnramifiedPrincipalSeries.borelBlocks n`, the shape of `n + 1`
   blocks of size one), and the blocks `σ_i = rankOneCharacter (character hϖ (z i))`
   (`AllField.Conductor.UnramifiedPrincipalSeries.blocks hϖ n z`). Each `σ_i` is of
   Whittaker type by `AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType` applied
   to the continuous quasicharacter `χ_{z_i}`
   (`AllField.Conductor.UnramifiedPrincipalSeries.quasicharacter`).
3. The resulting `G` gives the first clause after rewriting `q` (step 1).
4. For the second clause, `IsGeneralSymmetricGammaFactor.congr_equiv` (Library module
   `Langlands.Representation.RankinSelberg.GeneralPairGamma`) transports gamma factors
   along an equivalence of the second representation. The equivalence is
   `AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv hϖ n hq z :
   I(z) ≃ (⟨⟩ : LocalFieldData F).normalizedProductInduced (borelBlocks n) (blocks hϖ n z)`
   (module `Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction`),
   and the identity on `π`. After rewriting `q`, the second clause of step 2 applies.

The instances `T2Space F` and `TotallyDisconnectedSpace F` of the statement are not
used. The Borel structure `borel F` of the statement is the one of the all-field
statements.

## The all-field port behind the proof

`Langlands.AllField.RankinSelberg.gammaMultiplicativity` is proved by the same route as
the Library's p-adic theorem: `gammaMultiplicativity_of_twoBlock` (reduction to two
blocks, by induction in stages) and `twoBlockGammaMultiplicativity` (JPSS sections 4
and 7, the dominant two-block case). This candidate adds the all-field port of every
module in this development that involves the p-adic field: 721 modules under
`Langlands/AllField/`, each with a Markdown file. 693 of them are ports of Library
modules of the same path; their Markdown names the original module, lists the
declarations and records every deviation from the original. 26 are supplements
`<module>Supplement` to modules of the Library's earlier all-field port (unequal-rank
functional equation, JPSS section 2), adding the declarations that port did not need.
Two modules are new: `IntersectionLeviDiagonalCharacter` (character
determination on the intersection Levi without `CharZero`) and
`UnramifiedPrincipalSeriesInduction` (the bridge of step 4). The existing p-adic modules
are not changed.

Most ported declarations keep the statement and proof of their originals, with the p-adic
field `F : PadicField p` and its data replaced by a field with
`T : LocalFieldData F` or with local-field instances (see each module's Markdown). The
deviations in proof route, apart from omitted rewrites between a supplied and the
canonical realization of the p-adic field, are:

- `padic_exists_ne_zero_mem_nhds_zero` (`Group/GL/MirabolicTailConullProof`) uses a
  valuation ball instead of the algebra map `ℚ_[p] → F`.
- `IntersectionLeviModulusBalance` uses `IntersectionLeviDiagonalCharacter` instead of a
  theorem with hypothesis `CharZero F`.
- Two modules (`RankOneMatrixFunctionalEquationComparisonScalarHaar`,
  `RankOneMatrixFunctionalEquationComparisonSingularNull`) obtain the nontriviality of the
  punctured neighbourhood filter at `0` from `Langlands.LocalField.nhdsNE_zero_neBot`
  instead of the canonical normed field.

The ported scope is the closure of the Library's two roots
`Langlands.RankinSelberg.gammaMultiplicativity` and
`Langlands.RankinSelberg.lFactorMultiplicativity` (JPSS (3.1)(i) and (ii)). Five modules
of the L-factor branch are not ported:

- `HarmonicAnalysis.PrincipalUnitPowerCofinalityStatement` and its proof. The
  statement is false in positive characteristic `p`: for `p ∣ m`, the `m`-th powers of
  the principal units `U^b` contain no principal unit group `U^N`.
- `RankinSelberg.WhittakerTypeHighlyRamifiedProof`, `LFactorMultiplicativityProof` and
  `TwoBlockLFactorMultiplicativityProof` depend on that statement.

The gamma-factor branch used here does not depend on these five modules.
