# Every-place cuspidal support for automorphic representations of `GL_n`

`Langlands.Global.cuspidalSupportEveryPlace` proves
`Langlands.Global.CuspidalSupportEveryPlaceStatement.{u}`. The one ordered tuple
of actual cuspidal realizations and spectral presentations in universes `u, u`
supplies the finite, real and complex constituents of the given irreducible
automorphic operator subquotient.

## Proof

The proof applies `cuspidalSupportEveryPlace_of_realCuspidalParameters` from
`CuspidalSupportCommonRealizationProof`. The common realization comes from a
translated constant term on a cyclic source for the subquotient. The selected
period has a central eigencharacter and vanishing strict refinements. Its Levi
coefficients are unitarized for decomposition into cuspidal factors, and a
single projection tuple is selected while retaining the quotient. The restored
coefficients and the inverse half-modulus twist give normalized induction for
this tuple.

At finite places, the normalized finite section subquotient gives the required
local constituents and sphericity outside a finite set. At a real or complex
place, separating coefficient probes embed the common quotient source into
the standard module of the ordered block concatenation tensored with a
multiplicity space. The embedding respects the compact and Lie actions. The
finite-support tensor argument extracts a stable subspace of one copy of the
standard module and an equivariant map with nonzero image in the original
subquotient. Compact admissibility passes to that image. Minimizing the
multiplicity of a detecting compact type gives an irreducible stable subspace
of the image. Restricting to its preimage gives the required standard
constituent map. The complex branch uses
`exists_cuspidalComplexPlaceParameter`.

For the real branch, `realCuspidalParameters` in
`CuspidalSupportRealParameterBridge` uses the principal-series quotient theorem
and `realLanglandsFromPrincipalSeries` to obtain a nonzero intertwiner from a
standard module in Langlands order. The infinitesimal-character theorem and Kostant's
Whittaker theorem give maximal faithfulness for an irreducible admissible
generic module. `realLargeLanglandsQuotientInjective` then gives injectivity
of the intertwiner. `realGenericStandardParameterReduction` combines these
steps. At a given real place of a cuspidal realization,
`cuspidalArchimedeanGenericComponentBridge` uses the admissible component
and Whittaker theorems to produce an irreducible admissible generic submodule.
`OperatorRealization.hasRealPlaceParameter_of_component` composes the standard
module embedding with its inclusion into the realization.

## Provenance

The common realization formalizes the forward direction of Langlands,
*On the notion of an automorphic representation* (1979), Proposition 2 and
Lemmas 4–6, printed pp. 204–205 (registered PDF pp. 199–200,
`langlands-1979-notion-automorphic-representation`). The passage to local
constituents follows the finite-support tensor argument of Lemma 1, printed
p. 203 (PDF p. 198), as in the second half of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Theorem 10.7.1 and its remark, printed
pp. 286–287 (PDF pp. 298–299, `getz-hahn-2024-automorphic-representations`).
The real parameter step uses the principal-series and standard-quotient route
documented in `RealLanglandsQuotientReduction` and
`RealGenericParameterReduction`. The source for the ordered real parameters
is Knapp, *Local Langlands correspondence: the archimedean case* (1994),
Theorem 1(a), printed p. 400 (PDF p. 410, `knapp-1994-archimedean-llc`).
Maximal faithfulness uses Kostant, *On Whittaker vectors and representation
theory* (1978), Theorem 3.9. The large-quotient criterion follows Vogan,
*Gelfand–Kirillov dimension for Harish-Chandra modules* (1978),
Theorem 6.2, printed p. 89, specifically (a) ⇒ (f), p. 93. The implemented
proofs of these two inputs are documented in
`RealWhittakerMaximallyFaithfulProof` and
`RealLargeLanglandsQuotientInjectiveProof`.
