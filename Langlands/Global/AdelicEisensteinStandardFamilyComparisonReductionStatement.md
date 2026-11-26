# Inputs of the regular-patch Eisenstein comparison for finite families

Module `Langlands.Global.AdelicEisensteinStandardFamilyComparisonReductionStatement` states
`Langlands.Global.StandardEisensteinFamilyComparisonReductionStatement` as a proposition. It
supplies no proof.

The proposition is the implication

`EisensteinMeromorphicContinuationStatement → LeadingCuspidalInjectivityStatement →
ConvergentCuspidalTestExpansionStatement → CuspidalProjectionDecompositionStatement →
LeviCuspFormPairingMajorantStatement → StandardEisensteinFamilyComparisonStatement`,

all at the same universe `u`. Its premises are, in order:

1. the meromorphic continuation of Eisenstein series in the uniform-growth Fréchet spaces
   (module `Langlands.Global.AdelicEisensteinContinuationStatement`);
2. the injectivity of global leading cuspidal components (module
   `Langlands.Global.AdelicLeadingCuspidalInjectivityStatement`);
3. the convergent expansion of the norm-one Levi tests of constant terms of Eisenstein series,
   formula (6.20) (module `Langlands.Global.AdelicConvergentCuspidalTestExpansionStatement`);
4. the existence and uniqueness of cuspidal projections of nested constant terms with finite
   exponent decompositions (module `Langlands.Global.AdelicCuspidalProjectionDecompositionStatement`);
5. integrable weighted majorants of Levi cusp forms (module
   `Langlands.Global.AdelicLeviCuspFormMajorantStatement`).

The conclusion is the comparison on a regular patch for finite families of inducing data in the
standard setting (module `Langlands.Global.AdelicEisensteinStandardFamilyComparisonStatement`).

## Source

Provenance: derived. These are the inputs of the proof of Theorem 2.3 (4) in J. Bernstein and E.
Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024),
§8.6, p. 225, registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`. That proof
uses Theorem 2.3 (1), Theorem 6.3, Lemma 6.8 with (6.20), Proposition 6.9, the cuspidal
projections of §6.2 and the rapid decay of cusp forms (C. Mœglin and J.-L. Waldspurger, *Spectral
decomposition and Eisenstein series* (1995), I.2.18, registered as
`moeglin-waldspurger-1995-spectral-decomposition`). The majorant is the form of rapid decay that
makes the norm-one Levi tests continuous on the uniform-growth spaces, as
`StandardParabolicFamily.constantTermLeviPairingCLM` requires. The finite family adds no input:
the linearity of the Eisenstein series and of the intertwining integrals in the region of
convergence, and the absolute convergence of the tests of regular intertwining integrals, are
proved from results already in the Library.
