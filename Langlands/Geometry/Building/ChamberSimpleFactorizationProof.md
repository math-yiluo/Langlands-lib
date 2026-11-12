# Proof of the chamber-simple factorization (KP (7.5.1))

This module proves the published proposition
`Langlands.Geometry.Building.ChamberSimpleFactorizationStatement.{u}`
(module `Langlands.Geometry.Building.AffineIwahoriTitsInputStatements`) at an
arbitrary universe `u`. The theorem is
`Langlands.Geometry.Building.chamberSimpleFactorization`. Its type is exactly
the statement: the statement is not changed, and no hypothesis is added. Its
only hypothesis on the datum `P` is still
`P.apartment.SatisfiesApartmentAxioms P.centralizer`.

## What is proved

Let `F` be a nonarchimedean local field, `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`, and `P : ParahoricBuildingData G` a datum that
satisfies the apartment axioms. Let `C` be a chamber,
`ψ ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C`, `α` a relative root
with `ψ.linear = rootForm P.i α`, and `v` a coroot of `ψ`, with proof `hv`.
Then every `b ∈ P.parahoric C` can be written as `b = b' * u`, with
`b' ∈ P.parahoric (AffineRootSystem.affineReflection ψ hv.1 '' C)` and
`u ∈ P.apartment.affineRootGroup α ψ`. This is KP (7.5.1), `I ⊆ s I s U_ψ`,
in the form explained in the statement's Markdown.

## Implemented proof

The proof composes published Library results only. It adds no new
mathematical argument and no new assertion from the literature.

1. **The published reduction.** `chamberSimpleFactorizationPrerequisiteReduction`
   (module `ChamberSimpleFactorizationPrerequisiteReduction`) proves that the
   exact target follows from two inputs:
   - `RootRankOneFactorizationStatement.{u}`;
   - `P.zeroDatum.CoverImageCentralizerNormKernelStatement` for every local
     field `F`, every `G` and every `P : ParahoricBuildingData G`. This is the
     containment `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` for the datum's own zero data.

   That reduction applies the published local theorem
   `ParahoricBuildingData.simpleFactorization_of_rankOneFactorization`
   (module `ChamberSimpleParahoricFactorization`). Its Markdown describes the
   geometric argument: the chamber Iwahori decomposition writes an element of
   `P_C` as a negative root factor, a factor in `Z(F)^0` and a positive root
   factor. The first two factors lie in `P_{rC}`. The positive factor splits
   into an element of `P_{rC}` followed by an element of `U_ψ`.

2. **Rank-one factorization.** The first input is the published unconditional
   theorem `Langlands.GroupScheme.rootRankOneFactorization`
   (module `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`,
   KP Proposition 2.11.17).

3. **The cover-image comparison.** For each datum `P`, the second input comes
   from the published conditional theorem
   `ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_inputs`
   (module `KPCoverImageReduction`), applied to `P.zeroDatum`. That theorem
   takes five structural statements as hypotheses. The proof supplies all
   five from published proofs:
   - `hC`: `cocenterQuotientExistence`
     (module `Langlands.GroupScheme.Derived.CocenterQuotientProof`);
   - `hB1`: `inducedTorusIwahori` (module `KPInducedTorusIwahoriProof`,
     KP Lemma 2.5.18);
   - `hsc`: `isSimplyConnectedFieldExtension`
     (module `Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof`);
   - `hF : SplitTorusCentralizerCocenterInducedStatement`: the published
     reduction `splitTorusCentralizerCocenterInduced_of_inputs`
     (module `Rational.SplitTorusCentralizerCocenterAssembly`), applied to the
     five published proofs `dynamicCentralizerReductive`,
     `cocenterQuotientExistence`, `isSimplyConnectedFieldExtension`,
     `splitSimplyConnectedCorootSpan` and
     `splitTorusCentralizerCocenterRootModel`;
   - `hPL : SplitTorusCentralizerCoverPreimageStatement`: the published
     reduction `splitTorusCentralizerCoverPreimage_of_inputs`
     (module `SimplyConnected.SplitTorusCentralizerCoverPreimageReduction`),
     applied to `reductiveCentralDerivedProduct`, `dynamicCentralizerReductive`
     and a proof of `SplitTorusCentralizerDerivedSimplyConnectedStatement`.

   The last proof is the published reduction
   `splitTorusCentralizerDerivedSimplyConnected_of_inputs`
   (module `SimplyConnected.SplitTorusCentralizerDerivedAssembly`), applied to
   `dynamicCentralizerReductive`, `derivedSubgroupSemisimple`,
   `splitSimplyConnectedCorootSpan`, `splitCorootSpanSimplyConnected`,
   `splitTorusCentralizerDerivedCorootComparison` and a proof of
   `IsSimplyConnectedAlgebraicClosureAscentStatement`. That ascent proof is
   the published `isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure`
   (module `SimplyConnected.FieldExtensionStructuralAssembly`). It is applied
   to the seven published proofs that the Library's
   `isSimplyConnectedFieldExtension` also uses:
   `simplyConnectedCoverTensorDescent`, `splitSimplyConnectedCoverExistence`,
   `simplyConnectedCentralCoverUniversalProperty`, `maximalTorusBaseChange`,
   `rootDatumExistence`, `splitSimplyConnectedCorootSpan` and
   `splitCorootSpanSimplyConnected`.

The intermediate results are local `have`s inside the single theorem. The
module adds no other top-level declaration. Its names therefore cannot clash
with proofs that other tasks may publish for these intermediate statements.

`lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled
the module with no errors and no warnings. The theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

The target and its source locations are documented in
`AffineIwahoriTitsInputStatements.md`. The source is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`: inclusion (7.5.1),
printed p. 259 / PDF p. 290, in the proof of Theorem 7.5.1 (printed
pp. 259–260 / PDF pp. 290–291). The 1 November 2024 corrections, PDF p. 35,
are registered as `kaletha-prasad-2024-corrections`. KP derive (7.5.1) from
the chamber Iwahori decomposition (Corollaries 7.4.9 and 6.3.11). The
implemented proof follows the Library's existing reduction. For the central
factor, that reduction needs the cover-image containment used in the proof of
KP Corollary 2.6.28 (printed pp. 105–106 / PDF pp. 136–137). Each composed
result has its own published Markdown with its sources.

Author: Worker 4689.
