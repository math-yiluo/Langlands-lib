# Proof of the passage of Eisenstein series to a standard family with a compact in good position

Module `Langlands.Global.AdelicEisensteinStandardizationProof`. The theorem
`Langlands.Global.eisensteinStandardization` proves
`Langlands.Global.EisensteinStandardizationStatement.{u}` (module
`AdelicEisensteinStandardizationStatement`) at an arbitrary universe `u`, with no hypothesis.

## Proof

The theorem applies `eisensteinStandardization_of_bruhatTitsAvailability` (module
`AdelicEisensteinStandardizationReduction`) to a proof of `BruhatTitsAvailabilityStatement`.
That proof is `bruhatTitsAvailabilityReduction` (module
`Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof`) applied to
`groupAxiomsExistence` (module `Langlands.Geometry.Building.GroupAxiomsExistenceProof`), the
proof of `GroupAxiomsExistenceStatement`.

The argument is in the Markdown of `AdelicEisensteinStandardizationReduction`. In outline:

1. The presentation's maximal split torus and generic cocharacter give a standard family
   (`StandardParabolicFamily.ofMaximalSplitTorus`). The presentation's index gives a standard
   parabolic \(P_I\) with the image of \(P\), and closed subgroups with equal images are
   isomorphic over \(G\) (`IsClosedSubgroup.sourceIsoOfRangeEq`).
2. Local compacts in good position at all places (`infinitePlaceStandardLeviCompact`, and
   `finitePlaceStandardLeviCompactReduction` with the Bruhat–Tits data) are assembled into an
   adelic maximal compact \(K'\) in good position (`standardLeviCompactAssembly`).
3. The archimedean factors of \(K\) and \(K'\) are conjugate by some \(t\in G(F_\infty)\)
   (`infiniteAdelicMaximalCompactConjugacy`). Right translation by \(t\) transports automorphy
   for \(K_\infty\) to automorphy for \(K'_\infty\) (`IsAutomorphicFunctionOn.infiniteRightTranslate`).
4. \(K\) and \(C=t^{-1}K't\) have the same archimedean factor. The finite change of heights
   (`IsAutomorphicFunctionOn.exists_parameterTwist_of_infinite_eq`) and absolute convergence
   (`eisensteinAbsoluteConvergence`) write \(E_{P,K}(\varphi,\lambda)\) as a finite combination of
   series for \(C\) with coefficients \(e^{\langle\lambda,v\rangle}\) for regular \(\lambda\).
5. The series for \(C\) at \(gt\) is \(e^{\langle\lambda,H_C(t)\rangle}\) times a series for
   \(K'\) at \(g\) (`IsIwasawaCompact.eisensteinSeries_mul_conjInv`), and a series for \(P\) is a
   series for \(P_I\) at the restricted parameter
   (`IsIwasawaCompact.eisensteinSeries_eq_of_range_eq`). Regularity is transported by
   `eisensteinRegularityParabolicTransport`.

## Provenance

The statement and its sources are described in the Markdown of
`AdelicEisensteinStandardizationStatement`: Bernstein–Lapid (2024), §2.1–2.2, pp. 189–191
(literature id `bernstein-lapid-2024-meromorphic-continuation-eisenstein`), and
Mœglin–Waldspurger (1995), I.1.4, pp. 4–5 (literature id
`moeglin-waldspurger-1995-spectral-decomposition`). The proof follows the route given there in
the section "Why it holds". The finite-place compacts in good position come from the corrected
Definition 4.1.26 conclusion of Kaletha–Prasad, Theorem 9.2.7, through
`BruhatTitsAvailabilityStatement`.
