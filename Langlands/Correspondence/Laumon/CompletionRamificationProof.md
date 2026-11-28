# Ramification across the completion: the proof

The module `Langlands.Correspondence.Laumon.CompletionRamificationProof` proves

- `henselianCompletionRamification : HenselianCompletionRamificationStatement.{u}`

(`Langlands.Correspondence.Laumon.Completion`) for every finite field `k : Type u`. It applies
`henselianCompletionRamification_of_galois`
(`Langlands.Correspondence.Laumon.CompletionRamificationReduction`) to the Library's proof
`henselianCompletionGalois` of `HenselianCompletionGaloisStatement`
(`Langlands.Correspondence.Laumon.CompletionGaloisProof`): restriction
`completionRestriction k` from the absolute Galois group of `LaurentSeries k` to that of the end
field `endField k` is a homeomorphism.

With \(X=\)`LaurentSeries k`, \(\Omega_X=\)`SeparableClosure X` and
\(\Omega=\)`endGenericClosure k`, the six clauses are proved as follows.

1. **Inertia** (`absoluteInertia_map_completionRestriction`): reduction maps the constants
   `endConstants k` bijectively onto the residue field of the integers of \(\Omega_X\)
   (Teichmüller roots of unity), so an automorphism lies in the Library's inertia exactly when
   its restriction fixes the constants, that is, fixes `endUnramifiedField k`.
2. **Residue map** (`exists_constants_residue_equiv`): the reduction of the constants composed
   with the Library's `residueClosureEquiv`.
3. **Degree** (`completionRestriction_localProjection_pow`): a Weil element of degree \(n\) acts
   on the residue field as the \(n\)-th power of geometric Frobenius, read through clause 2.
4. **Wild inertia** (`mem_map_localWildInertia_iff`): through the Library's
   `absoluteUpperWildInertia`, wild inertia consists of automorphisms whose restrictions lie in
   the first lower group at every finite Galois level. For \(\varpi^N=t\) with \(N\) prime to
   the characteristic of \(k\), the ratio \(\sigma(\varpi)/\varpi\) is an \(N\)-th root of unity
   because \(\sigma\) fixes \(t\). The finite-level congruence gives this ratio residue \(1\).
   Injectivity of reduction on these roots gives \(\sigma(\varpi)=\varpi\).
   Conversely, an inertia automorphism fixing all these roots satisfies the uniformizer
   congruence and hence the first lower group congruences at every finite level (Serre,
   *Local Fields*, IV §2, Proposition 5, p. 66).
5. **Lower groups** (`mem_lowerRamificationGroup_iff_henselianLowerTest`): the henselian
   elements \(L\cap\Omega\) of a finite Galois level \(L\) generate \(L\) over \(X\) and are dense
   in \(L\), so the congruences of Serre IV §1, Lemma 1 (p. 61) on the integers of \(L\) and on
   the henselian integers agree.
6. **Upper groups** (`mem_map_localAbsoluteUpperRamificationGroup_iff`): the Library's absolute
   upper group is the intersection of the preimages of the finite upper groups
   \(G(L/X)^v=G(L/X)_{\psi_L(v)}\) under finite restriction (Serre IV §3, pp. 73–74).
   If \(\lceil\psi_L(v)\rceil<0\), the finite group condition holds automatically because
   the lower group is the whole finite Galois group. At the endpoint \(v=-1\), this ceiling
   is \(-1\) at every finite level. For a nonnegative ceiling, clause 5 identifies the finite
   condition with the henselian lower test of index \(\lceil\psi_L(v)\rceil\).

Sources: Laumon 1987, (2.1.1), p. 151; Serre, *Local Fields*, II §3, pp. 30–31, and IV §§1–3;
Katz 1986, (1.4.8)–(1.4.9), pp. 81–82, for the comparison of the Galois groups of a henselian
discrete valuation field and of its completion. The theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`.
