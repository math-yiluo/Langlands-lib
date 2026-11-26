# Finite Galois covering spectral sequence on the analytic étale site

Let \(V'\to V\) be a finite analytic Galois covering of objects of the
étale site of \(X\), with deck group \(\Gamma\). Let \(F\) be a sheaf
of \(R\)-modules on that site. The Hochschild–Serre spectral sequence
for these objects has the form

\[
 E_2^{i,j}=H^i(\Gamma,H^j(V',F))
 \quad\Longrightarrow\quad H^{i+j}(V,F).
\]

`Langlands.Cohomology.AnalyticGlobalSpectralSequence.AnalyticEtaleFiniteGaloisSpectralSequenceStatement`
asserts this for the actual cover `AnalyticGaloisCover` of étale objects
over a fixed complete ultrametric normed field `K`, with the explicit
instance `[Finite Γ]`. The deck group and the commutative coefficient
ring `R` are in the module universe. The map `toEtaleSiteCover` supplies
the covering sieve and the local freeness and transitivity of the deck
transformations.
`GaloisCovering.sectionsWithDeck` sends \(F\) to its sections over \(V'\)
with the left action by pullback along inverse deck transformations.
The naturality of a sheaf morphism for those restrictions proves
equivariance of its induced linear map.

The terms \(H^j(V',F)\) are the right derived representation-valued
sections over \(V'\) in the actual sheaf category on the étale site
of \(X\). The group cohomology on page two is expressed as `Ext` from
the trivial rank-one representation. The specified spectral sequence
is the covariant hyperext sequence for the derived sections complex
over \(V'\) and that trivial representation. The statement quantifies
over the derived-category model of ordinary \(R\)-linear
\(\Gamma\)-representations in its own universe. Its abutment is the
ordinary right derived sections over \(V\), with the first quadrant and
finite filtration expressed by `FirstQuadrantAbutmentStatement`. For
\(V=X\) the abutment is the cohomology of \(X\).

Milne, *Étale Cohomology* (1980), III.2, Theorem 2.20 and its proof,
printed p. 105 (PDF p. 119), gives the construction for finite Galois
coverings of schemes. Sections on the covered object are degree-zero
deck invariants. The Čech cochains compute group cohomology as in
Example 2.6, and Lemma 2.4 gives acyclicity on injective sheaves
(printed pp. 98–100, PDF pp. 112–114). On the analytic site
`GaloisCovering` supplies the same descent of sections and
`isZero_groupCohomology_rep_of_injective` supplies the positive-degree
vanishing for injective sheaves.
Registered ID `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.

Berkovich, *Vanishing cycles for formal schemes* (1994), proof of
Corollary 5.6, printed p. 556 (PDF p. 18), uses the finite-cover
Hochschild–Serre spectral sequence on a compact analytic space to
reduce finiteness with finite locally constant coefficients to the
case of constant coefficients on a cover. The spectral sequence
above uses only the étale covering and works with any commutative
module coefficient ring in its stated universe. Registered ID
`berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
