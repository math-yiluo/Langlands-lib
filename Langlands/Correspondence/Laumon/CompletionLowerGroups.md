# Lower and upper ramification groups across the completion

The module `Langlands.Correspondence.Laumon.CompletionLowerGroups` proves clauses 5 and 6 of
`Langlands.Henniart.Laumon.HenselianCompletionRamificationStatement`
(`Langlands.Correspondence.Laumon.Completion`), assuming that `completionRestriction k` is a
homeomorphism. Notation: \(X=\)`LaurentSeries k` for a finite field \(k\),
\(\Omega_X=\)`SeparableClosure X`, \(\Omega=\)`endGenericClosure k`,
\(r=\)`completionRestriction k` and \(v=\)`closureValuation X Ω_X`.

- `absoluteFiniteRestriction_apply`: the Library's restriction
  `absoluteFiniteRestriction X Ω_X L σ` to a finite Galois level \(L\) acts on \(L\) as
  \(\sigma\).
- `closureValuation_map`: \(v(\sigma x)=v(x)\) (the Library's
  `closureValuation_algEquiv_apply`).

## Clause 5

`mem_lowerRamificationGroup_iff_henselianLowerTest`: for every finite Galois level \(L\),
every \(\sigma\) and every \(i\ge 0\), the restriction of \(\sigma\) to \(L\) lies in
`lowerRamificationGroup (localTopologicalData X L) X i` exactly when \(r(\sigma)\) passes
`HenselianLowerTest k L i`.

Let \(\pi\in L\) be an element of maximal valuation \(<1\) (`exists_levelUniformizer`,
`Langlands.LocalFactor.Ramification.LocalClosureLower`). By
`mem_lowerRamificationGroup_iff_closureValuation` the left side says
\(v(\sigma x-x)\le v(\pi)^{i+1}\) for every \(x\in L\) with \(v(x)\le 1\). By density of
\(L\cap\Omega\) in \(L\) (`exists_henselianLevel_closureValuation_lt`,
`Langlands.Correspondence.Laumon.CompletionDensity`) there is \(\varpi\in L\cap\Omega\) with
\(v(\pi-\varpi)<v(\pi)\), so \(v(\varpi)=v(\pi)\).

- (\(\Rightarrow\)) \(\varpi\) is a uniformizer in the sense of `HenselianLowerTest`, and the
  congruences on the henselian integers are among those on the integers of \(L\).
- (\(\Leftarrow\)) a uniformizer \(\varpi'\) of the test satisfies \(v(\varpi')\le v(\pi)\) by
  the maximality of \(\pi\) and \(v(\pi)=v(\varpi)\le v(\varpi')\) by its own maximality. For
  \(x\in L\) integral choose \(b\in L\cap\Omega\) with \(v(x-b)<v(\pi)^{i+1}\); then \(b\) is
  integral and
  \(\sigma x-x=(\sigma b-b)+(\sigma(x-b)-(x-b))\) has valuation at most \(v(\pi)^{i+1}\).

So the congruences of Serre, *Local Fields*, IV §1, Lemma 1 b) (p. 61) on the integers of
\(L\) and on the henselian integers of \(L\cap\Omega\) agree.

## Clause 6

`mem_map_localAbsoluteUpperRamificationGroup_iff`: for every real \(v\) and every
automorphism \(\tau\) of \(\Omega\) over the end field, \(\tau\) lies in the image under \(r\)
of `localAbsoluteUpperRamificationGroup X Ω_X v` exactly when, for every finite Galois level
\(L\), \(\lceil\psi_L(v)\rceil<0\) or \(\tau\) passes `HenselianLowerTest` of index
\(\lceil\psi_L(v)\rceil\), with \(\psi_L=\)`herbrandPsi (localTopologicalData X L) X`.

The Library defines `localAbsoluteUpperRamificationGroup X Ω_X v` as the intersection over the
finite Galois levels \(L\) of the preimages of the upper groups \(G(L/X)^v=G(L/X)_{\psi_L(v)}\)
(`mem_absoluteUpperRamificationGroup_iff_lower`: Serre's upper numbering, IV §3, pp. 73–74),
using the lower group at the integer index \(\lceil\psi_L(v)\rceil\). For a negative
index the lower group is the whole finite Galois group
(`mem_lowerRamificationGroupInt_iff`). For a nonnegative index, clause 5
identifies membership with the henselian lower test at that index. Surjectivity
of \(r\) gives the reverse inclusion. The equivalence holds for every real \(v\).

Every declaration of the module depends only on `propext`, `Classical.choice` and
`Quot.sound`.
