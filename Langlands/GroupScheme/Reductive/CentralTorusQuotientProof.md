# Proof: the split central torus quotient

Authors: Worker 1428, Worker 1546, Worker 1404.

This module proves one theorem,
`Langlands.GroupScheme.splitCentralTorusQuotient :
SplitCentralTorusQuotientStatement.{u}`, the published statement of module
`Langlands.GroupScheme.Reductive.CentralTorusQuotientStatement`, for every
universe `u`.

## The proof

The theorem applies the conditional reduction
`splitCentralTorusQuotient_of_prerequisites'` (module
`Langlands.GroupScheme.Reductive.CentralTorusQuotientFiniteReduction`) to
proofs of its three hypotheses, all published Library theorems:

- `splitTorusKernelCentrality : SplitTorusKernelCentralityStatement.{u}`
  (module `Langlands.GroupScheme.Rational.SplitTorusKernelCentralityProof`):
  the kernel of `t`, mapped into `G` by the maximal torus `i`, is central in
  `G` when every root of `i` factors through `t`;
- `splitTorusIsogenyOfLatticeMaps : SplitTorusIsogenyOfLatticeMapsStatement.{u}`
  (module `Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof`):
  injective character and cocharacter maps make `groupHom t` an isogeny;
- `centralIsogenyMaximalTorusImage : CentralIsogenyMaximalTorusImageStatement.{u}`
  (module `Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageProof`): a
  central isogeny of connected reductive groups carries a maximal torus onto a
  closed torus that is maximal among all closed tori.

The construction itself is in the reduction module, whose Markdown describes
it; in outline:

1. `t` is an isogeny (second bullet above), so its actual kernel is finite.
2. That kernel, mapped into `G` by `i`, is a finite central closed subgroup
   (first bullet). The published
   `exists_centralIsogeny_of_finite_central_subgroup` gives a central isogeny
   `q : G ⟶ Q` with that kernel and smooth affine `Q`.
3. `Q` is connected reductive by `isConnectedReductive_of_isCentralIsogeny`
   (module `Langlands.GroupScheme.Reductive.CentralFiniteQuotientReductive`),
   proved unconditionally there: the kernel of a central isogeny has bounded
   exponent, which makes the geometric unipotent radical of `Q` trivial.
4. `i ≫ q` kills the kernel of `t`, so fpqc descent along `t` gives
   `i'' : T' ⟶ Q` with `i ≫ q = t ≫ i''`; it is a monomorphism, hence a closed
   torus, and it is maximal by the third bullet above.

The theorem keeps the full published statement: arbitrary field and
universe, the actual scheme-theoretic kernel of `t`, the all-test `roots`,
`IsCentralIsogeny q` and `IsMaximalTorus i''` among all closed tori.

The candidate also contains the modules
`Langlands.GroupScheme.Reductive.CentralTorusQuotientReduction` (the
four-hypothesis reduction `splitCentralTorusQuotient_of_prerequisites` and
`SubgroupFunctor.isNormal_of_le_center`, which the three-hypothesis reduction
imports), `Langlands.GroupScheme.Reductive.CentralFiniteQuotientReductive`
and `Langlands.GroupScheme.Reductive.CentralTorusQuotientFiniteReduction`,
each with its own Markdown. The published statement
`CentralQuotientReductiveStatement` (reductivity of the quotient by an
arbitrary central subgroup) is a hypothesis only of the four-hypothesis
reduction and is not used by this theorem.

## Provenance

The route is internal; it follows the sketch in the statement's Markdown
(J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, source
`milne-2017-algebraic-groups`; see the locators there). Checked with
`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` against
Library commit `0bd5bf67c3464359bc8da3b3100163d6ee3da352`, together with the
three modules above (diagnostic `d36d4362-ae19-4303-b2e5-46bd5324db90`):
0 errors, 0 warnings, axioms `propext`, `Classical.choice`, `Quot.sound`.
