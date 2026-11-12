# Rational points of locally separated spaces are locally Hausdorff

Author: Worker 79.

`LocallySeparatedRationalPointsStatement` states that over a henselian valued field the
rational points of every quasi-separated, locally separated algebraic space locally of
finite type are locally Hausdorff, locally compact when the field is, and locally totally
disconnected when its norm is ultrametric. This is the topological claim of Conrad's
Example 5.5, in the corrected form of `UnipotentOrbitQuotientPointTopologyStatement`, for
an arbitrary such space rather than an orbit quotient. The module states the claim and
contains no proof.

## The statement

Let `K : Type u` be a nontrivially normed field with `IsHenselianValuedField K`
(`HenselianEtalePointStatement.lean`: the absolute value extends uniquely to every
algebraic extension). Let `X : AlgebraicSpace (Spec K)` satisfy
`IsLocallySeparatedLocallyFiniteType K X` (`HenselianSpacePointTopologyStatement.lean`):
`X` is quasi-separated (`IsQuasiSeparated`), locally of finite type over `K`
(`LocallyOfFiniteTypeOverBase`) and locally separated (`IsLocallySeparated`, the diagonal
is a representable immersion). The conclusion is `HasLocallyHausdorffRationalPoints K X`
(`UnipotentOrbitQuotientStatement.lean`): with `X(K)` carrying `etaleChartTopology K X`,
every rational point has an open neighbourhood `W` that is Hausdorff, locally compact if
`K` is locally compact, and totally disconnected if the norm of `K` is ultrametric
(`IsUltrametricDist K`).

## Sources

- Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
  registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, Example 5.5,
  printed p.16: "The topological space `(V_d/G)(k)` is locally Hausdorff and locally
  compact (and locally totally disconnected)." Conrad gives no argument. In the proof of
  Proposition 5.4 (printed pp.14–16), the step on printed p.16 shows that `U(k) → X(k)` is
  a local homeomorphism for an étale map `U → X` from a separated scheme; that step needs
  local separatedness of `X`, as explained in `HenselianSpacePointTopologyStatement.md`.
- The corrected topological claim, with local separatedness and with local compactness
  and total disconnectedness qualified by the properties of `K`, is that of
  `UnipotentOrbitQuotientPointTopologyStatement`; its Markdown
  (`UnipotentOrbitQuotientStatement.md`, section "Correction") gives the reasons and a
  counterexample without local separatedness.

## Derivation (provenance: derived)

The statement is the corrected claim of Example 5.5 with the orbit quotient replaced by an
arbitrary quasi-separated, locally separated space locally of finite type; clause 3 of
`UnipotentOrbitQuotientStatement` follows from it once the quotient is known to be
quasi-separated and locally of finite type (`SmoothStabilizerActionQuotientStatement` and
`ActionQuotientFinitenessStatement`). The derivation sketched in
`UnipotentOrbitQuotientStatement.md` applies:

- Every rational point `x` of `X` is the image of a rational point `u` of an affine scheme
  `U` of finite type with an étale map to `X` (the Library's
  `exists_affine_chart_pointMap_eq`, `EtaleChartTotallyDisconnected.lean`).
- As `X` is locally separated, `U(K) → X(K)` is a local homeomorphism (the Library's
  `isLocalHomeomorph_ringPointsMap`, `EtaleChartLocalSeparation.lean`). So `x` has an open
  neighbourhood homeomorphic to an open subset of `U(K)`.
- `U(K)` is a closed subset of some `K^n`. Open subsets of it are Hausdorff, locally
  compact when `K` is, and totally disconnected when the norm is ultrametric.

The names of the declarations are derived here.
