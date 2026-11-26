# Scheme points of a closed subscheme and its complement

Let \(R \to S\) be a map of commutative rings, \(Z \hookrightarrow X\)
a closed immersion of \(R\)-schemes, \(U\) the complementary open in
\(X\), and \(p:\operatorname{Spec} S\to X\) an \(R\)-point with values
in \(S\). Let \(\mathcal J\) be the ideal sheaf defining
\(Z\times_X\operatorname{Spec} S\) in \(\operatorname{Spec} S\).

`SchemePointStratificationStatement` gives the following criteria.

- The image of \(p\) is set-theoretically contained in \(Z\) exactly
  when \(\mathcal J\) is contained in the nilradical.
- The point factors through \(Z\) exactly when \(\mathcal J=0\).
- The point factors through \(U\) exactly when its image is contained
  in the complementary open.

For a nonzero \(S\) the two factorization conditions are disjoint. For a
local Artinian \(S\), every point either has image contained in \(Z\) or
factors through \(U\). For a field \(S\), every point factors through one
of the two subschemes. There is no affineness or finiteness assumption on
\(X\) or \(Z\).

This gives the support and factorization distinction in Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, Remark 3.3, printed
p. 5. The source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The local Artinian clause uses the single point of the spectrum. The field
clause uses reducedness as well. `ConradRemark33Correction` gives the
dual-number example showing that support in the closed subscheme need
not give factorization over a local Artinian ring.
