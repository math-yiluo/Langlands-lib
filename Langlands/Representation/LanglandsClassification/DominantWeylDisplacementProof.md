# Proof of the ambient Weyl displacement bound

`Langlands.GroupScheme.dominantWeylDisplacement` proves
`Langlands.GroupScheme.DominantWeylDisplacementStatement` over an arbitrary
field. If \(x \in V^*(T)\) pairs nonnegatively with the simple coroots of the
supplied relative reflection data, then \(x-w^{-1}x\) belongs to the conic
hull of the simple roots in \(\mathbb R \otimes_{\mathbb Z} X^*(T)\), with
the actual relative Weyl action.

The empty-index standard Levi represents the centralizer of the maximal split
torus \(T\). The canonical factor of \(T\) into that Levi is central and remains
maximal split, so it is a split component. The proof uses this factor in
`ParabolicDatum.standardRootPresentation`, taking the map from the split
component to \(T\) to be the identity.

The Lean proof applies `ParabolicRootPresentation.restrict_displacement_mem_nonnegCone`
to that presentation and \(w^{-1}\). The imported length induction uses
\(x-vs_\alpha x=(x-vx)+\langle x,\alpha^\vee\rangle v\alpha\) when right
multiplication by \(s_\alpha\) increases the length of \(v\). In that case
\(v\alpha\) is a positive root and dominance gives a nonnegative coefficient.
Restriction along the identity fixes the displacement in the full real
character space. For the empty index the restricted simple roots are all the
original simple roots, and `RootCombination.nonnegCone_eq_hull` identifies
their nonnegative combination cone with `PointedCone.hull` of the vectors
\(1\otimes\alpha\).

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, (VII.4.1.3) and its proof, printed pp. 241–242
(PDF pp. 247–248), and V.3.15 for the closed chamber and nonnegative root cone,
printed p. 113 (PDF p. 119). Source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
