# Reflection of the rational dual-pullback equation

`IsRationalDualPullbackMultiple.of_baseChange_of_naturality` considers a
rational map \(f\colon A\to B\) of abelian schemes and rational dual-valued
maps \(\lambda_A\) and \(\lambda_B\). It assumes the dual base-change
comparisons and their naturality, and that rational Hom pullback along
\(b\colon S'\to S\) detects zero for maps from \(A\) to its dual.
If the canonical pullbacks satisfy the multiplier equation with \(q\in
\mathbb Q\), then \(f^\vee\lambda_B f=q\lambda_A\) over \(S\).

The proof applies `rationalDualPullbackBaseChangeHom_commutes` and
linearity to show that the canonical dual-valued pullback of
\(f^\vee\lambda_B f-q\lambda_A\) is zero. This canonical map is ordinary
rational Hom pullback followed by the comparison isomorphism for the
dual of \(A\). Composing with the inverse comparison and applying zero
detection gives the multiplier equation. The integral variant
`IsRationalDualPullbackMultiple.integral_of_baseChange_of_naturality`
applies this argument to the rational images of actual dual-valued
homomorphisms and uses `rationalDualBaseChangeHom_homToHom0` to identify
their pullbacks.
