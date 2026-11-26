# Rational Bruhat cells as locally closed multiplication maps

`Langlands.GroupScheme.rationalBruhatCell` proves
[`RationalBruhatCellStatement`](BruhatCellStatement.md) with all of its
hypotheses as stated. Write \(\chi\) for the generic cocharacter through
the maximal split torus \(T\), \(W=nVn^{-1}\cap U\) for
`BruhatCell.factor u v n`, and \(f\) for `BruhatCell.parametrization u v p n`.

## The multiplication formula

`BruhatCell.lift_parametrization` computes \(f\) on every test scheme
\(X\) over \(k\): for \(a\colon X\to W\) and \(b\colon X\to P\), the
composite of \((a,b)\) with \(f\) is the product
\(a\cdot n_X\cdot b\) in \(G(X)\), where \(a\) and \(b\) are viewed in
\(G\) through their inclusions and \(n_X\) is the constant point of \(n\)
(`GroupScheme.constantPoint`). The proof unfolds `parametrization`, uses
`SubgroupFunctor.lift_cellMultiplication` and
`Dynamic.comp_rationalLeftTranslation`, and rewrites the conjugated
inclusion of \(V\) with `comp_innerIso_hom`.

## The immersion

The projection `subgroupIntersectionFst` from \(W\) to \(V\) is a base
change of \(u\colon U\to G\), so it is a closed immersion because \(u\) is
(`isClosedSubgroup_subgroupIntersectionFst`, using the hypothesis
`IsClosedSubgroup u`). Its product with the identity of \(P\) is again a
closed immersion (`ImageGeneration.isClosedImmersion_tensorHom_left`).
The opposite-cell multiplication \(V\times P\to G\),
`SubgroupFunctor.cellMultiplication v p`, is an open immersion by the
published theorem `oppositeCellStatement`, applied to the representing
maps \(v\) of \(U_G(-\chi)\) and \(p\) of \(P_G(\chi)\); its smoothness
and affineness inputs come from the connected reductive structure of
\(G\). Left translation by \(n\) is an isomorphism. The map \(f\) is the
composite of these three maps, so the private lemma
`BruhatCell.parametrization_isImmersion` concludes by instance search
that \(f\) is an immersion.

## Rational points

The proof first records two published facts. By `genericCentralizer`,
the dynamic centralizer of the generic cocharacter is the centralizer
\(Z_G(T)\) of the maximal split torus. With `oppositeCellStatement`
this gives the unipotent Weyl factorization
`hasUnipotentWeylFactorization_of_oppositeCell`: for every rational
point \(n\) normalizing \(T\), each \(x\in U(k)\) factors as
\(x=x_1x_2\) with \(x_1,x_2\in U(k)\), \(n^{-1}x_1n\in V(k)\) and
\(n^{-1}x_2n\in U(k)\).

*Image contained in the double coset.* Let \(x\colon\operatorname{Spec}k\to W\times P\)
with \(x\cdot f=g\), and let \(a\), \(b\) be its two components. The
range of the inclusion of \(W\) is the intersection of the two ranges
(`range_subgroupIntersectionHom`), and the range of \(u\) is
\(U_G(\chi)\) by the representability hypothesis. Hence \(a\) is a point
of \(U(k)\subseteq P(k)\) (`Dynamic.unipotent_le_parabolic`) and
lifts through \(p\) by `SubgroupFunctor.IsRepresentedBy.pointsEquiv`.
The formula above, with `constantPoint_self` for the constant point of
\(n\) over \(k\), gives \(g=a\,n\,b\) in \(P(k)\,n\,P(k)\).

*Double coset contained in the image.* Let \(g=a\,n\,b\) with
\(a,b\in P(k)\). Decompose \(a=x z\) with \(x\in U(k)\) and \(z\) in the
rational Levi points (`RationalPoint.existsUnique_unipotent_mul_levi`),
and factor \(x=x_1x_2\) by the Weyl factorization. The Levi is
\(Z_G(T)\), which \(n^{-1}\) normalizes
(`torusCentralizer_isNormalizedBy_torusNormalizer`), so
\(n^{-1}zn\) is again a Levi point. Therefore
\[
  d=(n^{-1}x_2n)(n^{-1}zn)\,b
\]
lies in \(P(k)\), using `RationalPoint.unipotent_le_parabolic`,
`RationalPoint.levi_le_parabolic` and closure under multiplication.
The point \(x_1\) lies in \(U(k)\) and, since \(n^{-1}x_1n\in V(k)\), in
the range of the conjugated inclusion of \(V\); by
`range_subgroupIntersectionHom` it comes from a point \(c\) of \(W\).
Lifting \(d\) to a point of \(P\) through \(p\), the point \((c,d)\) of
\(W\times P\) is sent by \(f\) to
\[
  x_1\,n\,(n^{-1}x_2n)(n^{-1}zn)\,b=x_1x_2\,z\,n\,b=a\,n\,b=g ,
\]
and the `group` tactic closes this identity in \(G(k)\).
