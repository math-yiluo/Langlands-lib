# Proper parabolics under a smooth connected unipotent quotient

This is an internal consequence of the actual parabolic order correspondence
and fpqc reflection for represented subgroup functors. It supplies no new
facet geometry.

Let \(k\) be any field in universe \(u\). Let \(G\) be a smooth connected
affine group scheme over \(k\), let \(Q\) be affine, and let
\(q:G\to Q\) be flat, surjective and locally of finite presentation.
Assume that its actual scheme-theoretic kernel is smooth, connected and
unipotent. Then every actual rational parabolic embedding in \(G\) is an
isomorphism if and only if every actual rational parabolic embedding in
\(Q\) is an isomorphism. Equivalently, a proper actual rational parabolic
exists in \(G\) if and only if one exists in \(Q\).

Here an actual rational parabolic is an embedding over the original field
with the existing `IsParabolicSubgroup` predicate: it is smooth and closed
and contains a Borel after extension to the algebraic closure. Proper
means that the original embedding is not an isomorphism. The proof uses
subgroup functors on every scheme test over the field, so it does not
replace properness with a statement about rational points. There is no
perfectness, reductivity or characteristic restriction.

The preliminary lemma
`SubgroupFunctor.isIso_iff_of_range_eq_comap` works over any base scheme.
For an fpqc homomorphism \(q\), suppose monomorphisms \(i\) and \(j\)
have full scheme-test ranges satisfying
\(\operatorname{range}(i)=q^{-1}\operatorname{range}(j)\).
If \(i\) is an isomorphism, its range is the full subgroup. The existing
`SubgroupFunctor.comap_le_range_iff` reflects containment of the full
subgroup into \(\operatorname{range}(j)\). Thus \(j\) has full range
and is an isomorphism. Conversely, full range of \(j\) pulls back to full
range of \(i\), so \(i\) is an isomorphism. Both steps reuse the published
`isIso_of_full_range` and `full_range_of_isIso` from
`Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction`; they do not
assume surjectivity on rational points. Only monomorphisms, rather than
closed immersions, are needed for this preliminary lemma.

For `UnipotentQuotientParabolics.noProperParabolic_iff`, the proof uses
`parabolicComapOrderIso` from
`Langlands.GroupScheme.Absolute.UnipotentQuotientParabolicOrder`.
Given a target parabolic, its image under the order isomorphism is
represented by an actual source parabolic, and the forward full-comap
identity identifies their ranges as above. In the reverse direction,
the inverse order map supplies an actual target parabolic and its
exact inverse-comap identity gives the same range equality. Parabolic
closedness supplies monicity in both cases. The preliminary lemma now
transfers the hypothesis that each actual parabolic embedding is an
isomorphism. `exists_properParabolic_iff` follows by classical negation.

The proposition `UnipotentQuotientNoProperParabolicStatement.{u}` states
the absence equivalence with the displayed actual quotient and kernel
hypotheses. `unipotentQuotientNoProperParabolic` proves it by the preceding
construction.

This is the algebraic quotient step after a neutral special fibre and its
quotient have been supplied. It proves neither that a Gamma-chamber
residue group has no proper rational parabolics nor that such a residue
group or a coherent descended facet model exists.
`Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement`
remains open.
