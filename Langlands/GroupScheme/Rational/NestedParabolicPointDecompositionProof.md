# Decompositions for supplied nested parabolic triples

Author: Worker 1754. The canonical preimage interfaces used here were constructed
by Worker 1452 in the separate `LeviParabolicPreimage` module.

The theorem `Langlands.GroupScheme.nestedParabolicPointDecomposition` proves
`NestedParabolicPointDecompositionStatement` at its original universe `u`.
It retains the original arbitrary nonarchimedean local field, connected reductive
ambient group, three supplied actual parabolic triples, and the three prescribed
compatibility hypotheses. It identifies the supplied inner radical and proves
both ordered products of subsets of the original ambient rational-point group.

Write the supplied triples as \(P=MN\), \(Q=LU\), and \(P_L=MN_L\). All
intermediate range comparisons are comparisons of subgroup functors on every
relative scheme test. Rational points are used only in the imported density
comparison and in the final evaluation.

## Projection and the supplied radicals

The private lemma `exists_projection_radical_comparison` starts with a monic
map \(a:P\to Q\) whose range is the inverse image of the range of
\(P_L\to L\) under the actual Levi retraction \(\rho:Q\to L\).
The constructed isomorphism `leviPreimageIsoOfRange` identifies \(P\), with its
given inclusion into \(Q\), with the actual pullback of that retraction.
Transporting the pullback projection gives \(t:P\to P_L\), satisfying
\(t\,;\,p_L=a\,;\,\rho\).

The original \(U\) lifts to the pullback. Transporting its lift back to \(P\)
gives an exact representative of the kernel of \(t\). The proof transports
the range of the actual categorical kernel, rather than choosing an unrelated
abstract unipotent group. Smoothness of \(t\) follows by base change of the
smooth Levi retraction and composition with an isomorphism. The canonical
section of the pullback gives a section of \(t\), hence surjectivity.
The kernel representative has the smoothness, connectedness and unipotence
of the supplied \(U\).

The published
`HasSmoothConnectedUnipotentKernel.radical_comap_eq` therefore applies to \(t\)
and the original supplied radical maps \(n:N\to P\) and
\(n_L:N_L\to P_L\). It gives
\[
  \operatorname{range}(n)
    =t^{-1}(\operatorname{range}(n_L)).
\]
No radical identity or radical decomposition is a premise.

The private lemma `range_radical_levi_preimage` combines this comparison with
\(t\,;\,p_L=a\,;\,\rho\). Its reverse inclusion first uses the original
preimage comparison to lift a test point of \(Q\) to \(P\). Monicity of
\(p_L\) then identifies its \(t\)-image with the specified \(N_L\)-point,
so the radical comparison lifts it to \(N\). Thus
\[
  \operatorname{range}(n\,;\,a)
   =\rho^{-1}(\operatorname{range}(n_L\,;\,p_L)).
\]

## Intersection and ordered products

Two further private lemmas work over an arbitrary base scheme. If the range
of \(a:A\to Q\) is the inverse image of the range of \(s:B\to L\), then
`range_levi_intersection_of_preimage` identifies the range of
\(s\,;\,l\,;\,q\) with the intersection of the ranges of \(l\,;\,q\) and
\(a\,;\,q\), for monic \(q:Q\to G\). In the reverse inclusion, cancellation
through \(q\), followed by the identity \(l\,;\,\rho=1\), gives the required
factorization through \(s\).

The lemma `range_product_of_levi_preimage` writes a test point in the range
of \(a\) using its actual Levi and radical components. The preimage comparison
places its Levi component in the range of \(s\). Conversely, applying the
retraction to a product of such a Levi point and a radical point puts the
product in that preimage. After composition with \(q\), this proves equality
with the ordered set product of the two images on each test scheme.

## Assembly of the exact statement

The published rational-Levi data give affineness and connectedness of
\(P,Q,P_L\); their parabolic predicates supply smoothness. The imported
`exists_range_eq_comap_leviRetraction_of_nested_points` uses the prescribed
rational-point containment and intersection to construct \(a:P\to Q\), with
\(a\,;\,q=p\), and the first preimage comparison. This step uses rational-point
density, geometric normal-unipotent containment in a Borel, and fpqc reflection,
as documented in `NestedParabolicPreimage`.

Applying the radical, intersection and product comparisons and evaluating at
the identity test scheme \(\operatorname{Spec} k\) yields
\[
  N_L(k)=L(k)\cap N(k),\qquad
  N(k)=(L(k)\cap N(k))\,U(k),\qquad
  P(k)=P_L(k)\,U(k),
\]
where each displayed subgroup is the image of its original composite map
into \(G(k)\). The products are pointwise products of subsets, with the
outer radical on the right. The common-\(M\) morphism equality and connected
reductivity of \(G\) remain among the exact statement's hypotheses; this
structural proof does not need them.

This is an internal proof of the derived structural statement associated with
Renard 2026, VI.1.4, printed pages 136–137, PDF pages 142–143. It does not
assert a new existence theorem for the three supplied parabolic triples, or
replace the separate dynamic presentation theorem.
