# Proof of the solvable radical and centre comparison

`reductiveRadicalCenter` proves `ReductiveRadicalCenterStatement`, the
comparison of Renard, *Représentations des groupes réductifs p-adiques*,
V.2.1 (printed p. 104) and the torus assertion of V.2.2 (printed p. 105).

## Torus and centrality over the ground field

The proof applies the published radical structure theorem
`IsGeometricSolvableRadical.isTorus_and_isCentral_of_structural` to
`algClosedReductiveNormalSolvableTorus`. That theorem applies the
algebraically closed result to the base change of the radical, which is a
smooth connected solvable normal closed subgroup of the pseudo-reductive
group \(G_{\bar k}\), so the base change is a central torus. It then descends
both properties to \(k\). The torus property descends by `IsTorus.of_baseChange`,
and centrality is reflected along the faithfully flat map to the algebraic
closure by `IsCentral.of_baseChange`.

## The radical lies in the reduced identity component of the centre

Over \(\bar k\), let \(z : Z \to G_{\bar k}\) represent the scheme-theoretic
centre and let \(j\) be `ReducedSubgroup.identityCoreι Z ≫ z`. The base change
of the central map \(r\) is central (`IsCentral.baseChange`), so its subgroup
functor is contained in
`center`, which is the range of \(z\). The lemma
`SubgroupFunctor.exists_factor_of_range_le` turns this containment into a
factorization of \(r_{\bar k}\) through \(z\).

The radical over \(\bar k\) is smooth, so its source is reduced by
`isReduced_of_smooth_over_field`. The factorization therefore lifts through
the reduction of \(Z\) by `ReducedSubgroup.liftHom`. The source is also
connected, so `IdentityComponent.factor` factors the lift through the identity
component. The resulting factorization of \(r_{\bar k}\) through \(j\) gives
the first containment of ranges by `SubgroupFunctor.range_le_of_factor`.

## The reduced identity component of the centre lies in the radical

The map \(j\) is a closed immersion, as a composite of closed immersions, and
its source is smooth and connected. It is central, being the composite of the
central map \(z\) with an inclusion (`IsCentral.comp`). Centrality makes its
source commutative through `IsCentral.commGroupScheme`, hence solvable by
`isSolvableGroupScheme_of_isCommMonObj`, and makes its range normal by
`IsCentral.range_isNormal`. The maximality field `IsSolvableRadical.greatest`
of the radical over \(\bar k\) then gives the reverse containment.

Both containments compare subgroup functors of the original embeddings on all
test schemes over \(\bar k\), so the two ranges are equal.
