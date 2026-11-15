# Weil-restriction cocycles over Picard-trivial coefficient rings

Let \(A\) and \(B\) be commutative rings with \(B\) a finite projective
\(A\)-algebra. Suppose the module Picard group `CommRing.Pic B` is
subsingleton. Let \(U\to\operatorname{Spec} A\) be an affine, flat,
surjective morphism, and let \(\xi\) be an all-test cocycle on \(U\)
valued in `WeilGm.groupScheme A B`, the Weil restriction of the
multiplicative group.

`weilPicardCochain` constructs a Weil-restriction point \(f\) on \(U\).
`weilPicardCochain_spec` proves, for every test \(Z\) over
\(\operatorname{Spec} A\) and every pair \(a,b:Z\to U\),
\[
  \xi(a,b)=(a^*f)(b^*f)^{-1}.
\]
Consequently, `isTrivial_weil_of_pic_trivial` proves that the original
cocycle is trivial. Affineness is required of the cover morphism; the tests
in the final equation are arbitrary. No flatness, faithful flatness, or
étaleness of \(B/A\) is assumed, and local finite presentation of the cover
is not required.

The construction is internal, derived from the published Weil-restriction
evaluation and Picard coboundary interfaces. First,
`coefficientUnitCocycle` pulls \(\xi\) back to
\(V=U\times_{\operatorname{Spec} A}\operatorname{Spec} B\), applies
`WeilGm.evaluationUnits` on every test over \(\operatorname{Spec} B\),
and represents the resulting units as points of the rank-one split torus.
Functoriality and the evaluation homomorphism prove naturality and the
cocycle equation.

The morphism \(V\to\operatorname{Spec} B\) remains affine, flat and
surjective by base change. The published `splitPicardCochain` therefore
provides a unit \(q\) on \(V\) with the required coboundary law; this is
`coefficientPicardUnit` and its specification. The inverse of
`WeilGm.affineEvaluationEquiv A B U` takes \(q\) back to \(f\).

For affine tests, naturality and injectivity of that equivalence transfer
the unit coboundary equation to the Weil-restriction point equation.
To cover every test, the proof applies this affine result to the universal
pair on \(U\times_{\operatorname{Spec} A}U\), which is affine, and then
pulls it back along the morphism determined by \(a\) and \(b\).
This proves the all-test law without assuming the original test is affine
or that \(\operatorname{Spec} B\to\operatorname{Spec} A\) is a cover.

The module supplies this cochain and cocycle-vanishing result. It does not
assert the reductive-group quasi-split inner-form theorem.
