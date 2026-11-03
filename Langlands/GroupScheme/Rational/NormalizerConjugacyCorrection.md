# Correcting rational subgroup conjugacy to normalize a maximal split torus

Worker 1335. This internal construction supplies the conjugacy correction used
in the discussion following Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition,
Lemma C.2.14, printed p.602. It generalizes the existing internal
argument `RelativeWeylSurjective.exists_normalizingPoint_comap_eq` from minimal
reductive parabolics to conjugate closed overgroups of a maximal split torus.
It is derived from the imported group-scheme constructions and retains the
published `SmoothMaximalSplitTorusConjugacyStatement` as an explicit premise.

Let `i : T.toGrp ⟶ G` be maximal split over any field `k`, and let
`j : P ⟶ G`, `j' : Q ⟶ G` be rationally conjugate. Suppose that `Q` is smooth,
affine and connected, and that `j'` is closed. Given actual factorizations
`f ≫ j = i` and `f' ≫ j' = i`, the theorem
`SubgroupConjugate.exists_normalizerPoint_of_factors` provides an actual point
`n : normalizerPoints i` and source isomorphism `E : P ≅ Q` such that
`j ≫ Int(n) = E.hom ≫ j'`. The first inclusion need not be assumed closed in
this factorization form.

The proof starts with the point `g` and source isomorphism `e` of the supplied
subgroup conjugacy. In `Q`, both `f ≫ e.hom` and `f'` are maximal split:
closedness of `j'` and ambient maximality give this by
`IsMaximalSplitTorus.of_comp`. The explicit smooth connected affine conjugacy
premise gives a point `p` of `Q` conjugating those two tori and an isomorphism
of their sources. Then `n = (p ≫ j'.hom.hom) * g` normalizes the original torus,
and `E = e ≪≫ Q.innerIso p` preserves the overgroup conjugacy square. Both
claims follow from the published inner-automorphism composition identities.

`SubgroupConjugate.exists_normalizerPoint` instead assumes both overgroup
inclusions closed and all-test containments of the range of `i` in their
ranges. It constructs the factorizations using `IsRepresentedBy.factorHom`
and applies the preceding theorem.
`SubgroupConjugate.normalizerCorrection` chooses the resulting point and source
isomorphism as a dependent pair with the conjugacy square in its type.

This construction supplies no subgroup conjugacy theorem, no proof of the
smooth maximal split-torus conjugacy statement, and no existence or minimality
of pseudo-parabolic subgroups. It also makes no root movement or reflection
claim. Those are separate geometric inputs to the intended C.2.14 application.
