# Coherent pullback of chosen actual parabolic representatives

Let `G` be a reductive group scheme over any `S : Scheme.{u}`. For a morphism
`a : T ⟶ M` in `Over S`, a parabolic subgroup functor `F` of `G_M`, and a
parabolic subgroup functor `F'` of `G_T` identified with `restrict hG a F`,
`parabolicRepresentativePullbackIso` compares the actual pullback of the chosen
representative of `F` with the chosen representative of `F'`.

The comparison is the existing isomorphism between two groups representing the
same subgroup functor. Its source inclusion is exactly
`familyHom (parabolicRepresentative F).hom a`; its target inclusion is the chosen
inclusion for `F'`. The established parabolicity of the evaluated inclusion
provides monicity. The given equality of restricted subgroup functors identifies
its all-test range with `F'`. The `hom_comp` lemma records compatibility with
these actual inclusions, and `unique` proves that it determines the isomorphism.

For identity restriction the comparison equals `baseChangeIdIso`. For two
successive maps `a : T ⟶ M` and `b : U ⟶ T`, the comparison for `b ≫ a` equals
`baseChangeCompIso a.left b.left` followed by the base change along `b.left` of
the first representative comparison and then the second comparison. The theorem
allows any proofs of the three subgroup identifications, so consumers can use
the equalities furnished by their presheaf formulation.

Both laws follow by uniqueness against the target representing inclusion.
Identity evaluation supplies the identity case. For composition,
the published `TorusSubgroupModuli.familyHom_comp` moves the first representative comparison inside family
evaluation, and `familyHom_evaluate_comp` identifies successive evaluation.
`familySourceComparison_eq_baseChangeCompIso_symm` unfolds the existing source
comparison to the inverse of the standard actual group composition comparison;
the two inverse maps then cancel.

This is internal derived API from actual parabolic restriction,
represented-subgroup uniqueness, and the existing group base-change comparisons.
It makes no constant rank assumption. It supplies the group comparisons needed
for a subsequent determinant construction; it does not construct a determinant
polarization, prove ampleness, or prove global parabolic representability.
