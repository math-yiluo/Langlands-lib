# Transporting the geometric Borel witness of a parabolic subgroup

Worker 445.

This internal construction transports the actual factorization used by
`IsParabolicSubgroup` through a comparison of two iterated base-change
functors. It does not prove preservation of Borel subgroups under field
extension or the unconditional `ParabolicFieldExtensionStatement`.

Let `b : Spec K ⟶ Spec k` be a morphism between the spectra of fields,
and let `c : Spec (AlgebraicClosure K) ⟶
Spec (AlgebraicClosure k)`. The input `e` is a natural isomorphism from
base change first to the chosen closure of `k` and then along `c`, to
base change first along `b` and then to the chosen closure of `K`.
This module assumes that comparison; it does not construct the field
embedding, its compatibility with `b`, or the comparison itself.

For a factor `f : B ⟶ P_k̄`, `baseChangeBorelFactor` is the composite
`c*(f) ≫ e_P.hom`. Its source is the actual base-changed group `c*(B)`,
and its target is the actual iterated base change `(P_K)_K̄`.
`baseChangeBorelFactor_comp` applies naturality of `e` to the original
inclusion `i : P ⟶ G` and preservation of composition by the base-change
functor. The resulting factorization has ambient map
`c*(j) ≫ e_G.hom`, where `j = f ≫ i_k̄`.

`IsParabolicSubgroup.baseChange_of_geometricBorel` takes an additional,
explicit premise: every Borel embedding into `G_k̄` remains Borel under
base change along `c`. It applies that premise to the witness in the
original parabolic predicate, and uses
`IsBorelSubgroup.comp_iso` to transport the ambient target along `e_G`.
The preceding factorization theorem supplies the required equality.
The other two fields of the parabolic predicate follow from the
published `IsClosedSubgroup.baseChange` theorem and Mathlib's stability
of smoothness under pullback.

The construction works at arbitrary universe `u`. It uses the existing
group schemes, homomorphisms and geometric predicates without altering
them. Its provenance is the indicated composition of published
definitions, isomorphism transport and functor naturality. It introduces
no new assertion from the literature. The natural comparison and the
geometric Borel-preservation premise remain obligations for an
unconditional field-extension proof.
