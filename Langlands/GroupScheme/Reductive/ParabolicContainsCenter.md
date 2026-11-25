# Parabolic subgroups contain the centre; fppf inverse images reflect containment

This module is a helper for the proof of
`AdjointParabolicCorrespondenceStatement` (Conrad, *Reductive group schemes*
(2014), Exercise 5.5.8). It contains clause 1 of that statement and the
descent lemma behind clause 4. Namespace `Langlands.GroupScheme`.

## `SubgroupFunctor.le_range_of_comap_le_of_fppf`

Hypotheses: `q : G ⟶ Q` is a homomorphism of group schemes over `S` whose
underlying morphism is flat, surjective and locally of finite presentation.
`F` is a subgroup functor of `Q`, and `j : H ⟶ Q` is a homomorphism that is a
monomorphism over `S`. Finally, `F.comap q ≤ (range j).comap q`.

Conclusion: `F ≤ range j`.

Proof. Let `x : T ⟶ Q` lie in `F`. Form the pullback `V = T ×_Q G` with
projections `a : V ⟶ T` and `z : V ⟶ G`, so that `a ≫ x = z ≫ q`. The morphism
`a` is a base change of `q`, so it is flat, surjective and locally of finite
presentation. The point `z ≫ q = a ≫ x` lies in `F`, so `z` lies in `F.comap q`
and therefore in `(range j).comap q`. Hence `a ≫ x` lies in `range j`, and
`SubgroupFunctor.mem_range_of_comp_mem_range` (an fppf cover is an effective
epimorphism) gives `x ∈ range j`.

The published `SubgroupFunctor.le_range_of_comap_le` (module
`SubgroupFunctor/FpqcComap`) is the same statement under quasi-compactness of `q`
instead of local finite presentation. An fppf quotient by the centre is not
assumed quasi-compact in the target statement, which is why this variant is
needed.

## `SubgroupFunctor.range_eq_of_comap_eq_of_fppf`

Hypotheses: `q` as above. `j₁ : H₁ ⟶ Q` and `j₂ : H₂ ⟶ Q` are monomorphisms
over `S` with `(range j₁).comap q = (range j₂).comap q`.

Conclusion: `range j₁ = range j₂`.

Proof. Apply the previous lemma in both directions.

## `IsRelativeParabolicSubgroup.center_le_range`

Hypotheses: `G` is reductive over `S`, and `i : P ⟶ G` is a relative parabolic
subgroup (`IsRelativeParabolicSubgroup i`).

Conclusion: `center G ≤ SubgroupFunctor.range i`, i.e. every point of the
all-test centre functor of `G` factors through `P`.

Proof. The published relative centre theorem `reductiveRelativeCenter` gives a
scheme-theoretic centre `z : Z ⟶ G` with `range z = center G`, and `z` is
central (`IsSchemeTheoreticCenter.isCentral`). The published
`IsRelativeParabolicSubgroup.central_range_le` (module
`Reductive/RelativeCentralProductParabolic`) says that the range of every
central homomorphism into a reductive `G` lies in every relative parabolic. So
`center G = range z ≤ range i`.

The two fppf inverse-image lemmas are imported from the shared `SubgroupFunctor/FppfComap` module.
