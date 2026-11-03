# Dynamic parabolics are determined by their Lie algebras

Module `Langlands.GroupScheme.Dynamic.ParabolicLieCriterion`. It is derived infrastructure for
clause 2 of `Langlands.GroupScheme.RegularCocharacterBorelStatement` (task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`).

Let `G` be a smooth connected affine group over a field `k`, and let `χ, χ'` be cocharacters
whose points lie in each other's dynamic parabolic. The module proves that `P_G(χ) = P_G(χ')`
exactly when the two Lie algebras `Lie P_G(χ)` and `Lie P_G(χ')` agree, each written as a sum
of nonnegative `𝔾_m`-weight spaces on `Lie(G)`. Subgroup-functor equality holds on every test
scheme.

## Structural inputs

The two criteria take four published statements as explicit hypotheses and do not prove them.
A final proof applies the criteria to the Library proofs of these statements once those
proofs are published.

- `hLie : DynamicLieStatement` (Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), Proposition 2.1.8(1), printed p.53). An element of `lieKernel G k` is a point of
  `Dynamic.parabolic χ` exactly when it lies in `⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)`.
- `hSm : DynamicSmoothStatement` and `hCo : DynamicConnectedStatement` (CGP 2.1.8(3), (4)).
  Representatives of dynamic parabolics of a smooth (connected) affine group are smooth
  (connected).
- `hEq : LieSubgroupEqualityStatement` (Milne, *Algebraic Groups* (2017), Proposition 10.15,
  printed p.190). A smooth closed subgroup of a smooth connected affine group that contains
  the whole Lie algebra is the whole group.

These hypotheses appear only on the lemmas below. They are not premises of any target
statement.

## Contents

- `Lie.reduction_comp_hom`: reduction of `k[ε]`-points commutes with postcomposition by a
  homomorphism. `mem_lieKernel_of_comp`: if `f` is a monomorphism and `y ≫ f` lies in the
  kernel of reduction, then so does `y`.
- `SubgroupFunctor.range_comp_le`: the points of `f ≫ g` are points of `g`.
- `SubgroupFunctor.IsRepresentedBy.liftOfLE` (a definition) and `liftOfLE_comp`. Suppose `i`
  represents a subgroup functor `F` and all points of `f : H' ⟶ G` lie in `F`. Then
  `liftOfLE` is a factorization of `f` through `i`, and `liftOfLE_comp` states
  `liftOfLE ≫ i = f`. This specializes `IsRepresentedBy.lift` to the top subgroup functor of
  `H'`.
- `range_le_centralizer_groupHom_comp`: the points of a commutative subgroup `j : T ⟶ G` lie
  in `Dynamic.centralizer (ν ≫ j)` for every cocharacter `ν` of `T`. The proof uses only
  that `T`'s points commute.
- `parabolic_le_parabolic_of_lieKernel` (Lie criterion for containment). Assume
  `G` smooth, affine and connected, the points of `χ'` in `P_G(χ)`, and every element of
  `lieKernel G k` in `P_G(χ)` also in `P_G(χ')`. Then `P_G(χ) ≤ P_G(χ')`. In the proof, `H`
  is the closed representative `Dynamic.Affine.parabolicHom χ` of `P_G(χ)`, and `H` is smooth and
  connected by `hSm` and `hCo`. The cocharacter `χ'` factors through `H` as `χ'_H` by
  `liftOfLE`. The closed representative `K` of `P_H(χ'_H)` is smooth by `hSm`. As a subgroup
  functor `P_H(χ'_H)` is the preimage of `P_G(χ')` in `H`, by
  `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`. By hypothesis each element of `Lie(H)`
  lies in `P_G(χ')`, so it lifts to `Lie(K)`. Then `hEq` gives that `K` has all points of `H`,
  hence `P_G(χ) ≤ P_G(χ')`.
- `parabolic_eq_iff_iSup_weightSpace_eq`. Let `G` be smooth, affine, locally of finite type
  and connected. If the points of `χ` and `χ'` lie in each other's dynamic parabolic, then
  `P_G(χ) = P_G(χ')` iff
  `⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n) = ⨆ n : ℕ, weightSpace χ' (Gm.powerHom _ n)`.
  The forward direction reads both sides through `hLie`. The reverse direction applies the
  containment criterion in both directions, again through `hLie`.
- `parabolic_comp_eq_iff_iSup_weightSpace_eq`: the case `χ = ν ≫ j` and `χ' = ν' ≫ j` for
  cocharacters `ν, ν'` of a commutative subgroup `j : T ⟶ G`. The mutual containment
  hypotheses follow from `range_le_centralizer_groupHom_comp` and
  `Dynamic.centralizer_le_parabolic`.

## Provenance

This module is derived, not a statement from a source. Milne, *Algebraic Groups* (2017),
Propositions 21.29–21.31 (printed pp.433–434), proves that `P(ν)` depends only on the Weyl
chamber of `ν`. That argument works over an algebraically closed field and uses Borel
theory, `C_G(T) = T` and rank-one groups. The present argument replaces that route by the
Lie-algebra description of dynamic parabolics (CGP 2.1.8) and Milne's Proposition 10.15.
For a regular cocharacter `ν` of a split torus `j : T ⟶ G`, Worker 303's module
`Langlands.GroupScheme.Absolute.RegularCocharacterWeights` identifies the weight-space sum
`⨆ n : ℕ, weightSpace (ν ≫ j) (Gm.powerHom _ n)` (it includes `n = 0`) with
`weightSpace j 0 ⊔ ⨆ (α ∈ roots j, 0 < ⟨α, ν⟩), weightSpace j α`. This is the trivial-weight
space together with the root spaces of the roots positive on `ν`, matching
`𝔱 ⊕ ⨁_{⟨α,ν⟩>0} 𝔤_α` in Milne's Proposition 21.29. Combining that module with
`parabolic_comp_eq_iff_iSup_weightSpace_eq` gives clause 2 of the target, still conditional on
the four inputs above.
