# The quotient of a cyclic weight subgroup by the next one

Let `k` be a field and `G` a group scheme over `Spec k` with an isomorphism
`ψ : groupScheme F e ≅ G` from a corepresented model, whose representing algebra `B` is
formally smooth and of finite type. Let `S` be a torus with splitting
`φ : S.toGrp ≅ splitTorus I`, and `b : AutomorphicAction S.toGrp G`. This module assembles
the conclusion of `CyclicWeightFiltrationStatement` for `G` from the weight subgroup functors
`weightSubgroupFunctor e ψ φ b P` (`Rational.CyclicWeightSubgroups`). All declarations are in
namespace `Langlands.GroupScheme.RelativeRoot`.

## Statements

- `exists_quotient_of_weightFiltration_eq`: let `a` be a character with nonzero exponent vector
  `a' = characterExponents φ a`, and `r > 0`. Assume:
  - `hWr`, `hWr1`: `weightFiltration b a r` and `weightFiltration b a (r + 1)` are the weight
    subgroup functors of the cyclic tails `cyclicTail a' r` and `cyclicTail a' (r + 1)`;
  - `hsharp`: on every test scheme `T`, the transported action `b.transport φ.inv ψ` is the
    model torus action at the unit coordinates `splitTorus.pointsEquiv I T s`.

  Then every representative `j : H ⟶ G` of `weightFiltration b a r` has the following data:
  - a vector group `V = VectorGroup.groupScheme k N`;
  - `q : H ⟶ V` with `IsFppfQuotient ((weightFiltration b a (r + 1)).comap j) q`;
  - the action `c = VectorGroup.weightAction (r • a)` of weight `r • a`, with
    `HasUniqueWeightVectorStructure c (r • a)`;
  - an action `d` of `S` on `H` lifting `b` along `j`, intertwined with `c` by `q` on all
    test schemes.
- `cyclicTail_subset_of_le`, `cyclicTail_add_mem`: the tails decrease, and adding an element of
  a tail to an element of a smaller tail stays in the smaller tail.
- `cyclicWeightFiltration_of_model`: the full conclusion of
  `CyclicWeightFiltrationStatement` for `G`, `b`, `a ≠ 0` and `r > 0`. Besides the standing
  data it assumes only that `G` and the model `groupScheme F e` are affine over the base
  (`IsAffineHom`) and that `B` is formally smooth and of finite type over `k`; `ψ` and `φ` are
  explicit arguments although they do not occur in the conclusion.

## Proofs

`exists_quotient_of_weightFiltration_eq` uses the following ingredients.
- By `hWr`, `weightFiltration b a r` is represented by `cutHom hJ ≫ ψ.hom` for the cut group
  scheme of the weight ideal (`isRepresentedBy_cutHom`, `IsRepresentedBy.comp_iso`).
  `isoOfIsRepresentedBy` gives `θ : H ≅ cutGroupScheme hJ` with `θ.hom ≫ cutHom hJ ≫ ψ.hom = j`.
- `exists_isFppfQuotient_cyclicTail` (`Rational.TorusWeightQuotient`) gives primitive
  coordinates `y` of weight `r • a'`. It also gives `IsFppfQuotient M (VectorGroup.quotientMap hy)`
  for `M = (weightFiltration b a (r + 1)).comap (cutHom hJ ≫ ψ.hom)`; the points of `M` are
  identified by `hWr1` and `groupSchemeMap_points`. The Library's `IsFppfQuotient.comapIso`
  along `θ.symm`, with `SubgroupFunctor.comap_comp`, gives the quotient statement for
  `q = θ.hom ≫ VectorGroup.quotientMap hy`.
- `r • a ≠ 0`, because its exponent vector is `r • a' ≠ 0` (`nsmul_ne_zero_of_pos`). So
  `VectorGroup.hasUniqueWeightVectorStructure_weightAction` (Worker 1239) applies to
  `c = VectorGroup.weightAction (r • a)`.
- `d = AutomorphicAction.onRepresentedSubgroup b j hj hstab`, where `hstab` is the `b`-stability
  of the filtration (`hWr`, `isStable_weightSubgroupFunctor`). Its lifting property is
  `onRepresentedSubgroup_act_comp`.
- Intertwining is checked on vector coordinates (`VectorGroup.points_ext`). The `i`-th
  coordinate of `h ≫ q` is the value of the primitive coordinate `y i` at the point of the
  cut group below `h` (`VectorGroup.coordinates_quotientMap`). For `d.act s h`, that point
  of the model is `b.transport φ.inv ψ` acting by `s ≫ φ.hom` (cancel `ψ.hom`, then use the
  lifting property and `AutomorphicAction.transport_act`). By `hsharp` this is the model torus
  action. Writing `y i` as the image of a weight component of weight `r • a'`
  (`exists_eq_mk_comp`), `coord_act_of_isHomogeneous` multiplies its value by the exponent
  value of `r • a'`. By `pointsEquiv_characterExponents` this equals `VectorGroup.charValue
  (r • a)`, the scalar by which `c` acts.

`cyclicWeightFiltration_of_model` first proves, for every `n`, the two hypotheses of
`weightFiltration_eq_weightSubgroupFunctor` from Worker 1239's Lie-algebra lemmas
(`Rational.TorusWeightLie`), translated between characters and exponent vectors by
`mem_cyclicTail_characterExponents`:
- the support hypothesis from `actionWeightSupport_comap_weightSubgroup_subset` (the action
  weights of the weight subgroup functor of `P` have exponent vectors in `P`);
- the rigidity hypothesis `TangentRigid` for each generator `F'` from
  `tangentRigid_of_actionWeightSupport_subset`, applied to the support condition of `F'`.

This identifies all members of the filtration with weight subgroup functors. Normality is then
`weightSubgroupFunctor_isNormalizedBy` with `P = A_1`, `P' = A_r`. The quotient part is
`exists_quotient_of_weightFiltration_eq`, with `hsharp` supplied by `pointsEquiv_act`
(`Rational.TorusActionPoints`).

## Provenance

Internal assembly for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af), following
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Lemma 3.3.8 (printed pp.111-112). There,
`U_{A_j}(G)` is normal in `U_A(G)` and `U_{A_j}(G)/U_{A_{j+1}}(G)` is a vector group with unique
`S`-equivariant linear structure of weight `j a`. The quotient is constructed explicitly here;
the uniqueness is Worker 1239's published theorem. The identification of the filtration with
explicit weight subgroups (maximality through tangent rigidity) is internal to this
formalization.
