# A central isogeny onto a semisimple group from a product of almost-simple groups

Author: Worker 162 (Task 6631, with Worker 161).

This module is an internal step toward the proof of
[`SimpleFactorDecompositionStatement`](SimpleFactorDecompositionStatement.md), Conrad's
decomposition theorem for semisimple groups (Theorem 5.1.19). Its main result,
`Langlands.GroupScheme.SimpleFactor.exists_almostSimplePresentation`, gives the existence
part used there: every semisimple group over a field receives a central isogeny from a finite
product of almost-simple groups. It does not prove that the factors are the minimal normal
subgroups, or any uniqueness. All declarations are in the namespace
`Langlands.GroupScheme.SimpleFactor`. The module imports the companion draft module
`Reductive.SimpleFactorPoints` (Worker 161) for `IsCentralIsogeny.id_tensor`,
`comp_commutingSubgroupMultiplicationHom`, `derivedSubgroup_pi_eq_top` and
`isNormal_range_of_image`.

## Main result

`exists_almostSimplePresentation G hG`: for a field `k : Type u` and a group scheme `G` over
`Spec k` with `IsSemisimple G`, there exist a type `I : Type u` with `Finite I`, group schemes
`A i` over `Spec k`, and a homomorphism `mul : pi A ⟶ G` from their categorical product, such
that

- every `A i` is `IsAlmostSimple`;
- for every `i`, the factor map `piFactorInclusionHom A i ≫ mul : A i ⟶ G` is
  `IsClosedSubgroup` (its underlying scheme morphism is a closed immersion);
- for every `i`, `SubgroupFunctor.range (piFactorInclusionHom A i ≫ mul)` is normal in `G`;
- `mul` is `IsCentralIsogeny`.

`I` may be empty; the proof uses an empty `I` when `G` is trivial.

`exists_almostSimplePresentation_aux` is the same statement without the normality clause.

## Proof

**Induction.** `exists_almostSimplePresentation_aux` is proved by the published strong
induction on Lie dimension of smooth connected affine groups,
`smoothConnectedAffineGroup_lieDimension_induction`. A semisimple group is smooth, connected
and affine because it is connected reductive. Let `G` be semisimple.

- If `SubgroupFunctor.range (𝟙 G) = ⊥` (the group is trivial), the empty presentation
  `SimplyConnectedAlmostSimpleProduct.empty` gives an isomorphism `G ≅ pi A` with `I`
  empty. Its inverse is an isomorphism, hence a central isogeny
  (`isCentralIsogeny_of_isIso`); the factor clauses are vacuous.
- If `G` is almost-simple, take `I = PUnit` and `A _ = G`, with `mul` the projection from
  the one-factor product, an isomorphism by `productUniqueIso`. The factor map is
  `piFactorInclusionHom _ _ ≫ π = 𝟙`, a closed immersion.
- Otherwise `G` is nontrivial, so it is noncommutative
  (`IsSemisimple.noncommutative_of_nontrivial`). The negation of `IsAlmostSimple G` then
  gives a smooth connected closed normal subgroup `j : H ⟶ G` whose range is neither `⊥` nor
  `⊤`. The published `semisimpleNormalIsogenyComplement` gives `H` semisimple and a semisimple
  closed subgroup `i : K ⟶ G` whose points commute with those of `H`, and makes the
  commuting multiplication `m = commutingSubgroupMultiplicationHom j i hc : H ⊗ K ⟶ G` a
  central isogeny.

  Neither inclusion is an isomorphism. If `j` were one, its range would be `⊤`. If `i` were
  one, every point of `H` would commute with every point of `G`; since `j` is a monomorphism,
  `H` would be commutative, hence trivial by `noncommutative_of_nontrivial`, and then
  `range j = ⊥`. So `Lie.dimension_lt_of_proper_closedSubgroup` makes the Lie dimensions of
  `H` and `K` smaller than that of `G`, and the induction hypothesis gives presentations
  `mul₁ : pi A₁ ⟶ H` and `mul₂ : pi A₂ ⟶ K`.

  The new index type is `I₁ ⊕ I₂` with the family `sumGroupFamily A₁ A₂`, and
  `mul = (finiteProductSumIso A₁ A₂).inv ≫ (mul₁ ⊗ₘ mul₂) ≫ m`.
  - The factors are almost-simple by the two induction hypotheses.
  - For a left index `a`, `piFactorInclusionHom_inl_comp_finiteProductSumIso_inv` and
    `lift_zero_comp_commutingSubgroupMultiplicationHom` rewrite the factor map to
    `(piFactorInclusionHom A₁ a ≫ mul₁) ≫ j`, a composite of closed immersions. Right indices
    are symmetric, ending in `i`.
  - `mul₁ ⊗ₘ mul₂` is a central isogeny by `IsCentralIsogeny.tensorHom`, and so is its
    composite with the isomorphism `(finiteProductSumIso A₁ A₂).inv`
    (`IsCentralIsogeny.iso_comp`). Each factor is almost-simple, hence semisimple, hence
    perfect (`semisimplePerfect`), so the product has derived subgroup `⊤`
    (`derivedSubgroup_pi_eq_top`). `IsCentralIsogeny.comp_of_derivedSubgroup_eq_top` then makes
    the composite with the central isogeny `m` central.

**Normality.** `exists_almostSimplePresentation` adds the normality clause with
`isNormal_range_of_image`, applied to the finite, flat, surjective `mul`, the identity of
`A i`, the factor inclusion `piFactorInclusionHom A i` (whose range is normal in the product by
`isNormal_range_piFactorInclusionHom`), and the closed immersion
`piFactorInclusionHom A i ≫ mul`. So the image of a normal subgroup under the central isogeny
`mul` is normal.

## Auxiliary lemmas

- `IsCentralIsogeny.tensorHom`: if `f : C ⟶ H` and `g : C' ⟶ H'` are central isogenies of
  group schemes over any base scheme, so is `f ⊗ₘ g`. It writes
  `f ⊗ₘ g = (f ⊗ₘ 𝟙) ≫ (𝟙 ⊗ₘ g)`, uses the published `IsCentralIsogeny.tensor_id` and
  `IsCentralIsogeny.id_tensor` for the isogeny and finite-presentation parts, and checks the
  kernel is central coordinatewise: a point in the kernel has its two coordinates in the
  kernels of `f` and `g`.
- `lift_zero_comp_commutingSubgroupMultiplicationHom` and
  `lift_zero_left_comp_commutingSubgroupMultiplicationHom`: for `p : P ⟶ H`,
  `lift p 0 ≫ commutingSubgroupMultiplicationHom j i hc = p ≫ j`, and for `q : P ⟶ K`,
  `lift 0 q ≫ commutingSubgroupMultiplicationHom j i hc = q ≫ i`. Both are checked on
  points.
- `finiteProductSumIso_inv_fst` and `finiteProductSumIso_inv_snd`: the two components of
  `(finiteProductSumIso A B).inv` are the restrictions of the product over `I ⊕ J` to the
  left and right indices.
- `piFactorInclusionHom_inl_comp_finiteProductSumIso_inv` and
  `piFactorInclusionHom_inr_comp_finiteProductSumIso_inv`: inserting a left factor `a` of the
  product over `I ⊕ J` and passing to `pi A ⊗ pi B` equals
  `piFactorInclusionHom A a ≫ lift (𝟙 (pi A)) 0`; similarly on the right with
  `lift 0 (𝟙 (pi B))`. Both are checked coordinatewise with `piFactorInclusionHom_π_self` and
  `piFactorInclusionHom_π_ne`.

## Provenance

The theorem is the existence half of Conrad, *Reductive group schemes* (2014), Theorem 5.1.19,
p.150 (registered as `conrad-2014-reductive-group-schemes`): the multiplication map from the
product of the `G_i` to `G` is a central isogeny. Conrad's proof (pp.150–151) uses the split
case (Proposition 5.1.17) and Galois descent. The Lean proof takes a different route: an
induction on dimension that splits off a normal subgroup and its commuting complement, using
the published `semisimpleNormalIsogenyComplement`. Its structure follows the published
Lie-dimension induction in
[`SimplyConnected.AlmostSimpleProduct`](../SimplyConnected/AlmostSimpleProduct.md), which proves
the simply connected case with an isomorphism instead of a central isogeny. The statement form
and the auxiliary lemmas are internal to this proof and have no separate literature source.
