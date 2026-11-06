# Rational points of the three-factor cell are dense

This derived internal support module bridges the published triple-cell open
immersion and the rational-point closure interface. Work over a field
`k : Type u`, with group schemes `H`, `M`, `Z`, `A` over `Spec k`. A rational
point of `H` is a morphism over `Spec k` from the identity object
`Over.mk (𝟙 (Spec k))` to `H.X`. Rational points form a group under the actual
group-scheme multiplication.

## Declarations

- `rationalTripleProduct m z a`: for morphisms of group schemes `m : M ⟶ H`,
  `z : Z ⟶ H`, `a : A ⟶ H`, this is the set of rational points of `H` of the
  form `x * y * w`. Here `x`, `y`, `w` are rational points of `H` in the range
  functors `SubgroupFunctor.range m`, `SubgroupFunctor.range z`,
  `SubgroupFunctor.range a`, evaluated at the identity object. The set is the
  pointwise product of these three sets of rational points.
  `rationalTripleProduct_eq` unfolds the definition (by `rfl`).
- `mem_rationalTripleProduct_of_mem_range`: suppose the underlying scheme
  morphism of `Dynamic.tripleCellMultiplication m z a :
  M.X ⊗ (Z.X ⊗ A.X) ⟶ H.X` is an open immersion. Then every rational point of
  `H` whose location (the image of the closed point of `Spec k`) lies in the
  image of that morphism belongs to `rationalTripleProduct m z a`.
- `rationalPointClosure_rationalTripleProduct_eq_univ`: let `k` be
  algebraically closed and `H.X ⟶ Spec k` locally of finite type. If the cell
  multiplication is an open immersion and dominant (`IsDominant`), then
  `rationalPointClosure H (rationalTripleProduct m z a) = Set.univ`. In other
  words, the location of every rational point of `H` lies in the Zariski
  closure of the locations of the rational triple products.
- `rationalPointClosure_dynamicTripleProduct_eq_univ`: let `k` be algebraically
  closed and `H` smooth, affine and connected. Let
  `χ : Gm(Spec k).toGrp ⟶ H` be a cocharacter. Suppose `m`, `z`, `a` represent
  `Dynamic.unipotent (−χ)`, `Dynamic.centralizer χ` and `Dynamic.unipotent χ`
  (`IsRepresentedBy`), where `−χ` is `χ` precomposed with
  `Gm.powerHom (-1)`. Then
  `rationalPointClosure H (rationalTripleProduct m z a) = Set.univ`.
  The hypotheses `hm`, `hz`, `ha` have exactly the form used in
  `Dynamic.isOpenImmersion_tripleCellMultiplication`. `Z` is arbitrary, so a
  torus `t : T.toGrp ⟶ H` whose inclusion represents `Dynamic.centralizer χ`
  is a special case.

## Proofs

`mem_rationalTripleProduct_of_mem_range`. The underlying space of `Spec k` is a
single point. So the range of the given rational point `x` lies in the image of
the open immersion `c = tripleCellMultiplication m z a`.
`IsOpenImmersion.lift` factors `x.left` through `c.left`. The factorization
commutes with the structure morphisms, so it is a rational point `y` of the
product `M.X ⊗ (Z.X ⊗ A.X)` with `y ≫ c = x`. Split `y` into its three
components. Then `Dynamic.lift_tripleCellMultiplication` writes `x` as the
product of the compositions of these components with `m`, `z`, `a`. Each of
these compositions lies in the corresponding range functor by definition.

`rationalPointClosure_rationalTripleProduct_eq_univ`. `H.X` is locally of
finite type over a field, so it is a Jacobson space
(`LocallyOfFiniteType.jacobsonSpace`). To show that the locations of
`rationalTripleProduct m z a` are dense, take a nonempty open set `U`. `c.left`
has dense range, so `U` meets the image of `c.left`. That image is open, so the
intersection is a nonempty open, hence locally closed, set. In a Jacobson space
such a set contains a closed point `y` (`nonempty_inter_closedPoints`). Since
`k` is algebraically closed, `pointOfClosedPoint` gives a rational point `p`
located at `y`. By the previous lemma, `p` lies in the triple product. So `U`
meets the locations of the triple product. The closure of a dense set is
everything, and this gives the equality.

`rationalPointClosure_dynamicTripleProduct_eq_univ`. Smooth morphisms are
locally of finite type, so the previous theorem applies. Its open-immersion
hypothesis is the published `Dynamic.isOpenImmersion_tripleCellMultiplication`,
and its density hypothesis is the published
`Dynamic.isDominant_tripleCellMultiplication`. Both use the same `χ`, `hm`,
`hz`, `ha`.

## Provenance and scope

This is an internal derivation from Library and Mathlib results; no
literature statement is formalized here. It supplies the rank-one input in
the proof of Milne, *Algebraic Groups* (2017), Proposition 23.22, printed
p.491 (PDF p.507). There, for a simple root `α`, the product `U''_α U''_{−α}`
lies in `G''_α`, and `G''_α` lies in the closure of `U''_{−α} T'' U''_α`.
Applied with `H = G''_α` and `χ` a cocharacter for which `U(χ) = U''_α`,
`U(−χ) = U''_{−α}` and `Z(χ) = T''`, the last theorem gives the rational-point
form of this containment. The open-cell input, `U(−χ) Z(χ) U(χ)` open in `H`,
is the published `Dynamic.isOpenImmersion_tripleCellMultiplication`. Its
density in a smooth connected group is the published
`Dynamic.isDominant_tripleCellMultiplication`. The passage from density of an
open subscheme to density of its rational points uses the Nullstellensatz:
closed points are dense in the locally closed subsets of a scheme locally of
finite type over a field, and over an algebraically closed field they are
rational.

The module identifies no torus with a centralizer, constructs no graph group,
and proves neither `SplitCommonTorusLeviGluingStatement` nor
`SplitCommonTorusIsomorphismStatement`.
