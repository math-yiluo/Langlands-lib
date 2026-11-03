# The reduced subgroup and its identity component

Author: Worker 1399. This is a helper module for the proof of
`Langlands.GroupScheme.SomeBorelQuotientProperStatement` (task
`26c798aa-c7cc-4a23-94b9-235cc57dc70c`). It is step (D) of Worker 1396's plan:
inside a closed subgroup `S` of an affine group `G` over an algebraically closed
field `k`, find a smooth connected closed subgroup `H`, open in `S`, that contains
every smooth connected closed subgroup of `G` lying in `S`. Classically
`H = (S_red)⁰`. Over a perfect field, `S_red` is an algebraic subgroup of `S`
(Milne, *Algebraic Groups*, 2017, Proposition 1.38 and Corollary 1.39). It is smooth
because it is reduced over a perfect field (Proposition 1.26). Milne gets reducedness of
`S_red × S_red` from geometric reducedness. Mathlib lacks "reduced over a perfect field
implies geometrically reduced", so the Lean proof first proves `S_red` smooth, from
homogeneity, and gets reducedness of the product from that.

## The reduced closed subscheme of a scheme

For a scheme `X`, `red X` is the closed subscheme cut out by Mathlib's
`vanishingIdeal ⊤`, which is the nilradical. `redι X : red X ⟶ X` is its inclusion.

- `redι` is a closed immersion, and `red X` is reduced. Both facts come from the
  Library's `Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`.
- `range_redι`: `redι` is surjective. Its range is the support of the nilradical,
  which is the whole space. So `redι` is a bijective closed embedding (`redι_surjective`,
  `redι_injective`), and `isOpen_image_redι` says it maps open sets to open sets.
- `redLift f` factors a morphism `f : T ⟶ X` with `T` reduced through `redι X`
  (`redLift_fac`). The kernel of `redι X` is the nilradical, which lies in the kernel
  of every map from a reduced scheme.
- `redIso e : red X ≅ red Y` is the restriction of an isomorphism `e : X ≅ Y`,
  with `redIso_hom_redι`.

## The reduced subgroup

Let `S` be a group scheme over `Spec k`. `redOver S` is `red S.X.left`, viewed over
`k`, and `redOverι S : redOver S ⟶ S.X` is its inclusion. `liftOver` factors a
morphism over `k` from a scheme with reduced underlying scheme through `redOverι`.

From now on `k` is algebraically closed and `S` is locally of finite type.

- `point_comp_mulRight` holds for any group object `A` in a cartesian monoidal
  category: for points `x, y : 𝟙 ⟶ A`, right translation by `x⁻¹ y` sends `x` to `y`.
  The proof is Mathlib's computation in `AlgebraicGeometry/Group/Smooth.lean`.
- `exists_translation`: for closed points `x, y` of `S`, some automorphism of
  `S.X.left` over `k` sends `x` to `y`. Mathlib's `pointEquivClosedPoint` turns `x`
  and `y` into `k`-points. The automorphism is right translation by `x⁻¹ y`.
- `smooth_redOver`: `S_red` is smooth over `k`. It is reduced and locally of finite
  type over `k`. Each translation from `exists_translation` restricts to an
  automorphism of `S_red` through `redIso`. Closed points of `S_red` map to closed
  points of `S`, because `redι` is a closed embedding, and `redι` is injective. So
  the automorphisms of `S_red` over `k` act transitively on its closed points. The
  Library's `closedPointHomogeneousSmooth` then gives smoothness.
- `S_red ×_k S_red` is smooth over `k`, so it is reduced
  (`SmoothReducedProof.isReduced_of_smooth_over_field`). `Spec k` is reduced too. So the
  unit, the multiplication and the inverse of `S`, restricted to `S_red`, factor
  through `S_red` by `liftOver`. The results are `redOne`, `redMul` and `redInv`, with
  `redOne_fac`, `redMul_fac` and `redInv_fac`.
- `grpObj_redOver` makes `S_red` a group object by the Library's
  `GroupObjectDescent.grpObjOfMono`, since `redOverι` is a monomorphism. `redOverι` is
  then a monoid homomorphism.
- `reducedSubgroup S` is this group scheme, and `reducedSubgroupι S` is its inclusion
  into `S`. The inclusion is a closed immersion. `reducedSubgroup S` is smooth, and it
  is affine over `k` when `S` is.
- `liftHom g` factors a homomorphism `g : K ⟶ S` through `reducedSubgroupι S` when
  `K` has reduced underlying scheme (`liftHom_fac`). The underlying morphism is
  `liftOver g`. It is a monoid homomorphism because `redOverι` is a monomorphism and
  both `g` and `redOverι` are monoid homomorphisms.

## The identity component

`exists_reducedIdentityComponent`: let `G` be a group scheme over `Spec k` with `k`
algebraically closed. Assume `G` is locally of finite type and affine over `k`. Let
`iS : S ⟶ G` be a closed subgroup. Then there are a group scheme `H` and
`f : H ⟶ S` such that:

- `f ≫ iS` is a closed subgroup;
- `H` is smooth over `k`, and its underlying space is connected;
- the range of `f` on underlying spaces is open in `S`;
- every closed subgroup `iK : K ⟶ G` with `K` smooth and connected and
  `range iK ≤ range iS` factors as `e ≫ f ≫ iS = iK` for some `e : K ⟶ H`.

Here `range` is the subgroup functor of points (`SubgroupFunctor.range`).

Proof. `S` inherits finite type and affineness from `G` through the closed immersion
`iS`. Take `H = identityComponent (reducedSubgroup S)` and
`f = identityComponentι ≫ reducedSubgroupι S`. The Library's
`Langlands.GroupScheme.IdentityComponent` module applies, since `S_red` is smooth and
affine. It makes `H` smooth and connected, with `identityComponentι` an open and closed
immersion. So `f ≫ iS` is a composite of closed immersions. The range of `f` is the
image under `redι` of an open set, which is open by `isOpen_image_redι`. For the
factorization, `SubgroupFunctor.exists_factor_of_range_le` gives `g : K ⟶ S` with
`g ≫ iS = iK`. Smooth `K` is reduced, so `liftHom g : K ⟶ S_red`. Since `K` is
connected, `IdentityComponent.factor` factors it through `H`.

The theorem assumes only that `G` is locally of finite type and affine over `k`, not
that it is smooth. Step 5 of `someBorelQuotientProper_of_prerequisites` (module
`Langlands.GroupScheme.Absolute.BorelProperQuotientReduction`) applies it to a smooth
affine `G`; `Smooth` implies `LocallyOfFiniteType`.
