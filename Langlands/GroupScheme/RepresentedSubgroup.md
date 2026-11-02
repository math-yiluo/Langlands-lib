# Points of representing group schemes, and homomorphisms between them

A homomorphism of group schemes `i : H ⟶ G` over a scheme `S` *represents* a subgroup functor `F`
of `G` (the published `SubgroupFunctor.IsRepresentedBy F i`) when `i` is a monomorphism of
schemes over `S` and its points are exactly the points of `F` on every test scheme. This module
makes this usable:

- the points of `H` are identified with the points of `F`, as groups and naturally in the test
  scheme;
- a natural family of homomorphisms between the points of two represented subgroup functors
  comes from a unique homomorphism of the representing group schemes;
- two group schemes representing the same subgroup functor are isomorphic over `G`.

## Provenance

This is internal infrastructure, with no literature source of its own. It is the Yoneda lemma
for group objects in `Over S`. Mathlib proves that lemma as `yonedaGrpFullyFaithful`, the full
faithfulness of the functor `yonedaGrp` from group objects to presheaves of groups. The module
specializes it to the published representability notion of
`Langlands.GroupScheme.SubgroupFunctor`. It is used for the scheme-level decomposition in
[`Dynamic/SchemeDecomposition`](Dynamic/SchemeDecomposition.md).

## Declarations (namespace `Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy`)

Fix `hi : F.IsRepresentedBy i` with `i : H ⟶ G`.

- `pointsHom hi T : (T ⟶ H.X) →* F.carrier T` sends a point `x` of `H` to `x ≫ i`. It is a
  group homomorphism because `i` is a homomorphism of group objects (Mathlib's
  `MonObj.one_comp` and `MonObj.mul_comp`).
- `pointsEquiv hi T : (T ⟶ H.X) ≃* F.carrier T` is `pointsHom` as an isomorphism. It is
  injective because `i` is a monomorphism, and surjective because the range of `i` is `F`.
  - `pointsEquiv_apply_coe`: its value is `x ≫ i`.
  - `pointsEquiv_symm_comp`: the inverse followed by `i` is the original point.
  - `pointsEquiv_comp`: it is natural in the test scheme.
- `pointsNatTrans hi hj φ hφ`. Let `hj : K.IsRepresentedBy j` with `j : H' ⟶ G'`, let
  `φ T : F.carrier T →* K.carrier T` be group homomorphisms, and let `hφ` say they commute with
  restriction along every `T' ⟶ T`. Then `pointsNatTrans` is the corresponding natural
  transformation `yonedaGrp.obj H ⟶ yonedaGrp.obj H'` of group-valued point functors.
- `lift hi hj φ hφ : H ⟶ H'` is the homomorphism of group schemes obtained from
  `pointsNatTrans` by Mathlib's `yonedaGrpFullyFaithful.preimage`.
  - `pointsEquiv_lift` and `lift_comp`: on points, `lift` is `φ`, that is,
    `(x ≫ lift) ≫ j = φ (x ≫ i)`.
  - `lift_comp_eq`: any homomorphism `f : H ⟶ G'` that acts on points as `φ` equals
    `lift ≫ j`.
- `hom_ext hj`: two homomorphisms into `H'` that agree after `j` are equal, because `j` is a
  monomorphism.
- `isoOfIsRepresentedBy hi hi₂ : H ≅ H₂` for two group schemes representing the same `F`. It
  is built from `lift` of the identity families in both directions.
  `isoOfIsRepresentedBy_hom_comp` says it commutes with the inclusions into `G`.

No hypothesis on `S`, `G` or `H` is needed.
