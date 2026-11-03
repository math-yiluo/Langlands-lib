# Proof: the closure of a group of rational points is a smooth closed subgroup

Module `Langlands.GroupScheme.Absolute.RationalPointClosureProof` proves

```lean
theorem Langlands.GroupScheme.rationalPointClosureSubgroup :
    RationalPointClosureSubgroupStatement.{u}
```

Let `k` be an algebraically closed field, `H` an affine group scheme over `Spec k` that is
locally of finite type, and `Γ` a subgroup of the `k`-points of `H`. The theorem gives a smooth
group scheme `Z` over `k` and a closed subgroup `ζ : Z ⟶ H` whose underlying set is the
Zariski closure of the points where the elements of `Γ` are located. This is the
reduced-closure part of Milne, *Algebraic Groups* (2017), Lemma 1.40 and Theorem 1.45, with
Proposition 1.26(b) for smoothness. Milne takes the
reduced closed subscheme on the closure and shows it is a subgroup. The Lean proof does not
follow that route: it cuts out `Z` with an ideal and checks the subgroup property on functors of
points.

## Coordinates

`H.X` is affine, so `essImage_algSpec` gives a commutative `k`-algebra `B` and an isomorphism
`j : algSpec (op B) ≅ H.X`. The Library's
`AffineLinearEmbedding.corepresentableBy H j` makes `B` corepresent the points of `H` over
commutative `k`-algebras. `AffineLinearEmbedding.modelIso H j` identifies the group scheme
corepresented by `B` with `H`. `Γ` is moved along the isomorphism `Spec k ≅ algSpec k` to a
subgroup `Γ'` of the points with values in `k`.

## The cut-out subgroup (section `Core`, general corepresented group functors)

The section works for any functor `F` from commutative `k`-algebras to groups that is
corepresented by `B` (via `e`), and any subgroup `Γ` of `F k`.

- `vanishingIdeal e Γ` is the intersection of the kernels of the classifying maps `B → k` of
  the points of `Γ`. `cutSet e Γ A` is the set of points over `A` whose classifying maps kill this
  ideal. `cutSet` is stable under every `F.map`.
- `universalPoint` is the point over the quotient `Q = B ⧸ I` classified by the quotient map.
  A point lies in `cutSet` exactly when it is the image of the universal point under some
  algebra map out of `Q` (`mem_cutSet_iff`, via `Ideal.Quotient.liftₐ`).
- Separation: the maps `Q → k` lifting the points of `Γ` separate the elements of `Q`
  (`eq_zero_of_forall_lift`). `tensor_eq_zero_of_separating` shows that the tensor products
  of pairs of such maps separate `Q ⊗[k] Q`. It expands an element in `b ⊗ q` form over a
  `k`-basis `b` of `Q` and uses linear independence.
- `mem_cutSet_of_separating`: if a separating family of maps `A → k` sends a point to `Γ`,
  then the point lies in `cutSet`. This gives:
  - the inverse of the universal point lies in `cutSet` (test with the lifts of `Γ`; `Γ` is
    closed under inverses);
  - the product of the two pullbacks of the universal point to `Q ⊗ Q` lies in `cutSet`
    (test with the maps `pairLift`; `Γ` is closed under products).

  Every point of `cutSet` is an image of the universal point, so `cutSet` is closed under
  products and inverses. It contains `1` because `1` is the image of `1 ∈ Γ`.
- `closureSubgroup e Γ` collects these subgroups, and `isCutOutBy_closureSubgroup` holds by
  definition. `isReduced_quotient` says `Q` is reduced: each lift `Q → k` kills a nilpotent
  element, so the separation lemma makes it zero.

## Geometry

- `Z := Corepresented.cutGroupScheme hI` and `ζ := cutHom hI ≫ (modelIso H j).hom`.
  `modelIso_hom_hom_hom` shows that the scheme map underlying `modelIso H j` is `j.hom`. It
  evaluates the Yoneda preimage at the identity point. So `ζ.left = cutHom.left ≫ j.hom.left`.
  This is a closed immersion because `Corepresented.isClosedImmersion_cutHom` holds and `j` is
  an isomorphism.
- Smoothness: `Z.X.left = Spec Q` is reduced, and `Z.X.hom` is locally of finite type because
  `Z.X.hom = ζ.left ≫ H.X.hom`, where `ζ.left` is a closed immersion. The lemma
  `smooth_of_grpObj_of_isAlgClosed` then applies: a reduced group scheme locally of finite type
  over an algebraically closed field is smooth. That lemma is private in Mathlib
  (`Mathlib/AlgebraicGeometry/Group/Smooth.lean`, by Andrew Yang, Apache 2.0). The module
  contains a verbatim copy under the same name in namespace
  `Langlands.GroupScheme.RationalPointClosure`, with the same local options.
- Range: `Corepresented.cutHom_left` identifies `cutHom.left` with
  `Spec.map (Ideal.Quotient.mk I)`. Its range is `zeroLocus I`
  (`range_comap_of_surjective`, `Ideal.mk_ker`). Let `S ⊆ Spec B` be the set of points
  classified by the elements of `Γ'` (`classifiedPoint`: the comap of the maximal ideal of `k`).
  Then `vanishingIdeal S = I` (`mem_asIdeal_classifiedPoint`), so
  `zeroLocus I = closure S` (`PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure`).
  `left_classifiedPoint` shows that `j.hom.left` sends `S` onto `rationalPointImage H Γ`.
  `j.hom.left` is a homeomorphism (`Scheme.Hom.homeomorph`), so it maps `closure S` onto the
  closure of that image.

## Provenance

The statement is `RationalPointClosureSubgroupStatement`
(`Absolute.RationalPointClosureStatement`, by Worker 1394). Its literature source is Milne
2017, Lemma 1.40, Theorem 1.45 and Proposition 1.26(b). All helper declarations in this
module are internal proof infrastructure. The only external code is the copied Mathlib lemma named above.
