# Unit square-root tests for ring cell calculations

This internal derived module removes the three square-root hypotheses from
`RingRootCell.WeylData.relation_of_unit_squares`, for an affine ambient group.
Its provenance is elementary monic polynomial algebra, the affine
spectrum/global-sections correspondence, and the exact ring calculation in
`RankOneRingCalculus`. It makes no additional literature claim.

For a commutative ring `R` and a unit `a`, `UnitSquareExtension.polynomial` is
`X² - a`, `Ring a` adjoins a root, and `inclusion` is the coefficient map.
`inclusion_injective` uses monicity and positive degree when `R` is nontrivial;
the zero ring is handled by subsingleton injectivity. `root_sq` is the defining
polynomial equation. `rootUnit` packages the root as a unit because its square
is the image of `a`; `rootUnit_mul` is its exact square equation in the unit
group. Induction in `exists_squareRoots` adjoins square roots of any finite
family of units in one injective extension in the same universe.
Neither two nor a nilpotent element is inverted.

For an affine scheme `Z` over any scheme `S`, `exists_squareRoot_test` constructs
`j : W ⟶ Z` over `S` with injective pullback on global sections, and square roots
of the pulled-back finite family of units. Here `W` is the spectrum of the
extension of `Γ(Z, ⊤)`, and its map to `Z` is the spectrum map followed by
`Z.isoSpec.inv`. `appTop_specMap_isoSpec_inv` identifies its pullback with the
coefficient inclusion followed by the canonical global-sections isomorphism.
This proves the claimed injectivity, with no flatness or separability premise
needed for the argument.

`points_ext_of_injective_appTop` descends equality of morphisms into an affine
target along any map injective on global sections: equality after pullback
gives equality of the original maps on sections, and affine-target
extensionality gives equality of scheme morphisms. This retains nilpotents
and is not a test on field-valued points.

Now let `D : RingRootCell.WeylData k`, where `k` is any commutative ring, and
assume the total scheme of `D.G` is affine. Recall that `D` supplies the actual
normalizer, its torus-valued square, and the decomposition
`xp(1)n = xm(β) γ xp(δ)` with `β` and `δ` units over the base.
For any scheme test `Z`, section `X`, and units `w,u` with `u = 1 + Xw`,
`WeylData.relation_of_unit` proves

```text
xp(X) xm(β w) = xm(β u⁻¹ w) h(u) xp(u⁻¹ X).
```

In this formula `β` denotes its pullback to the test, `h` is the supplied
cocharacter, and `cellPt` is the actual product on the right. On affine tests,
`relation_of_unit_affine` adjoins square roots of the three units
`δ`, `w⁻¹`, and `u w⁻¹`. It applies `relation_of_unit_squares` there and descends
the exact equation using injective pullback and ambient affineness.
`comp_pb` records the compatibility of base sections with pullback. Finally,
`relation_of_unit` restricts to the affine open cover and uses naturality of
all three cell coordinates to conclude on every test.

The second coordinate `w` is still required to be a unit, as is `1 + Xw`.
This module does not construct the supplied Weyl data, normalize opposite
roots, or prove the host local Isomorphism Theorem. It imposes no field,
reducedness, characteristic, Henselian, or noetherian hypothesis.
