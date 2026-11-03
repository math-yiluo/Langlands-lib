# Injectivity of restriction to a split component

This module derives injectivity of `characterRestrict i` for a split
component `i : A ⟶ G` of a connected reductive group `G` over a field `k`. It
takes the published proposition
`Langlands.GroupScheme.CentralSplitTorusCharacterStatement` as an explicit
hypothesis. That proposition says that central split tori detect nonzero
rational characters. The module does not prove it. The universe `u` is
arbitrary. No perfectness, characteristic, splitness or local-field hypothesis
on `k` is used.

The argument is derived, not quoted. Renard (V.2.2) deduces injectivity from
the structure of reductive groups over a nonarchimedean local field. Here the
structure input is isolated in `CentralSplitTorusCharacterStatement`. The
remaining step is the factorization of central split tori through the split
component, proved below from Worker 1178's
`Langlands.GroupScheme.exists_largestCentralSplitTorus` in
`Langlands.GroupScheme.Rational.SplitComponentProof`.

## Factorization through a split component

`IsSplitComponent.exists_comp_eq` assumes that `G.X.left` is affine and that
the coordinate algebra `AffineCoordinates.algebra G` is of finite type over
`k`. Let `i : A ⟶ G` be a split component and `i' : A' ⟶ G` a central split
torus (`IsCentralSplitTorus i'`). The theorem gives `f : A' ⟶ A` with
`f ≫ i = i'`.

Proof. `exists_largestCentralSplitTorus` gives a central split torus
`j : B ⟶ G` through which every central split torus factors. The universal
property needs only the split-torus and centrality parts (`hi.1.1.1`, `hi.1.2`,
`hi'.1.1`, `hi'.2`). It gives `g : A ⟶ B` with `g ≫ j = i` and
`g' : A' ⟶ B` with `g' ≫ j = i'`. The maximality clause of
`IsSplitComponent i`, applied to `j` and `g`, makes `g` an isomorphism. Then
`f = g' ≫ inv g` satisfies `f ≫ i = g' ≫ inv g ≫ g ≫ j = g' ≫ j = i'`.

`IsSplitComponent.lift hfin hi hi' : A' ⟶ A` is a factorization chosen from
this existence statement (by `Classical.choose`), under the same hypotheses.
`IsSplitComponent.lift_comp` records `hi.lift hfin hi' ≫ i = i'`; it is tagged
`@[reassoc (attr := simp)]`. The module does not prove that the lift is
unique.

## Injectivity

`characterRestrict_injective_of_centralSplitTorusCharacter` takes
`hS : CentralSplitTorusCharacterStatement.{u}`, `hG : IsConnectedReductive G`
and a split component `i : A ⟶ G`. It concludes
`Function.Injective (characterRestrict i)`.

Proof. From `hG` the proof uses only that `G.X.hom` is affine and smooth.
Affineness of `G.X.hom` makes `G.X.left` affine, since the base `Spec k` is
affine. Smoothness gives local finite type, so `finiteType_coordinateAlgebra`
(from `SplitComponentProof`) shows that the coordinate algebra is of finite
type. The full connected-reductive hypothesis `hG` is passed unchanged to
`hS`.

Since `characterRestrict i` is additive, it suffices to show that its kernel
is zero. Suppose `characterRestrict i χ = 0` but `χ ≠ 0`. By `hS` there is a
central split torus `i' : A' ⟶ G` with `characterRestrict i' χ ≠ 0`. The
lift `f = hi.lift _ hi'` above satisfies `f ≫ i = i'`. By the published
`characterRestrict_comp`,
`characterRestrict i' χ = characterRestrict f (characterRestrict i χ)
= characterRestrict f 0 = 0`. This is a contradiction.
