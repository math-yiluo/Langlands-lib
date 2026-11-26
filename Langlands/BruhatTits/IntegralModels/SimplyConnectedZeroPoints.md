# `G(K)^1 = G(K)^0 = G(K)` for a simply connected group

This module proves `G(k)^1 = G(k)` for semisimple groups and
`G(K)^0 = G(K)` for simply connected groups over the maximal unramified
extension `K`. In Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (KP),
Notation 2.6.15 and Lemma 2.6.16(4) describe `G(k)^1`. Definition 2.6.23(1)
defines the quasi-split zero subgroup using `G(k)^♮`, the image of the simply
connected derived cover on rational points from Definition 2.6.20. KP §4.1.28
uses these equalities for Axiom 4.1.20(4). The proofs below derive them from
the definitions and the cited Library results.

## Results over a field `k`

- `rationalCharacters_subsingleton_of_isSemisimple`: a semisimple group `G` has
  only the trivial rational character. The Library result `semisimplePerfect`
  says that the derived subgroup functor of a semisimple group is all of `G`.
  So the identity `𝟙 G` is a derived subgroup (`IsDerivedSubgroup (𝟙 G)`).
  The Library result `IsDerivedSubgroup.characterRestrict_eq_zero` says that
  every rational character restricts to zero on a derived subgroup. Restriction
  along the identity is the character itself (`characterRestrict_id`), so any
  two characters are both zero.
- `characterValuationKernel_eq_top_of_isSemisimple`: for every valuation `v` on
  `k`, the common kernel `characterValuationKernel v G` of the valuations
  `v ∘ χ` (`χ` a rational character) is all of `G(k)` when `G` is semisimple.
  The only character is `0`, which takes the value `1` at every point. This is
  `G(k)^1 = G(k)` for semisimple `G`. KP Notation 2.6.15 defines `G(k)^1` as the
  kernel of `ω_G`, and KP Lemma 2.6.16(4) (printed p. 103, PDF p. 134) describes
  it as this common kernel.
- `isIso_of_isClosedSubgroup_of_range_eq_top` (private): a closed subgroup
  `p : P → G` whose subgroup functor of points is all of `G` is an isomorphism.
  Both `p` and `𝟙 G` represent the top subgroup functor. The Library comparison
  `IsRepresentedBy.isoOfIsRepresentedBy` then gives an isomorphism `P ≅ G`
  whose underlying morphism is `p`.
- `IsSimplyConnectedDerivedCover.isIso_comp_of_isSimplyConnected`: take a
  simply connected derived cover `π : C → D`, `d : D → G` (`d` a derived
  subgroup, `π` a simply connected central cover of `D`). If `G` is simply
  connected, then `π ≫ d : C → G` is an isomorphism. `G` is semisimple, so it
  is perfect (`semisimplePerfect`). Then the range of `d` is all of `G`, and `d`
  is an isomorphism by the previous lemma. Hence `π ≫ d` is a central isogeny
  (Library `IsCentralIsogeny.comp_iso`) from the semisimple group `C` to the
  simply connected group `G`. A central isogeny onto a simply connected group
  from a semisimple group is an isomorphism
  (`IsSimplyConnected.central_isogeny_isIso`).
- `simplyConnectedImage_eq_top_of_isSimplyConnected`: in the same situation the
  image `G(k)^♮` of `C(k) → G(k)` (KP Definition 2.6.20) is all of `G(k)`. A
  point `g` is the image of `(π ≫ d)⁻¹(g)`.

## Result over the maximal unramified extension

Let `F` be a non-archimedean local field and `K = UnramifiedClosure F`.

- `UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected`: let `E` be any
  datum computing `H(K)^0 = H(K)^♮ · T(K)^0` (KP Definition 2.6.23(1); the
  Library structure `UnramifiedZeroDatum`). If `H` is simply connected, then
  `E.zeroPoints` is all of `H(K)`. The subgroup `E.simplyConnectedImage` is
  already all of `H(K)` by the previous result. It is contained in
  `E.zeroPoints` (Library `simplyConnectedImage_le_zeroPoints`).

## Sources

- KP Notation 2.6.15 and Lemma 2.6.16(4) (printed pp. 102–103, PDF pp. 133–134):
  `G(k)^1` is the common kernel of the valuations of the rational characters.
- KP Definition 2.6.20 (printed p. 104, PDF p. 135): `G(k)^♮` is the image of
  `G_sc(k) → G(k)`.
- KP Definition 2.6.23(1) (printed p. 104, PDF p. 135): for quasi-split `G`,
  `G(k)^0 = G(k)^♮ · T(k)^0`.
- The facts that a semisimple group is perfect and that a central isogeny from
  a semisimple group onto a simply connected group is an isomorphism are the
  Library results named above.
