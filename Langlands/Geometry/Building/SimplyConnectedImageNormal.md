# Transport and normality of `G(k)^♮`

For a group scheme `G` over a field `k`, with an inclusion `d : D → G` of its derived subgroup
and a simply connected cover `π : C → D`, `simplyConnectedImage d π` (module `KPZeroSubgroups`)
is the image of `C(k) → G(k)`. This is `G(k)^♮` of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Definition 2.6.20 (printed p. 104, PDF p. 135). This module proves that the
subgroup is functorial for isomorphisms (with the induced isomorphism
`simplyConnectedImageEquiv`), does not depend on the chosen cover, and is normal.
It is a helper for the published `IwahoriWeylExactSequenceStatement`, whose quotient
`G(F)/G(F)^0` needs normality of `G(F)^0 = G(F)^♮ · Z(F)^0`. It does not prove that target.

## Statements

- `GroupScheme.comp_iso_mem_derivedSubgroup`: an isomorphism `e : G ≅ G'` carries points of
  `derivedSubgroup G` to points of `derivedSubgroup G'`.
- `GroupScheme.IsDerivedSubgroup.comp_iso`: if `d : D → G` is an inclusion of the derived
  subgroup, then so is `d ≫ e.hom : D → G'`.
- `GroupScheme.IsSimplyConnectedDerivedCover.exists_comp_eq_comp_iso`: for simply connected
  covers `π : C → D` of `d : D → G` and `π' : C' → D'` of `d' : D' → G'`, and an isomorphism
  `e : G ≅ G'`, there is a homomorphism `a : C → C'` with `a ≫ π' ≫ d' = π ≫ d ≫ e.hom`.
- `Building.map_simplyConnectedImage_le`: the image of `G(k)^♮` under `e` lies in `G'(k)^♮`.
  This is the case of isomorphisms of KP Fact 2.6.21, which states it for every morphism
  `G → H`. The general morphism case is not proved here.
- `Building.map_simplyConnectedImage_eq`: the image of `G(k)^♮` under `e` is exactly
  `G'(k)^♮`.
- `Building.simplyConnectedImageEquiv h h' e : simplyConnectedImage d π ≃* simplyConnectedImage d' π'`
  (definition): the group isomorphism `G(k)^♮ ≃* G'(k)^♮` obtained by restricting the
  isomorphism `G(k) ≃* G'(k)` induced by `e`. The simp lemma
  `coe_simplyConnectedImageEquiv_apply` states that it sends `x` to `e(x)` in `G'(k)`.
- `Building.simplyConnectedImage_eq`: two inclusions of the derived subgroup of the same `G`,
  each with a simply connected cover, give the same subgroup `G(k)^♮`.
- `Building.simplyConnectedImage_normal`: `G(k)^♮` is a normal subgroup of `G(k)`.
- For the data of KP Definition 2.6.23 in `KPZeroSubgroups`:
  `UnramifiedZeroDatum.simplyConnectedImage_eq` and `ZeroSubgroupDatum.simplyConnectedImage_eq`
  state that `H(K)^♮` and `G(F)^♮` do not depend on the datum (for `ZeroSubgroupDatum`, also
  not on its torus `S` and Levi subgroup `Z`). The instances
  `UnramifiedZeroDatum.simplyConnectedImage_normal` and
  `ZeroSubgroupDatum.simplyConnectedImage_normal` give normality.

## Proof

*Derived subgroups.* `derivedSubgroup G` consists of the points lying in every closed
subgroup that contains all commutators. For a point `x` of `derivedSubgroup G` and such a
subgroup `i : H → G'`, the composite `i ≫ e.inv : H → G` is again a closed immersion (an
isomorphism followed by a closed immersion). Its range contains all commutators, since
`e.hom` preserves multiplication and inverses. So `x` factors through `i ≫ e.inv`, and
`x ≫ e.hom` factors through `i`. For `IsDerivedSubgroup.comp_iso`, `d ≫ e.hom` is a closed
immersion. Its range is `derivedSubgroup G'`: one inclusion follows from the first lemma for
`e`, the other from the first lemma for `e.symm`.

*Lifting covers.* Both `d ≫ e.hom` and `d'` represent `derivedSubgroup G'`, so
`isoOfIsRepresentedBy` gives `ψ : D ≅ D'` with `ψ.hom ≫ d' = d ≫ e.hom`. The composite
`π' ≫ ψ.inv : C' → D` is a central isogeny (`IsCentralIsogeny.comp_iso`), and `C'` is
semisimple, being simply connected. The universal property of `π`
(`IsSimplyConnectedCover.universal`) gives `a : C → C'` with `a ≫ π' ≫ ψ.inv = π`. Then
`a ≫ π' ≫ d' = a ≫ π' ≫ ψ.inv ≫ ψ.hom ≫ d' = π ≫ d ≫ e.hom`.

*Transport, independence and normality.* For `c ∈ C(k)`, the point `a(c) ∈ C'(k)` maps to
`e(π(d(c)))` by the factorization above. This proves `map_simplyConnectedImage_le`. Applying it to `e.symm` gives the reverse
inclusion `G'(k)^♮ ⊆ e(G(k)^♮)`, since `e(e⁻¹(g)) = g`; this is
`map_simplyConnectedImage_eq`. The definition `simplyConnectedImageEquiv` composes Mathlib's
`MulEquiv.subgroupMap` for the point isomorphism `isoPointsEquiv e` with
`MulEquiv.subgroupCongr` along that equality. For two
covers of the same `G`, applying it to `Iso.refl G` in both directions gives
`simplyConnectedImage_eq`. For normality, apply it to the inner automorphism
`G.innerIso g` with the same cover on both sides. By `comp_innerIso_hom` and
`constantPoint_self`, that automorphism acts on `G(k)` as `x ↦ g x g⁻¹`, so `G(k)^♮` is stable
under conjugation. The datum-level results are these lemmas applied to the stored
`isSimplyConnectedDerivedCover` fields.

## Relation to the literature

KP proves Fact 2.6.21 by lifting a morphism `G → H` to `G_sc → H_sc`. Our proof is that
argument for isomorphisms. KP uses normality of `G(k)^♮` in the proof of Lemma 2.6.24 (PDF
p. 136), which deduces normality of `G(k)^0`. Independence of the cover is implicit in KP's
notation `G_sc`. The Lean statement makes it explicit, because `simplyConnectedImage` takes
the cover as an argument.
