# Geometric inputs for central-torus exactness of fundamental groups

Author: Worker 149 (Task 6713). This is a helper module for the proof of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorusFundamentalExactnessStatement`
in `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof`. It proves the
geometric facts about maximal tori and simply connected covers that the lattice
argument of `Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusLattice` needs.

## Setting

Names are in `Langlands.GroupScheme.AlgebraicFundamentalGroup.CentralTorus`.
Throughout, `k` is a field in universe `u`, and over `Spec k` we have:

- a commutative group scheme `Z`, connected reductive group schemes `H` and `G`, and
  homomorphisms `i : Z.toGrp ⟶ H` and `p : H ⟶ G`;
- presentations `aZ : Choice k Z.toGrp`, `b : Choice k H` and `c : Choice k G`. Each
  is a maximal torus together with a simply connected cover of the derived
  subgroup, as in `Langlands.GroupScheme.AlgebraicFundamentalGroup`;
- torus homomorphisms `e : aZ.torus ⟶ b.torus` and `e' : b.torus ⟶ c.torus`.

Each result assumes only the hypotheses it lists. The ones used are:

- `hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`: `p` is flat,
  surjective and locally of finite presentation, and its kernel has exactly the
  points of the image of `i` on every test scheme;
- `hi : IsClosedSubgroup i` (closed immersion) and `hc : IsCentral i`;
- `hZ : IsIso aZ.inclusion`: the chosen maximal torus of `Z` is all of `Z`. In the
  application this follows from `IsTorus Z.toGrp` by `IsMaximalTorus.isIso_of_torus`;
- `he : aZ.inclusion ≫ i = groupHom e ≫ b.inclusion` and
  `he' : b.inclusion ≫ p = groupHom e' ≫ c.inclusion`: `e` and `e'` are the
  restrictions of `i` and `p` to the chosen maximal tori.

`E` is a field with `[Algebra k E]`, and `B` is base change along `algebraBaseMap k E`.
The lattice `X_*(T_E)` is `cocharacterLattice (B.obj T)`, and
`Choice.torusLatticeMap` is postcomposition `ν ↦ ν ≫ B.map e`.

## Statements

- `range_kernelι_eq_range hq hZ he he'`: the full kernel of `groupHom e'` and the image
  of `groupHom e` have the same points on every test scheme.
- `mono_torusMap hi hZ he`: `groupHom e` is a monomorphism (of the underlying objects
  over `Spec k`).
- `kernelIso hq hi hZ he he' : aZ.torus ≅ CommGroupScheme.kernel e'`, with
  `kernelIso_hom_comp`: composing it with the kernel inclusion gives `e`. So `T_Z` is
  the scheme-theoretic kernel of `T_H → T_G`.
- `torusLatticeMap_exact E hq hi hZ he he'`: the map
  `aZ.torusLatticeMap b E (B.map e) : X_*(T_Z,E) → X_*(T_H,E)` is injective, and its
  range is the kernel of `b.torusLatticeMap c E (B.map e') : X_*(T_H,E) → X_*(T_G,E)`.
- `torusLatticeMap_surjective E hH hG hZt hq hi hc he'`, for `[IsSepClosure k E]`,
  connected reductive `H` and `G`, and `hZt : IsTorus Z.toGrp`: the second map
  `b.torusLatticeMap c E (B.map e')` is surjective.
- `exists_coverIso hH hG hq hc`: there is an isomorphism `ψ : b.cover ≅ c.cover` with
  `ψ.hom ≫ c.covering = b.covering ≫ b.derivedMap c p`. Here `b.derivedMap c p` is the
  map of chosen derived subgroups induced by `p`.
- `exists_scTorusIso ψ hψ he'`: given such a `ψ`, there is an isomorphism
  `φ : b.scTorus ≅ c.scTorus` of the preimage tori with
  `φ.hom ≫ c.scToTorus = b.scToTorus ≫ e'`.

## Provenance

These are internal lemmas. They supply the geometric facts in the proof of
Kaletha–Prasad (2023), Lemma 11.5.1 (printed p. 430, PDF p. 461), for an arbitrary
central torus (see the statement's Markdown,
`Langlands/GroupScheme/AlgebraicFundamentalGroupCentralTorusStatement.md`):

- the preimage of a maximal torus of `G` is a maximal torus `T` of `H` containing `Z`,
  with `T/Z` maximal in `G`;
- `0 → X_*(Z) → X_*(T) → X_*(T/Z) → 0` is exact over a separable closure;
- `p` identifies the simply connected covers of the derived subgroups, so the coroot
  lattices correspond.

The Lean statements are formulated for the chosen maximal tori and their restrictions
`e` and `e'`. They do not use the description of `T` as a preimage.

## Proofs

- `range_kernelι_eq_range`. Pointwise, on every test scheme.
  - Let `x` be killed by `e'`. Then `x ≫ b.inclusion` is killed by `p`, by `he'`. By
    `hq.2.2.2` it is `y ≫ i` for some `y`, and `y ≫ inv aZ.inclusion` maps to `x`
    under `e`: cancel the monomorphism `b.inclusion` and use `he`.
  - Conversely, `(y ≫ e) ≫ b.inclusion = (y ≫ aZ.inclusion) ≫ i` is killed by `p`,
    by `hq.2.2.2`. So `y ≫ e` is killed by `e'`: cancel the monomorphism `c.inclusion`
    and use `he'`.
- `mono_torusMap`. By `he`, `groupHom e ≫ b.inclusion` equals the composite of the
  isomorphism `aZ.inclusion` and the monomorphism `i`, so `groupHom e` is a
  monomorphism.
- `kernelIso` is `KernelRepresentative.iso` (`Langlands.GroupScheme.KernelRepresentativeTransport`).
  It applies to the kernel of `groupHom e'` and its monomorphic representative
  `groupHom e`, using the previous two items. `CommGroupScheme.isoOfGroupIso` makes it
  an isomorphism of commutative group schemes. `kernelIso_hom_comp` is
  `KernelRepresentative.iso_hom_comp`.
- `torusLatticeMap_exact`. Compose `B.mapIso kernelIso` with
  `CommGroupScheme.kernelBaseChangeIso` (base change of the kernel is the kernel of the
  base change). Transport cocharacters along the result
  (`cocharacterLattice.congr`), then apply `cocharacterLattice.kernelEquiv`. This
  `kernelEquiv` (`Langlands.GroupScheme.Torus.KernelCocharacters`) identifies
  cocharacters of a kernel with cocharacters killed by the map. The composite
  equivalence sends `w` to `w ≫ B.map e`, by `kernelBaseChangeIso_hom_ι` and
  `kernelIso_hom_comp`. Injectivity and `ker = range` follow.
- `torusLatticeMap_surjective` applies
  `Geometry.Building.Kottwitz.cocharacter_surjective_of_central_torus_square`
  (`Langlands.Geometry.Building.Kottwitz.CentralSurjectionZeroSurjectivity`). Its
  inputs are:
  - surjectivity of `p` (`hq.2.1`);
  - centrality of `kernelι p`, from `hc` and `hq.2.2.2` via `isCentral_iff_range_le_center`;
  - `kernel p` is a torus: `hq.kernelIso` identifies it with `Z`;
  - maximality of `b.inclusion` and closedness of `c.inclusion`;
  - splitting of both tori over `E`, by `isSplitTorus_baseChange_of_isSepClosure`;
  - the square `he'`.
- `exists_coverIso`.
  - `b.derivedMap c p` is a central isogeny by `IsDerivedSubgroup.isCentralIsogeny_map`
    (`Langlands.GroupScheme.CentralSurjection.DerivedMap`), using surjectivity of `p`
    and centrality of its kernel.
  - The cover `b.cover` is semisimple, so it equals its derived subgroup
    (`semisimplePerfect`). Hence the composite `b.covering ≫ b.derivedMap c p` is a
    central isogeny (`IsCentralIsogeny.comp_of_derivedSubgroup_eq_top`).
  - Its source is simply connected and its target `c.derived` is semisimple. So
    `simplyConnectedCentralCoverUniversalProperty` gives the universal property, and the
    composite is an `IsSimplyConnectedCover`.
  - `ψ` is `IsSimplyConnectedCover.iso` between it and the chosen cover
    `c.covering`, and the identity is `iso_hom_comp`.
- `exists_scTorusIso`.
  - `c.scTorus` is the fibre product of `c.covering ≫ c.derivedInclusion` and
    `c.inclusion`.
  - `φ'` is `pullback.lift` of `b.scInclusion ≫ ψ.hom` and
    `groupHom b.scToTorus ≫ groupHom e'`. The cone condition follows from `hψ`,
    `derivedMap_comp`, `scInclusion_comp` and `he'`.
  - `b.scInclusion ≫ ψ.hom` is a maximal torus of `c.cover` (`scInclusion_isMaximalTorus`
    and `IsMaximalTorus.comp_iso`).
  - `φ' ≫ c.scInclusion` equals it, and `c.scInclusion` is a closed torus. So
    maximality makes `φ'` an isomorphism.
  - `φ` is `CommGroupScheme.isoOfGroupIso (asIso φ')`, and the compatibility is
    `pullback.lift_snd`.
