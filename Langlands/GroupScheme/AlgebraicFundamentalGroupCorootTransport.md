# Geometric conjugators preserve the coroot images of the derived covers

Author: Worker 149 (Task 6302). This is a helper module for the proof of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupComparisonStatement`
in `Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof`. It supplies the
coroot-preservation input `hB` of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice.comparison_of_conjugators`.

## Statements

- `Langlands.GroupScheme.IsSimplyConnectedDerivedCover.fieldBaseChange K h`: let `k` be a
  field and `K` a field extension of `k`. If `π : C ⟶ D` and `d : D ⟶ H` form a simply
  connected cover of the derived subgroup of `H` over `Spec k`
  (`IsSimplyConnectedDerivedCover d π`), then their base changes along
  `algebraBaseMap k K` again form one over `Spec K`.

In the remaining statements, `k` is a field, `E` a field extension of `k` (no separable
closure hypothesis), `G` a group scheme over `Spec k`, and `_E` denotes base change along
`algebraBaseMap k E`. Names are in `Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice`.

- `mem_corootImage_of_lift a x ν hx`: let `ν : a.lattice E` be a cocharacter of `(T_a)_E`
  and `x : (𝔾_m)_E ⟶ (C_a)_E` a homomorphism. Suppose
  `x ≫ (π_a ≫ d_a)_E = ν ≫ (i_a)_E` as homomorphisms `(𝔾_m)_E ⟶ G_E`. Then
  `ν ∈ a.corootImage E`. In words, a cocharacter of the maximal torus lies in the coroot
  image as soon as its image in `G` lifts to the simply connected cover.
- `IsConjugationComparison.corootImage_le h`: if `(g, e)` is a conjugator from `a` to `b`
  (`a.IsConjugationComparison E b g e`), then
  `a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom)`. So `ν ↦ ν ≫ e.hom`
  carries the coroot image of `a` into that of `b`.

## Provenance

These are internal lemmas. They formalize the step of Kaletha–Prasad (2023),
Construction 11.3.1 (printed p. 427, PDF p. 458) that conjugation of maximal tori
identifies the images of `X_*(T_sc)`, because conjugation lifts to the simply connected
cover. No literature statement is claimed for the Lean declarations.

## Proofs

- `IsSimplyConnectedDerivedCover.fieldBaseChange`: the three components are
  - connected reductivity of `H_K` (`connectedReductiveFieldExtensionStatement`,
    `Langlands.GroupScheme.Reductive.FieldExtensionProof`);
  - the derived subgroup property, transported with
    `IsDerivedSubgroup.baseChange_of_eq` and `derivedSubgroup_baseChange_eq_of_field`
    (`Langlands.GroupScheme.Derived.FieldBaseChangeAssembly`);
  - the simply connected cover property (`isSimplyConnectedCover_fieldExtension`,
    `Langlands.GroupScheme.SimplyConnected.FieldExtensionProof`).
- `mem_corootImage_of_lift`: `a.scTorus` is the fibre product of `π_a ≫ d_a` and `i_a`.
  The hypothesis `hx` gives a map `l = pullback.lift x ν hx` from `(𝔾_m)_E` into the
  fibre product of the base-changed maps. Composing with the inverse of
  `subgroupIntersectionBaseChangeIso` (`Langlands.GroupScheme.SubgroupIntersection`) gives a
  cocharacter of `(a.scTorus)_E`. Its image under `a.corootMap E` is `ν`, by
  `PreservesPullback.iso_inv_snd` and `pullback.lift_snd`.
- `IsConjugationComparison.corootImage_le`: base change both covers to `E` with
  `fieldBaseChange`. Apply `exists_comp_eq_comp_iso`
  (`Langlands.Geometry.Building.SimplyConnectedImageNormal`) to the inner automorphism
  `int(g)` of `G_E`. It gives `ψ : (C_a)_E ⟶ (C_b)_E` with
  `ψ ≫ (π_b)_E ≫ (d_b)_E = (π_a)_E ≫ (d_a)_E ≫ int(g)`. For a coroot-image element
  `ν ≫ scToTorus` with `ν` a cocharacter of `(a.scTorus)_E`, the lift
  `ν ≫ (scInclusion_a)_E ≫ ψ` satisfies the hypothesis of `mem_corootImage_of_lift` for `b`
  and `ν ≫ scToTorus ≫ e.hom`. The verification uses the defining square of the fibre
  product (`subgroupIntersection_condition`), the conjugator equation and the equation
  for `ψ`.
