# The identity-coset stalk of Renard's induction sheaf

This internal helper module proves the fibre sentence of Renard III.3.2, printed
p.85 / PDF p.91: "la représentation de `H` dans la fibre du faisceau `F_τ`
au-dessus du point `o = H1_G` de `H\G` est isomorphe à `(τ, E)`". The source calls
this clear and gives no proof. The argument here is internal. Source: David
Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF p.91 was
read for this module.

All declarations have the prefix `Langlands.Sheaf.Renard.HomogeneousOriginStalk`.
`G : Type` is a topological group, `H` is a subgroup, and the base is the
published `LeftQuotient H` with `HomogeneousSections.homogeneousAction`
(`g₀ • Hg = H(g g₀⁻¹)`). The identity coset is `origin H = quotientMap H 1`.

## Evaluation at the identity

Let `σ : Representation ℂ H V` be a complex representation.

- `evalOne H σ : CompactFunctions H σ →ₗ[ℂ] V` sends `f` to `f(1)`, that is,
  `eval H σ f.val 1`.
- `evalOne_compactInduced`: `evalOne (compactInduced H σ h f) = σ h (evalOne f)`
  for `h ∈ H`. This is `f(1·h) = f(h·1) = σ(h) f(1)` by the published
  `eval_covariant`.
- `evalOne_compactInducedMap`: `evalOne` commutes with `compactInducedMap H T`,
  by `rfl`.
- `evalOne_surjective` assumes `hG : IsLocallyProfinite G` and smooth `σ`. Every
  `v` equals `f(1)` for the published `compactLocalSection H σ hσ 1 v univ`. That
  construction needs `NonarchimedeanGroup G`, which is built locally from the
  published van Dantzig theorem
  `Langlands.Topology.LocallyProfiniteProof.vanDantzig`, the same way as in
  `SectionActions.hasStableNeighbourhoods_of_locallyProfinite`. It also needs a
  locally compact space, which is `hG.locallyCompactSpace`.
- `eval_action` assumes `[LocallyCompactSpace G]`, closed `H` and
  `hXq : IsLocallyProfinite (LeftQuotient H)`. The characteristic test of a
  compact open `K` acts on the published test module
  `CompactInductionTestModule.moduleObject` by `f ↦ (g ↦ 1_K(Hg) · f(g))`, by
  `rfl`.
- `evalOne_eq_zero_iff`: `f(1) = 0` if and only if some compact open `K ∋ origin H`
  satisfies `χ_K · f = 0`. Forward: the projected support of `f` is closed
  (`isClosed_quotientSupport`). It misses the origin because, by
  `quotientMap_mem_quotientSupport_iff_of_covariant`, `Hg` lies in it exactly
  when `f(g) ≠ 0`. A compact open `K` inside its complement then kills `f`
  pointwise. Backward: evaluate `χ_K · f` at `1`, where `1_K(H1) = 1`.

## The germ at the identity coset and the unit

Fix `hG : IsLocallyProfinite G` and `hH : IsClosed H`. Every use of local
compactness is `hG.locallyCompactSpace`, exactly as in `InductionSheaf`. For
`A : Langlands.SmoothRep.{0, 0, 0} ℂ H`:

- `inducedAction hG H hH A` is the published
  `CompactInductionTestModule.compatibleObject H hH A.representation`.
  `InductionSheaf.functor` reconstructs its sheaf.
- `germOne hG H hH A` is `ProjectorActionStalks.originalGerm` at `origin H`, viewed
  on `CompactFunctions H A.representation` and landing in the ordinary stalk of
  `((InductionSheaf.functor hG H hH).obj A).obj.obj`. Linearity for the original
  complex scalars follows from the published
  `CompactInductionTestModule.canonicalScalar_eq`.
- `germOne_surjective` is `ProjectorActionStalks.originalGerm_surjective`.
- `ker_evalOne`: the kernels of `evalOne` and `germOne` are equal. Both are
  described by the same compact-open test condition, through
  `evalOne_eq_zero_iff` and `ProjectorActionStalks.originalGerm_eq_zero_iff`.
- `unitLinearEquiv hG H hH A : A ≃ₗ[ℂ] stalk` composes three maps: the inverse of
  Mathlib's first isomorphism theorem for `evalOne`
  (`LinearMap.quotKerEquivOfSurjective`), `Submodule.quotEquivOfEq` for the equal
  kernels, and the first isomorphism theorem for `germOne`.
  `unitLinearEquiv_evalOne` states `f(1) ↦ germOne f`.
- `unitLinearEquiv_intertwining`: the map sends `A.representation h v` to the
  stalk action of `h` applied to its image. That stalk action is the
  representation of `(pointRestriction H hG hH).obj ((InductionSheaf.functor hG
  H hH).obj A)`, i.e. the published fixed-stalk transport. Write `v = f(1)`.
  Then `σ(h) f(1)` is the identity value of the right translate of `f` by `h`, and
  `ProjectorActionStalks.stalkPull_originalGerm` moves the translate to stalk
  transport. The action on `inducedAction` is literally `compactInduced`.
- `unitEquiv` packages this as a `Representation.Equiv` with
  `Representation.Equiv.mk`.
- `unitLinearEquiv_naturality`: for `u : A ⟶ B` in `SmoothRep`, the map commutes
  with `u` and with the image of `u` under induction followed by point
  restriction. Write `v = f(1)`. Then `u(f(1))` is the identity value of
  `compactInducedMap H (SmoothRep.hom u) f`, and
  `ProjectorActionStalks.stalkMap_originalGerm` applies to the published
  `CompactInductionTestModule.compatibleMap`.
- `unitIso hG H hH : 𝟭 (SmoothRep ℂ H) ≅ InductionSheaf.functor hG H hH ⋙
  pointRestriction H hG hH` is `NatIso.ofComponents` of
  `Langlands.SmoothRep.mkIso (unitEquiv hG H hH A)`.

No countability hypothesis on `G` is used. The module edits no Library file.
