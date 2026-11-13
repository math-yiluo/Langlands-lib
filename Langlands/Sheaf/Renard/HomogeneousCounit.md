# The counit of Renard's homogeneous equivalence

This internal helper module supports the final Theorem of Renard III.3.2, printed
p.85 / PDF p.91, using the countability setting of printed p.84 / PDF p.90. Source:
David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF p.91 was
read. There the source deduces the Theorem from the isomorphism
`α : F_c(H\G) → ind_H^G(τ, E)`, `φ ↦ [g ↦ (γ_g · φ)(o)]`, its inverse `β`, their
naturality, and the III.3.1 equivalence. This module carries out that deduction.
The two inputs it does not prove are taken as explicit hypotheses.

The declarations in `Langlands.Sheaf.Renard.HomogeneousCounit` work over
`G : Type`, `hG : IsLocallyProfinite G` and a closed subgroup `H`. The base is
`LeftQuotient H` with `HomogeneousSections.homogeneousAction`.

- `sectionAction hG H hH F` is the published compact-section compatible action
  `(CompactSectionActions.smoothFunctor hXq).obj F`, where
  `hXq = quotient_isLocallyProfinite H hG hH`. `inducedStalkAction hG H hH F` is
  the published `InductionSheaf.compatibleInduction` applied to the published
  point restriction of `F`.
- `smul_origin`: `g⁻¹ • origin H = quotientMap H g`.
- `alphaCompact_testSmul` shows that the published `alphaCompact H F` carries the
  test action on compact sections (`CompactSectionTestModule.testSmul`) to the
  multiplier on compact induction (`CompactInductionTestModule.multiplier`). At
  `g`, the germ at `origin H` of `γ_g(φ · s)` is moved to `g⁻¹ • origin H` by
  `CompactSectionActions.global_germ_transport`. There
  `CompactSectionTestModule.Γgerm_smul` extracts the scalar
  `φ(g⁻¹ • origin H) = φ(Hg)`, and the stalk transport is linear.
- `alphaHom` packages `alphaCompact` as a morphism of compatible test actions. Its
  test linearity is the previous lemma, and the group compatibility is the
  intertwining property of `alphaCompact`.

The rest of the namespace takes, as explicit arguments, maps
`beta F : compactInduced H (stalkRepresentation H F.obj) → compactRepresentation
F.obj` of representations that are two-sided inverses of `alphaCompact H F`
(hypothesis `hbeta`).

- `beta_testSmul`: such a `beta` is test linear, because `alphaCompact` is
  injective and test linear.
- `betaHom` and `alphaIso` give an isomorphism `sectionAction F ≅
  inducedStalkAction F` of smooth compatible test actions.
- `alphaIso_naturality` and `alphaNatIso` make it natural in `F`, by the published
  `alphaCompact_naturality`.
- `counitIso` additionally takes an equivalence
  `e : SmoothActionSheaf G (LeftQuotient H) ≌ SmoothCompatibleTestAction` with
  `e.functor = CompactSectionActions.smoothFunctor hXq` and
  `e.inverse = SmoothProjectorActionSheaf.smoothFunctor hXq hG`. It is the
  composite of the whiskered inverse of `alphaNatIso` with the inverse of
  `e.unitIso`, transported along these functor equalities by `eqToIso`. Its type
  is `pointRestriction H hG hH ⋙ InductionSheaf.functor hG H hH ≅ 𝟭`.

`Langlands.Sheaf.Renard.HomogeneousEquivalence.statement_of` assumes
`EquivariantModuleStatements.SmoothStatement.{0}` and
`HomogeneousSectionStatements.CompactAlphaBetaStatement` and proves
`HomogeneousEquivalence.Statement`. It applies the first assumption to
`X = LeftQuotient H` and the second to obtain `beta` (its two inverse laws are
used). It returns `CategoryTheory.Equivalence.mk (InductionSheaf.functor hG H hH)
(pointRestriction H hG hH) (HomogeneousOriginStalk.unitIso hG H hH) counitIso`.
Mathlib's `Equivalence.mk` keeps the given functors, so the functor equalities
hold by `rfl`. The `SigmaCompactSpace G` premise is only passed on to the second
assumption.

The two assumptions are published proof targets of sibling tasks (Task 5591 and
Task 5596). This module does not prove them; the entry module
`HomogeneousEquivalenceProof` supplies their published proofs. The module edits no
Library file.
