# Proof: Renard III.3.2, induction and original-stalk restriction are an equivalence

Worker 141 implemented this proof for Task 5598. The entry theorem is
`Langlands.Sheaf.Renard.HomogeneousEquivalence.homogeneousEquivalence : Statement`.
It proves the published statement `HomogeneousEquivalence.Statement` from
`Langlands/Sheaf/Renard/HomogeneousEquivalenceStatement.lean`, unchanged. For every
`G : Type` with a topological group structure and `SigmaCompactSpace G`, every
`hG : IsLocallyProfinite G` and every closed subgroup `H`, it gives an equivalence
`e : SmoothRep ℂ H ≌ SmoothActionSheaf G (LeftQuotient H)` with
`e.functor = InductionSheaf.functor hG H hH` and
`e.inverse = pointRestriction H hG hH`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, III.3.2, Theorem and its proof, printed pp.84-85 / PDF pp.90-91,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. These pages
were read. The source identifies the fibre of `F_τ` over `o = H1_G` with `(τ, E)`,
constructs the isomorphism `α : F_c(H\G) → ind_H^G(τ, E)`, `φ ↦ [g ↦ (γ_g · φ)(o)]`
with inverse `β`, and deduces the Theorem from the III.3.1 equivalence.

## Implemented proof

The theorem is `statement_of EquivariantModuleStatements.statements.2
HomogeneousCompactSectionProof.compactAlphaBeta`.

- `EquivariantModuleStatements.statements` is the published proof of Renard's
  III.3.1 equivalences (Task 5591). Its second component is
  `SmoothStatement`, used at universe `0`.
- `HomogeneousCompactSectionProof.compactAlphaBeta` is the published proof of
  `HomogeneousSectionStatements.CompactAlphaBetaStatement` (Task 5596).
- `HomogeneousEquivalence.statement_of`, in the helper module
  `Langlands/Sheaf/Renard/HomogeneousCounit.lean` submitted with this proof, turns
  these two results into the target. It applies `SmoothStatement` to
  `X = LeftQuotient H` and obtains `beta` with its two inverse laws from the
  second. It returns `CategoryTheory.Equivalence.mk (InductionSheaf.functor hG H hH)
  (pointRestriction H hG hH) unitIso counitIso`, so both functor equalities hold by
  `rfl`.
  - The unit `HomogeneousOriginStalk.unitIso` is the published natural
    isomorphism `InductionSheaf.functor ⋙ pointRestriction ≅ 𝟭` given by the
    germ at the identity coset (published with `originStalk`).
  - The counit `HomogeneousCounit.counitIso` makes the published `alphaCompact`
    an isomorphism of smooth compatible test actions, natural in the sheaf, from
    the compact-section functor to point restriction followed by compact
    induction. It whiskers the inverse with the published projector-sheaf
    functor and composes with the inverse of the III.3.1 unit.

Both functors are the published ones. No Library file is edited. The
`SigmaCompactSpace G` premise is only passed to `CompactAlphaBetaStatement`.
