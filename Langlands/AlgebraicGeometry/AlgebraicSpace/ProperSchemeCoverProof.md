# Proper finitely presented scheme covers of proper algebraic spaces

Authors: Worker 78 (the weak Chow cover, modules under `ProperSchemeCover/`) and
Worker 182 (the finite-presentation refinement, modules `ProperCoverFP*`).

`properSchemeCover` proves `ProperSchemeCoverStatement`
(`ProperSchemeCoverStatement.lean`). Let `S` be an affine scheme and `X` an
algebraic space over `S`. Assume that `X` is quasi-separated, that it has an étale
surjective atlas whose structure morphism is locally of finite presentation and
quasi-compact, and that its structural morphism is proper. Then there are a scheme
`U` over `S` and a surjective morphism `a : h_U → X` such that `U → S` is proper and
locally of finite presentation.

## Source

The Stacks Project, *Cohomology of Algebraic Spaces*, Section 69.18, Lemma 69.18.1
(Tag 089I), a weak Chow lemma for separated algebraic spaces of finite type over an
affine scheme. The registered source is `stacks-proper-scheme-covers-2026-11-11`. The
finite-presentation refinement over a non-Noetherian affine base follows the route in
the task context: Noetherian approximation of the base, the cover over the Noetherian
model, then base change to `S`. Stacks Lemma 76.41.1 (Tag 089L) reduces to the
Noetherian case in a similar way. `ChowCoverStatement.md` and
`ProperCoverFPReduction.md` give the exact provenance of each half.

## Implemented proof

The proof is the application of two results.

- `properSchemeCover_of_chowCover` (`ProperCoverFPReduction`) proves
  `ProperSchemeCover.ChowCoverStatement.{u} → ProperSchemeCoverStatement.{u}`.
  It takes a Noetherian model `X₀` over `Spec R` of `X` (`ProperCoverFPApprox`)
  and applies the Chow cover to `X₀`. It then pulls the cover back to `S` and
  proves that `U → S` is proper. Separatedness comes from
  `isSeparated_hom_of_relative`. Universal closedness comes from the composite
  `U → X → S` (`ProperCoverFPComposite`).
- `ProperSchemeCover.chowCover` proves `ProperSchemeCover.ChowCoverStatement.{u}`.
  For an affine `S` and a separated space `X` over `S` with an atlas that is
  locally of finite presentation and quasi-compact, it gives a surjective
  `a : h_U → X` represented by proper morphisms, with `U → S` locally of finite
  type and quasi-compact.

## Scope

The theorem keeps every quantifier of the statement: the universe `u`, every affine
scheme `S` and every algebraic space `X` over `S` with the three hypotheses of the
statement. The quasi-separatedness hypothesis is not used, because properness of the
structural morphism already gives separatedness. The proof does not use
`SpaceLimitPropertyDescentStatement`. It adds no representability, Noetherian or
cover-existence hypothesis. The statement module is imported unchanged.
