# Multiplication by any Hecke character on the stable automorphic operator core

Author: Worker 5136.

This internal module restricts multiplication by `χ ∘ det` to the Library's
stable automorphic operator core `automorphicOperatorCore F n`, for an arbitrary
Hecke character `χ`. The core consists of the finite-smooth functions all of
whose images under the operator algebra are automorphic forms. Write `M_χ` for
`FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ` (module
`Langlands.Automorphic.HeckeTwist.SmoothMultiplier`).

- `mem_automorphicOperatorCore_heckeDeterminantMultiplier`: `M_χ` maps the core
  into itself. For an operator `a`, `a (M_χ f) = M_χ (a' f)` with `a'` the
  conjugated operator (`operatorAction_heckeDeterminantMultiplier`, module
  `OperatorConjugation`). The function `a' f` is an automorphic form because `f`
  is in the core, and `M_χ` preserves automorphic forms
  (`mem_automorphic_heckeDeterminantMultiplier`, module `AutomorphicMultiplier`).
- A private lemma shows that the image of the core under `M_χ` is exactly the
  core. Surjectivity uses `M_{χ⁻¹}` and the Library's `determinantMul_inv_apply`.
- `StableAutomorphicFunctions.heckeDeterminantMultiplier n χ` is the resulting
  continuous linear automorphism of `StableAutomorphicFunctions F n`.
- `operatorAction_heckeDeterminantMultiplier`,
  `finiteAction_heckeDeterminantMultiplier`,
  `compactAction_heckeDeterminantMultiplier`: an operator `a` acts on `M_χ f` as
  `M_χ` applied to the conjugated operator acting on `f`. A finite translation
  by `d` or a compact translation by `k` picks up the scalar `χ(det d)` or
  `χ(det k)`.
- `envelopingAction_heckeDeterminantMultiplier`:
  `D(a) (M_χ f) = M_χ (D(heckeEnvelopingShift n χ a) f)`.
- `inclusion_heckeDeterminantMultiplier`, `evaluate_heckeDeterminantMultiplier`,
  `evaluate_heckeDeterminantMultiplier_symm`: compatibility with the inclusion
  into automorphic forms, and pointwise multiplication by `χ(det g)` and
  `χ(det g)⁻¹`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.StableAutomorphicDeterminantMultiplier` with the
finite-order hypothesis removed. The enveloping-algebra lemma is shifted by
`heckeEnvelopingShift n χ`. No correspondence with a particular passage of the
literature is claimed.
