# The Schrödinger model as an induced model

**GKT §1.2.2** (the Schrödinger model as the induced model of a Lagrangian; the restriction map
(1.5) and **Theorem 1.13**, p. 25), with Definition 1.6 (p. 20) and Proposition 1.12 (p. 23).

The module `Langlands.Theta.Heisenberg.SchrodingerInduced` identifies the induced model of the
Lagrangian `0 × Y` (with the trivial extension of `ψ`) with the Schrödinger model `schrodingerSB`.

## Content

For a pairing `β : X →ₗ[F] Y →ₗ[F] F`, the space `X × Y` with `polarizedForm β` has the Lagrangians
`X × 0` and `0 × Y`; the Schrödinger model lives on functions on `X`. In the book's notation
`W = X_B ⊕ Y_B` with `X_B = 0 × Y` (the Lagrangian of the induced model) and `Y_B = X × 0`, and
`⟨y_B, x_B⟩ = β(y_B, x_B)`; the operators (1.6) are those of `schrodingerFun`.

- `lagrangianRight X Y`: the subgroup `0 × Y`.
- `inducedFunction β ψ φ (x, y) = ψ(½ β(x, y)) φ(x)`, the book's `f_φ` (proof of Theorem 1.13:
  `f_φ(x + y, t) = ψ(t − ½⟨x, y⟩) φ(y)`); it restricts to `φ` on `X × 0`
  (`inducedFunction_apply_zero`), and the regular representation acts on it as the Schrödinger
  representation acts on `φ` (`regular_inducedFunction`, a computation with the cocycle).

Over a nonarchimedean local field with `X`, `Y` finite-dimensional with their module topologies:

- `continuous_pairing`, `continuous_polarizedForm_left`: continuity of `β` and of the form.
- `schrodingerDatum β hψ1 hβl`: the `InducingDatum` of `0 × Y` with `ψ_X(a) = 1`, for `ψ ≠ 1` and
  `β` non-degenerate on the left (self-duality by `mem_charOrthogonal_submodule`);
  `schrodingerInducedSpace`, its induced model.
- `inducedFunction_mem`, `restriction_mem`, `inducedFunction_restriction`: `φ ↦ f_φ` and
  `f ↦ f|_{X × 0}` are inverse to each other between `S(X)` and the induced space (a function of
  the induced space is determined by its values on `X × 0` through the equivariance under `0 × Y`).
- `restrictionEquiv`: **Theorem 1.13**, the restriction `R_{X,Y}` is an isomorphism of
  representations from the induced model of `0 × Y` to `schrodingerSB`.
- `isSmooth_schrodingerInducedSpace`, `isIrreducible_schrodingerInducedSpace` (for a perfect
  pairing): the induced model of `0 × Y` is smooth and irreducible, from the Schrödinger model
  (`isSmooth_schrodingerSB`, `isIrreducible_schrodingerSB`) through `isSmooth_of_equiv`,
  `isIrreducible_of_equiv`.

## Declarations

- `lagrangianRight`, `mem_lagrangianRight`, `inducedFunction`, `inducedFunction_apply`,
  `inducedFunction_apply_zero`, `regular_inducedFunction`.
- `continuous_pairing`, `continuous_polarizedForm_left`, `schrodingerDatum`,
  `isLocallyConstant_addChar`, `schrodingerInducedSpace`, `inducedFunction_mem`, `restriction_mem`,
  `inducedFunction_restriction`, `restrictionEquiv`, `restrictionEquiv_apply`,
  `restrictionEquiv_symm_apply`.
- `isSmooth_of_equiv`, `isIrreducible_of_equiv`, `isSmooth_schrodingerInducedSpace`,
  `isIrreducible_schrodingerInducedSpace`.

All in the name space `Langlands.HeisenbergGroup`.

## Dependencies

`Langlands.Theta.Heisenberg.InducedModel` (`InducingDatum`, `inducedSpace`),
`Langlands.Theta.Heisenberg.SchrodingerIrreducible` (smoothness and irreducibility of the
Schrödinger model).
