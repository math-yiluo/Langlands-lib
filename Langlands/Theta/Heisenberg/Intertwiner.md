# Intertwiners between the induced models of two Lagrangians

**GKT §1.2.4** (Lemma 1.20, **Proposition 1.21** and (1.9), Remark 1.22, pp. 30–32) and **§1.2.5**
((1.10) and **Proposition 1.24**, pp. 32–33), for two Lagrangian subspaces of a symplectic space with
the trivial extensions of `ψ`, in the realization of the induced models on functions on `W` (p. 29).

The module `Langlands.Theta.Heisenberg.Intertwiner` defines the integral `I_{A,A'}` from the
`A`-equivariant to the `A'`-equivariant functions, proves that it is well defined, lands in the
`A'`-equivariant functions and intertwines the regular representations, and identifies it with the
Fourier transform for transverse Lagrangians.

## Content

Let `B` be an alternating form on `W`, `A`, `A'` subspaces with `A'` isotropic. With the trivial
extensions `ψ_A(a, t) = ψ_{A'}(a, t) = ψ(t)`, `ψ_A⁻¹ ψ_{A'}` is trivial on `A ∩ A'`, so the element
`w` of Lemma 1.20 is `0` (Remark 1.22).

- `IsLagrangianEquivariant B ψ A f`: `f(a + w) = ψ(½ B(w, a)) f(w)` for `a ∈ A` (the equivariance of
  `Ind_{H(A)}^{H(W)} ψ_A` on functions on `W`, p. 29); `lagrangianEquivariantSubmodule`;
  `isLagrangianEquivariant_regular`: the regular representation preserves it.
- `lagrangianIntegrand B ψ A' f z b = ψ(½ B(b, z)) f(b + z)` on `A'`, the book's
  `f((b, 0)(z, 0))` (1.9); `lagrangianIntegrand_add`: **it is invariant under `A ∩ A'`** (the first
  step of the proof of Proposition 1.21); `lagrangianIntegrandQ`: the integrand on
  `A' / (A ∩ A')` (the book's `A ∩ A' \ A'`).
- `lagrangianIntertwiner hB hA' μ f`: **`I_{A,A'} f (z) = ∫_{A' / (A ∩ A')} ψ(½ B(b, z)) f(b + z)
  dμ(b)`** for a measure `μ` on the quotient.
- `lagrangianIntertwiner_regular`: **`I_{A,A'} (ρ_A(h) f) = ρ_{A'}(h) (I_{A,A'} f)`** (Proposition 1.21,
  "fourthly").
- `isLagrangianEquivariant_lagrangianIntertwiner`: for a Haar measure, **the image is
  `A'`-equivariant** (Proposition 1.21, "thirdly"; translation invariance of `μ`).

For the polarization `X × Y` of `polarizedForm β` (the book's `X = 0 × Y`, `Y = X × 0`):

- `transverseQuotientEquiv X Y`: `X ≃ (X × 0) / ((0 × Y) ∩ (X × 0))` (`X ∩ Y \ Y = Y`, p. 32);
  `isotropic_ker_snd`; `isLagrangianEquivariant_inducedFunction`.
- `lagrangianIntertwiner_inducedFunction`: **Proposition 1.24**, `I_{0×Y, X×0}(f_φ)` restricted to
  `0 × Y` is `F_{Y,X} φ = schrodingerFourier β hψ hψ1 μ φ`.

Not formalized: the induced models of arbitrary closed self-dual subgroups in the intertwiner, the
existence part of Lemma 1.20 (characters of `A ∩ A'` extended to `W`), the non-vanishing and the
unitary normalization of Proposition 1.21 for arbitrary Lagrangians, and Corollary 1.23. In the
case used by the standard Weil operator they are supplied in the Schrödinger realization
(`Langlands.Theta.Metaplectic.StandardOperator`, `Langlands.Theta.Metaplectic.InducedOperator`).

## Declarations

- `IsLagrangianEquivariant`, `lagrangianEquivariantSubmodule`, `lagrangianIntegrand`,
  `lagrangianIntegrand_add`, `isLagrangianEquivariant_regular`, `lagrangianIntegrandQ`,
  `lagrangianIntegrandQ_mk`, `lagrangianIntertwiner`, `lagrangianIntertwiner_regular`,
  `isLagrangianEquivariant_lagrangianIntertwiner`.
- `transverseQuotientEquiv`, `transverseQuotientEquiv_apply`, `isotropic_ker_snd`,
  `isLagrangianEquivariant_inducedFunction`, `lagrangianIntertwiner_inducedFunction`.

All in the name space `Langlands.HeisenbergGroup`.

## Dependencies

`Langlands.Theta.Heisenberg.SchrodingerFourier`, `Langlands.HarmonicAnalysis.FiniteDimensionalQuotient`.
