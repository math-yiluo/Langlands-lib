# The operators `M_A(g)` on the induced model of a Lagrangian

**GKT §2.2.1** (the left-action map `J_{A,gA}` (2.5) and (2.6), the operator
`M_A(g) = I_{gA,A} ∘ J_{A,gA}` (2.7), (2.8), **Proposition 2.5**, pp. 50–52) and **§2.3.1** ((2.10),
(2.12), (2.15), (2.16), pp. 53–55).

The module `Langlands.Theta.Metaplectic.InducedOperator` defines the book's operator `M_A(g)` on
the induced model of a Lagrangian `A` (with the trivial extension of `ψ`, realized on functions on
`W`), proves that it intertwines `ρ_A(h)` with `ρ_A(g · h)`, and identifies it, for the
polarization `X × Y` and `A = 0 × Y`, with the standard Weil operator of
`Langlands.Theta.Metaplectic.StandardOperator`.

## Content

Let `B` be an alternating form on `W` and `g` an isometry of `B`.

- `leftActionMap g f = f ∘ g⁻¹`: the book's `J_{A,gA}` ((2.5)). It carries the `A`-equivariant
  functions to the `gA`-equivariant ones (`isLagrangianEquivariant_leftActionMap`, from
  `B(g⁻¹ w, v) = B(w, g v)`, `isometryGroup_inv_apply_left`) and satisfies **(2.6)**,
  `J ∘ ρ_A(h) = ρ_{gA}(g · h) ∘ J` (`leftActionMap_regular`).
- `inducedOperator hB hA g μ f = I_{gA,A}(J_{A,gA} f)`: **the operator `M_A(g)`** ((2.7), (2.8))
  for a measure `μ` on `A / (gA ∩ A)`, with `I_{gA,A}` the intertwiner of
  `Langlands.Theta.Heisenberg.Intertwiner`. Since both extensions of `ψ` are trivial, the element
  `w_g` of (2.8) is `0`.
- `inducedOperator_regular`: **Proposition 2.5**, `M_A(g) ∘ ρ_A(h) = ρ_A(g · h) ∘ M_A(g)`.

For the polarization `(X × Y, polarizedForm β)` (the book's `X = 0 × Y`):

- `isotropic_ker_fst`; `lagrangianRightEquiv X Y : Y ≃ 0 × Y`.
- `map_standardKernel`: **`ker c = gX ∩ X`** ((2.15)) as submodules of `0 × Y`;
  `standardQuotientEquiv g : Y ⧸ ker c ≃ X / (gX ∩ X)`, `standardQuotientEquiv_mk`.
- `inducedOperator_inducedFunction`: **(2.12) with (2.16)**: for `φ` on `X`, the restriction to
  `X × 0` of `M_X(g) f_φ` (`f_φ` the induced function of Theorem 1.13) is
  `standardOperatorFun ψ g μ φ`, for the measure `μ` on `Y ⧸ ker c` carried to `X / (gX ∩ X)`.
  So the standard Weil operator `r(g)` is the book's `R_{X,Y} ∘ M_X(g) ∘ R_{X,Y}⁻¹`, with the
  measure of `Langlands.Theta.Metaplectic.StandardOperator` that makes it unitary.

Not formalized: `M_A(g)` for a Lagrangian with a non-trivial extension of `ψ` (the element `w_g` of
(2.8)) and for the induced models of closed self-dual subgroups.

## Declarations

- `leftActionMap`, `leftActionMap_apply`, `isometryGroup_inv_apply_left`,
  `isLagrangianEquivariant_leftActionMap`, `leftActionMap_regular`, `inducedOperator`,
  `inducedOperator_regular`.
- `isotropic_ker_fst`, `lagrangianRightEquiv`, `map_standardKernel`, `standardQuotientEquiv`,
  `standardQuotientEquiv_mk`, `inducedOperator_inducedFunction`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.Metaplectic.StandardOperator`, `Langlands.Theta.Heisenberg.Intertwiner`.
