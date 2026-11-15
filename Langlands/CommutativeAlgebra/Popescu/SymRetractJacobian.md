# The Jacobian matrix of the new relations

This module works in the algebra `C = SymAlg I F = R[x, y]/J`. `SymAlg` is a `def`, with
`CommRing` and `R`-algebra instances transferred from the quotient. `qC` is the quotient map,
and `uC` is the image of `u`. The module proves that the Jacobian matrix of the relations `H_k`
(module `SymRetractData`) has a right inverse up to the scalar `u⁵` over `C`. All declarations
are in namespace `SymRetract`.

## Matrices over `C`

- `EC`: the image of `E`.
- `DC`: the image of the Jacobian matrix `(∂f_k/∂x_i)`.
- `PC`: the image of `P`.
- `ZC`: the image of `Z̃`.
- `YC`: the `x`-derivatives `∂𝒢_k/∂x_i`.

## Identities in `C`

- `qC_F`, `qC_Gk`: the `f_k` and the `𝒢_k` vanish in `C`.
- `EC_eq`: `E = D P`.
- `EC_mul_DC`: `E D = u D`. This is `Et_mul_D_sub`, since `ιx(I) ⊆ J`.
- `EC_sq`: `E² = u E`.
- `ZC_mul_DC`: `Z̃ D = E Ỹ`. Apply `∂/∂x_i` to the identity `E 𝒢 = Z̃ f` (`Et_Gk`) and use
  that `𝒢` and `f` vanish in `C`.

## The Jacobian matrix of the `H_k`

Modulo `J`, differentiating `H_k` gives the following.

- `qC_pderiv_x_Hk`: the `x`-columns are `u³ D + u² Ỹ − E Z̃ D`.
- `qC_pderiv_y_Hk`: the `y`-columns are `u² (u·1 − E)`. Here `∂𝒢_k/∂y_j = u δ_kj − E_kj`, and
  the `y`-derivatives of the other summands are multiples of the `f`'s.

`JC` is the full `m × (n + m)` Jacobian matrix over `C`. `ΨC` is the `(n + m) × m` matrix with
`x`-rows `u P` and `y`-rows `u²·1 − Ỹ P`.

`JC_mul_ΨC` states `JC · ΨC = u⁵ • 1`. The sum over the `n + m` columns splits into the `x`-part
and the `y`-part (`Fin.sum_univ_add`). With `E Z̃ D = E E Ỹ = u E Ỹ`, the product becomes
`(u³ D + u² Ỹ − u E Ỹ)(u P) + u² (u − E)(u² − Ỹ P)`. Since `D P = E`, this is
`u⁴E + u³ỸP − u²EỸP + u⁵ − u⁴E − u³ỸP + u²EỸP = u⁵`. The final step is checked by `module`.

## Status

The module imports `SymRetractData` and uses only the standard axioms.
