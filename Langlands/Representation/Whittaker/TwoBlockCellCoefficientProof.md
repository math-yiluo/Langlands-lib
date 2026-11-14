# Proof of the pure-tensor scalar coefficient formula

The proof chooses the actual smooth cell section with rectangular restriction
`Ψ(x) (v₁⊗v₂)`, and an ambient Whittaker functional that extends the scalar cell
integral. Their coefficient belongs by construction to that functional's
coefficient image and hence to the intrinsic Whittaker set.

Leading-block translation keeps the chosen vector in the cell submodule, so
the extended functional on the translated vector equals its ordinary scalar
Jacquet integral. The translated restriction has the positive half modulus,
the original-order Levi action at `diag(I_A,g)`, and `Ψ(g⁻¹x)`. The block tensor
acts factorwise on the pure tensor. Linearity of the tensor functional gives
`ℓ₁(v₁) ℓ₂(π₂(g)v₂)` times the two scalar factors. The conjugate Jacquet kernel
is `ψ(-x_(B,1))`; commutative ring normalization and extraction of a constant
from the integral finish the calculation.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.Representation.Whittaker.TwoBlockCellCoefficientProof` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
