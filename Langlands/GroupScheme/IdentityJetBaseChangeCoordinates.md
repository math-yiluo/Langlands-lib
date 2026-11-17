# Actual base-changed identity jets in fixed affine coordinates

This internal construction compares the actual affine base-change coordinate
algebra with the tensor product of the fixed ambient coordinates. It uses
the actual affine base-change section theorem and the chosen affine
group-scheme coordinate isomorphism.

Let `G` be affine over `Spec R`, and let `b : S → Spec R` be arbitrary.
For each affine open `U` of `S`, `baseChangeCoordinateTensor` sends
`a ⊗ c` to the product of the actual base scalar function `a` and
the actual ambient coordinate function `c` on `G_S` above `U`.
`baseChangeCoordinateEquiv` proves that this is an algebra equivalence
over `Γ(S,U)`. No smoothness or finiteness assumption is imposed.

The proof first identifies the chosen coordinate algebra of `G` with
all actual global functions on `G`. The bijective actual tensor section
map from `LineHom.SectionsTensor`, after interchanging the tensor factors,
is exactly the constructed map. The composition formula for actual
function pullback identifies the coordinate functions in both descriptions.

`baseChange_augmentation_coordinateMap` proves that evaluation of an
actual coordinate function at the actual base-changed identity is the
base pullback of its original counit. The proof subtracts the corresponding
scalar from the coordinate and applies the previously proved actual
identity-vanishing theorem. The tensor coordinate equivalence therefore
intertwines the tensor augmentation and the actual augmentation. Its
transport of augmentation kernels is a generic algebraic fact about
augmented algebra equivalences.

`baseChangeJetEquiv G b n U` is the resulting actual linear equivalence
from `Γ(S,U) ⊗[R] (B / I^(n+1))` to
`Γ(IdentityJet.module G_S n,U)`, with `B = AffineCoordinates.algebra G`
and `I` its original counit kernel. It composes
`Algebra.SectionJet.baseChangeEquiv`, the augmentation-quotient equivalence
induced by the actual coordinate equivalence, and the inverse of the
actual `IdentityJet.sectionsEquiv`.

`baseChangeJetEquiv_tmul_mk` sends `a ⊗ [c]` to `a` times the restriction
of the prescribed existing global ambient quotient-coordinate section
`[c]` on the actual jet. The theorem `baseChangeJetEquiv_toLinearMap`
identifies its linear map with exactly
`ambientTensorCoordinates G b (identity of G_S) n U`; tensor induction
and representatives of quotient classes prove this identification.
Thus this comparison preserves the previously specified generators.
The base `S` is arbitrary, and the original group is affine over `Spec R`.
Transport from a group over a nonaffine base and the classified
Grassmannian kernel comparison are separate obligations.
