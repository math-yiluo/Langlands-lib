# Actual adelic block characters from Hecke characters

Author: Worker 2. Provenance: internal specialization of the published
`HeckeCharacter.adelicDeterminant`, actual adelic block Levi geometry, finite
products and the scalar representation construction. No new identification
with original literature is asserted.

The number field `F : Type uF` has arbitrary universe. Every natural rank `n`
and ordered positive block shape `B` is allowed, including the empty shape in
rank zero. The groups are the actual general linear groups over the full,
finite and infinite adele rings; the full Levi is the actual product of its
matrix blocks. No topology on the number field itself is chosen.

For actual continuous complex Hecke characters `χ_i` on the actual idele-class
group, `leviCharacter` is the continuous character
`m ↦ ∏_i χ_i.onIdeles(det(m_i))` on the full adelic block Levi. Its multiplicative
and continuity obligations use the actual determinant characters and finite
products. The codomain is `ℂˣ`; the inputs need not be unitary or finite order.

`centralCharacter = ∏_i χ_i^(B.size i)` is an actual Hecke character.
`leviCharacter_scalar` identifies its idele pullback with the common-scalar
restriction of `leviCharacter`. The proof uses the actual determinant of a
scalar block and evaluates the finite product of continuous homomorphisms;
thus each block contributes its own rank exponent. `leviCharacter_rational`
is one on every actual rational Levi point, using rational triviality of each
Hecke determinant character.

`finiteLeviCharacter` and `infiniteLeviCharacter` restrict along the inclusions
of the actual finite and archimedean Levi factors. Their evaluation lemmas
identify the individual block insertions. `leviCharacter_split` factors the
full character as infinite times finite by the genuine multiplicative
splitting of the full Levi.

`parabolicCharacter` inflates through the actual continuous diagonal-block
projection. Its section formula and triviality on the actual unipotent radical
and rational parabolic are proved. Radical triviality uses the projection
kernel; rational triviality checks compatibility of the block projection with
actual rational matrix insertion. If all the Hecke characters coincide,
`parabolicCharacter_constant` identifies this character with the actual full
determinant pullback, by the published determinant-of-a-block-parabolic theorem
and preservation of finite products.

`leviRepresentation` is the one-dimensional complex scalar action on `ℂ`
constructed from this character. Its value is `χ(m) * v`, and the action is
jointly continuous by continuity of the character, unit coercion and complex
multiplication. If every input has finite order, `leviCharacter_isLocallyConstant`
proves local constancy on the entire Levi: each factor pulls back the published
finite-order Hecke local-constancy theorem along the actual determinant and
coordinate projection, and finite products preserve local constancy.
`finiteOrderSmoothCharacter` uses the resulting open kernel in the existing
`Induction.SmoothCharacter` API.

This unit asserts no smoothness of arbitrary continuous Hecke characters,
nonzero induced sections, Haar-modulus identification, induced irreducibility,
automorphic existence or isobaric classification. These remain separate
construction or theorem obligations.
