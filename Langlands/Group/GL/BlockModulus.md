# Explicit standard block modulus and its two halves

Author: Worker 23.

For an actual ordered positive block shape `B` and a supplied compatible
p-adic-field realization `T`, `leviModulus T B` is the positive character

`product_(i<j) |det(m_i)|_F^(n_j) / |det(m_j)|_F^(n_i)`.

Each determinant norm is the published residue-normalized character, with its
proved arithmetic normalization. Multiplicativity is supplied by the finite
product of genuine monoid homomorphisms, not by an assumed character field.
The Levi is the actual product of matrix-unit groups. `parabolicModulus`
inflates this character through the published diagonal-block projection of
the actual upper block parabolic. It agrees with the Levi character on the
actual section and is trivial on the actual unipotent radical. Pairwise
cancellation proves triviality on ambient scalar matrices.

The simultaneous determinant-norm-one conditions define an actual subgroup
of the Levi. Each condition is open by the published determinant-norm theorem
and continuous coordinate evaluation. A finite intersection is open, and
the subgroup lies in the modulus kernel. This proves that kernel open.
Pullback along the continuous Levi projection proves the parabolic kernel
open. Continuity of both characters follows from continuity of the factors
and projection.

The positive square root is the published `Jacquet.positiveHalfCharacter`;
its complex embedding defines `leviHalfModulus`. Its square is the complex
embedding of the full modulus, and its kernel equals the full kernel.
The half is also pulled back to the parabolic, with proved open kernel.
The published inverse-half Jacquet character is definitionally the inverse
of this induction half. Thus the sign and magnitude are explicit.
Independence of compatible field realizations follows from the published
determinant-norm equality, for all four characters. Canonical specializations
use the accepted `canonicalTopologicalData` and the actual canonical Levi and
parabolic topologies, with proved open kernels. Thus every algebraic
`PadicField.{u} p` with prime `p` is covered, in its original field universe,
without an additional field or topology hypothesis. Every ordered positive
block shape is permitted; in particular this covers every positive ambient
rank. The formula also makes sense for the empty shape in rank zero.

This formula is the standard upper-block modulus formula. Its factors are
the determinant contribution of the left-right action
`X_ij -> m_i X_ij m_j^(-1)` on each rectangular off-diagonal block:
the row action contributes `det(m_i)^(n_j)` and the column action contributes
`det(m_j)^(-n_i)`. The Haar-scaling identification is proved downstream:
`Langlands.glBlockModulusHaar` in `Group/GL/BlockModulusHaarProof` proves
`Langlands.GLBlockModulusHaarStatement` of
`Group/GL/BlockModulusHaarStatement`, with no further hypotheses. For every
prime `p`, field `F : PadicField p`, realization `T`, rank `n`, ordered block
shape `B`, supplied measurable space with Borel structure on
`B.unipotentRadical F.Carrier` (which carries the subspace topology induced
by `T`), Haar measure `μ` on it and Levi element `m`, it gives
`μ.map (B.leviAction F.Carrier m) = (T.leviModulus B m)⁻¹ • μ`, where
`B.leviAction F.Carrier m` is conjugation `u -> m u m^(-1)`. Since the
Bernstein--Zelevinsky formula `∫ f(σ^(-1) u) dμ(u) = mod_U(σ) ∫ f dμ` means
that the image of `μ` under `σ` is `mod_U(σ)^(-1) μ`, the reciprocal scalar
says exactly `mod_U(m) = T.leviModulus B m`. This module does not import that
theorem. No Library theorem identifies `leviModulus` with the absolute
determinant of the full conjugation action on the radical (on its Lie algebra
or its matrix coordinates); that identification is not formalized. Neither
identification is assumed by this explicit finite-product construction.

Source conventions: Bernstein--Zelevinsky (1977), section 1.7 and section 1.8,
printed page 444 / PDF page 5, defines the module of conjugation on the
unipotent group, uses its positive half for right-translation induction and
its inverse half for the Jacquet quotient. Sections 2.1--2.2, printed page
446 / PDF page 7, specify the ordered upper-block parabolics and Levi groups.
Henniart (2002), section 2.5, printed pages 594--595 / PDF pages 8--9, fixes
that upper-block induction convention and the residue-normalized determinant
twist. Those original pages were read. The elementary block determinant
formula and its finite-product implementation are an internal derivation;
no unspecified Haar measure or topology on a representation carrier is used.

Sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  sections 1.7--1.8, page 444, and 2.1--2.2, page 446.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`,
  section 2.5, pages 594--595.

Imports are the published `Group/GL/PadicBlocks`,
`Group/GL/NormalizedCharacter` and `Representation/Jacquet/PositiveCharacter`.
No normalized induced representation, normalized Jacquet assembly or
classification theorem is claimed by this pair alone.
