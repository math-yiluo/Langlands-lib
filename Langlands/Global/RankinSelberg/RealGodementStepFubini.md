# Fubini for the real Godement step

This module formalizes the inner coordinate separation in Jacquet's
*Archimedean Rankin-Selberg Integrals* (2009), §7.2, equation (7.8). The
lower-rank block has positive rank `t + 1`. In the upper-Borel conventions of
this formalization, the rectangle is a free first column followed by a lower
unitriangular square block. The latter is the long Weyl conjugate of the
actual upper-unipotent matrix.

If `h_J` and `g_J` are the translators in Jacquet's formula, set
`h = h_J w_m`, `g = w_(m+1) g_J`, `x = w_m X`, and `u = v`, where `m = t + 1`.
Reversing rows and columns gives `w_m [v,X] w_(m+1) = [x,w_m u w_m]`.
The source uses the conjugate of its character in both the column and
unipotent factors. For Jacquet's parameter `b`, both factors in Lean use
`a = −b`. The equality `|a| = |b|` preserves the scalar self-dual measures.

The index equivalence places column-zero entries into a copy of `Fin (t + 1)`.
For each free entry of the square block, it reverses the two indices to obtain
an upper entry. The remaining entries are determined by the unitriangular
condition. The scalar product measure therefore separates into the real
self-dual column measure and the upper entry-product Haar from
`RealGodementStepChart`. Summing the simple entries splits the additive phase
into the first entry of the column and the upper Whittaker character.

`realGodementStepFubini` transports absolute integrability from the rectangular
Schwartz slice through this measure-preserving equivalence. Bochner Fubini with
the column integral innermost gives the displayed equality, with the standard
character evaluated on the upper-unipotent variable outside the column
integral. Every measure in the equality is the specified self-dual entry
measure.
