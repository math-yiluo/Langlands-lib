# Ordered block parabolic construction

Author: Worker 6.

`BlockShape n` records an ordered finite sequence of positive block sizes and
an equality between their sum and the total rank `n`. Its dependent-sum index
type labels a coordinate by a block and a coordinate inside that block.
`indexEquiv` uses Mathlib's `finSigmaFinEquiv`, followed by the recorded rank
equality. Thus numbering uses consecutive blocks in the given order, not an
arbitrary permutation of a finite set.

All groups are actual matrix unit groups over an arbitrary commutative ring.
The parabolic condition is Mathlib's `BlockTriangular`, with the block index
as ordering map. Its subgroup fields use the existing one, multiplication and
inverse-closure theorems. For inversion, the unit supplies the required
`Invertible` instance; there is no assumed inverse-closure field. The opposite
parabolic reverses the block order. Both are transported to `Fin n` by the
explicit index equivalence.

The Levi factor is the product of the actual general linear groups of the
blocks. Its embedding lifts Mathlib's dependent block-diagonal ring homomorphism
to units and then reindexes to the total rank. The diagonal-block projection
extracts the corresponding submatrices from a matrix and its inverse. In the
diagonal block of a product of two upper block triangular matrices, all
intermediate blocks other than that block contribute zero: one factor is
below the block diagonal. This is proved by splitting the finite matrix sum
over block indices. Applying this identity to the matrix and its inverse
proves both inverse identities for each diagonal block and the
multiplicativity of the projection.

`parabolicCoordinates` identifies the two actual parabolic subgroups by
the same reindexing. The block diagonal map is restricted to this parabolic
to give `leviInParabolic`. Extracting its diagonal blocks is the identity:
`leviProjection_section` proves this using the same-block entry formula
for `Matrix.blockDiagonal'`. Consequently the embedding is injective.
`leviSubgroup` is its actual image in GL, and `leviEquiv` identifies that
subgroup with the product Levi. Its inverse is explicitly diagonal projection
after the inclusion `leviAsParabolic`; no inverse is assumed.

`unipotentRadical` is the kernel of the proved Levi projection, as a subgroup
of the parabolic. Mathlib's kernel instance supplies normality. Its image
under the parabolic inclusion is `unipotentSubgroup`, an actual subgroup
of the ambient GL. The entry lemmas prove that radical membership is
equivalent to having identity diagonal blocks, together with the upper
block triangular condition. Thus this kernel has exactly the intended
upper block unipotent matrices as its carrier.

The Levi acts by conjugation on the normal kernel, through the constructed
section, using `MulAut.conjNormal`. For `g` in the parabolic,
`unipotentPart g` is `g * (leviInParabolic (leviProjection g))⁻¹`.
The section identity proves that it belongs to the kernel. `decomposition`
maps `g` to this element and its Levi projection; the inverse multiplies
the radical element by the embedded Levi element. The two inverse laws
are proved using the kernel equation, the section identity and group
cancellation. This constructs the unique factorization `g = u * m`.
It is a plain equivalence, not a claim that the direct-product group law
agrees with parabolic multiplication. The conjugation action records the
nontrivial action involved.

`mem_parabolic_iff` and `mem_oppositeParabolic_iff` express the zero conditions
in the standard `Fin n` coordinates through `index`.
`leviEmbedding_apply_same` and `leviEmbedding_apply_ne` give its diagonal
and off-block entries. `leviProjection_apply` gives the actual extracted
entries. Both radical membership lemmas give the Kronecker-delta conditions
on every diagonal block.

For a topological commutative ring, the construction supplies continuous
parabolic coordinate change, Levi embedding and projection, the section,
and the equivalence between the product Levi and its matrix image.
Continuity of maps to matrix units is checked on both the matrix and its
inverse through `Units.continuous_iff`. Their entries are continuous coordinate
evaluations, block diagonal assembly, or evaluation after inversion.
`decompositionHomeomorph` proves both directions of the factorization
continuous using multiplication, inversion and the section/projection.
`continuous_leviAction` proves joint continuity of the conjugation action.

With a Hausdorff coefficient topology, the parabolic and opposite parabolic
are closed by Mathlib's closed block triangular condition, pulled back along
continuous reindexing and the units value map. These two closedness statements
do not require continuity of the ring operations. The radical is closed
as the continuous kernel of the Levi projection; its matrix image is closed
because the inclusion of the closed parabolic is a closed map. Assuming
local compactness of the ambient GL, the module obtains local compactness
of the parabolic, opposite parabolic and radical by these closed inclusions.
No compact-open property or GL local compactness is assumed without being
shown as an explicit premise. `PadicBlocks` discharges the local compactness
premises for every supplied and canonical p-adic realization.

The convention follows the original Bernstein--Zelevinsky (1977), Sections
2.1--2.2, printed page 446, and Henniart (2002), Section 2.5, printed pages
594--595: ordered positive blocks, upper block triangular parabolics, diagonal
Levi factors and upper block unipotent radicals. Both original passages were
read. The generic commutative-ring extension, reindexing implementation,
kernel construction and topological proofs are internal derivations using
Mathlib, rather than assumptions imported from those passages.

Sources:

- `bernstein-zelevinsky-1977-induced-i`, Sections 2.1--2.2, printed page 446.
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Retained original:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- `henniart-2002-characterization`, Section 2.5, printed pages 594--595.
  SHA256 `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
  Retained original:
  `C:/Central-Library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`.

The companion `Basic` construction belongs to independently accepted artifact
`cd1132db-8cab-4cab-bd28-0c6164b44dbe`, version 1, published at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
Its complete `Basic` and `Padic` pairs retain the independently reviewed bytes.
Final review receipt `7c88f2621a5047a9a85fe9ef375a8ed0` confirms their
source correspondence, current dependencies and successful final Lake validation.
The construction does not assert that every totally disconnected locally
compact group is nonarchimedean. The separate intrinsic GL nonarchimedean
target remains necessary for the compact-open specialization.
