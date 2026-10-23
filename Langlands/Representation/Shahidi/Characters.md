# Whittaker characters on the rectangular radicals

This definition unit connects the actual radical matrices in `Shahidi.Geometry`
to the Library's standard Whittaker character. It follows Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)* (1984), printed pages 71–72, especially the conjugate-character kernels
in (0.2) and the functional immediately preceding (0.3).
The registered source is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.

All declarations lie in `Langlands.Shahidi`. The membership and homomorphism
constructions work over arbitrary commutative rings and arbitrary natural
block sizes. The character and kernel constructions use positive block sizes,
written `m+1,n+1`, over a topological commutative ring with an actual
`UnitaryAdditiveCharacter`. This extends the source's local-field setting
only for the elementary construction; it asserts no analytic theorem over
that wider class of rings.

`upper_mem_upperUnipotent` proves that `upper m n R a` lies in the full
upper unipotent matrix group. Its proof splits row and column indices into
the two blocks: the diagonal blocks are identities, the lower-left block
vanishes, and all entries of the upper-right block lie above the diagonal.
`swapRank_mem_upperUnipotent` observes that the numerical rank transport
preserves index inequalities and diagonal entries.
`intertwiningUnipotent_mem_upperUnipotent` then proves membership for the
exchanged radical `U'`. The homomorphisms `upperToUnipotent` and
`intertwiningToUnipotent` restrict the already proved coordinate group
homomorphisms to this subgroup.

`upperCharacter` and `intertwiningCharacter` compose these maps with
`Whittaker.standardCharacter`. Their values are exactly the additive
character of the sum of the first-superdiagonal entries in the actual
total-rank matrix. The two `_apply` lemmas expose this formula. Thus the
character is specified intrinsically on the ambient matrix group, with
the source's exchanged block order retained for `U'`.

`upperJacquetKernel` and `intertwiningJacquetKernel` take the complex
conjugates of these unit-valued characters. The former supplies the
character factor for the swapped functional integrated over `U`; the latter
supplies that for the source functional integrated over `U'`.
The norm lemmas follow from the unitary additive character, and the
`_eq_inv` lemmas prove that complex conjugation equals inversion.
Continuity of both kernels follows from continuity of the radical matrices,
their entries, finite sums, the additive character, and conjugation.

The kernels are only the scalar character factors. This unit does not define
an induced representation, a tensor contraction, an integral or a Whittaker
functional on an induced space. In particular it makes no convergence,
stabilization or local-coefficient existence assertion.
