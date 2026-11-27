# Standard block shapes for a pair of complementary idempotents

Let \(e_1,e_2\in\mathrm{End}_F(F^n)\) be nonzero, with \(e_1+e_2=1\) and
\(e_1e_2=e_2e_1=0\). Then \(F^n=V_1\oplus V_2\) with \(V_i=e_iF^n\). The
group \(1+e_1Ae_2\) (`blockUnipotent e₁ e₂ h₂₁ ⊤` of
`DiagonalSplitTypeRefinement`) is the unipotent radical of the
stabilizer of the flag \(F^n\supset V_1\supset 0\), as in BK93 (8.2.1).
This module expresses it in matrix coordinates by the two-block
parabolic subgroups of `GeneralLinear.BlockShape`.

`exists_blockShape_conjugateUnipotent_le` gives a `BlockShape` \(B\) with
`B.parabolic F ≠ ⊤` and \(g\in\mathrm{GL}_n(F)\) such that
`B.conjugateUnipotent g` is contained in the image of
\(1+e_1Ae_2\) under the inverse of `Matrix.GeneralLinearGroup.toLin`.

The proof takes \(a=\dim V_1\). Both summands are nonzero, so
\(0<a<n\), and \(B\) is the shape `ProductLeviChamber.twoBlock n a`.
It is proper by `Whittaker.UpperUnipotentCoinvariant.cutShape_parabolic_ne_top`.
Bases of \(V_1\) and \(V_2\), joined by `Submodule.prodEquivOfIsCompl`
and reindexed along `finSumFinEquiv`, give a basis of \(F^n\) whose first
\(a\) vectors lie in \(V_1\) and the others in \(V_2\). Let \(\varphi\)
be the automorphism sending the standard basis to it, and let \(E_1\)
be the diagonal idempotent of the first \(a\) coordinates. On the
standard basis, \(\varphi E_1=e_1\varphi\).

An element \(u\) of the standard radical is block unipotent
(`Whittaker.UpperUnipotentCoinvariant.isBlockUnipotent_of_mem_cutShape`).
Its entries agree with the identity except in rows with index less
than \(a\) and columns with index at least \(a\). So `diagonal_mul_sub_one_mul` gives
\(u-1=E_1(u-1)(1-E_1)\) as matrices. Conjugating by \(\varphi\),
\(\varphi(u-1)\varphi^{-1}=e_1\,\varphi(u-1)\varphi^{-1}\,e_2\), which is
membership of \(\varphi u\varphi^{-1}\) in \(1+e_1Ae_2\). The matrix \(g\)
is the inverse image of \(\varphi\) under `toLin`.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.1), printed p. 275.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
