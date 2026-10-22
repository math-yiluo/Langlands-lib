# Full upper unipotent matrix group

Author: Worker 6.

The carrier of `upperUnipotent n R` is a subgroup of the actual
`Matrix.GeneralLinearGroup (Fin n) R`. A matrix belongs precisely when its
strictly lower entries vanish and each diagonal entry is one. The coefficient
ring is any commutative ring, and zero rank is allowed. The convention agrees
with Jacquet--Piatetski-Shapiro--Shalika (1981), Section 1.2, printed page 200:
`N_r` is the strict upper triangular group, and formula (2) is the product of
the additive character evaluated at the adjacent upper entries. The original
page was read and its matrix formulas visually checked. Since an additive
character sends sums to products, our sum interface gives exactly that
character input. The generic ring generality and the intrinsic Lean
construction are internal derivations, not further claims attributed to
the paper.

Subgroup closure is proved from Mathlib's block triangular multiplication
and inverse closure. The diagonal of a product of two upper triangular
matrices is the product of their diagonal entries: every other summand
vanishes in one factor. Applying that identity to a matrix and its inverse
gives diagonal entries one for the inverse. No unipotent group law or
inverse property is an input assumption.

For rank `n + 1`, the adjacent upper entry at `(i.castSucc, i.succ)`, for
`i : Fin n`, adds under multiplication. The proof reduces the matrix sum to
the two endpoints. Every other index is before the first endpoint or after
the second, so one matrix entry is zero. The two diagonal entries are one.
`adjacentEntry` packages this identity as a homomorphism to
`Multiplicative R`; this is the additive group of the ring with multiplicative
notation. `superdiagonalSum` adds all these entries and is another such
homomorphism. The inverse formula is obtained from preservation of inverses
by `adjacentEntry`. In rank one the sum is the empty sum, hence zero.

Every entry and adjacent coordinate is continuous for any topology on the
ring, using the subgroup topology and the actual GL entry maps from `Basic`.
Continuity of the sum assumes `IsTopologicalRing R`. Hausdorffness makes the
group closed, as the intersection of the triangular zero conditions and
the equations fixing diagonal entries to one. Closedness transfers local
compactness from the ambient GL. It does not assume or prove a compact-open
basis. The character itself and its Whittaker representation remain with
their assigned construction task.

The only project import is `Langlands.Group.GL.Basic`, in independently accepted
artifact `cd1132db-8cab-4cab-bd28-0c6164b44dbe` version 1, published at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
Final review receipt `7c88f2621a5047a9a85fe9ef375a8ed0` confirms the unchanged
reviewed pairs, their current dependency closure and successful final Lake validation.

Source: `jpss-1981-conductor`, H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika,
*Conducteur des representations du groupe lineaire*, Math. Ann. 256 (1981),
199--214; Section 1.2, formula (2), printed page 200. Retained original PDF:
`C:/Central-Library/Jacquet-Piatetski-Shapiro-Shalika--Conducteur des representations du groupe lineaire--1981.pdf`.
SHA256: `986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
No conductor or essential-vector theorem is used here.
