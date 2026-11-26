# The Hasse kernel of simply connected type B groups

`numberFieldTypeBSimplyConnectedGaloisHasseKernel` proves
`NumberFieldTypeBSimplyConnectedGaloisHasseKernelStatement` in every universe. For an
absolutely almost-simple simply connected group over a number field, the supplied
Tits index and numbering identify the Cartan matrix as `B_n` with `n ≥ 3`. A cocycle
on a finite Galois cover that is trivial after pullback to the full cover at each
place is trivial on the original cover.

The proof recovers the actual type B vector quotient through
`TitsIndexData.typeBVectorQuotientRecovery`. Over the separable closure it is the
split odd norm-one isometry group, which is adjoint. Adjointness descends to the
quotient. The odd quadratic descent realizes it as the norm-one isometry group of a
scalar form on `Fin (2 * n + 1)`. Its polar kernel has dimension zero in
characteristic zero, so the form is nondegenerate.

The resulting central isogeny onto an adjoint group has the full centre of the
source as its scheme-theoretic kernel. The type B Cartan determinant gives two
geometric characters of that centre. The absolute Galois action fixes both because
it preserves zero and there is a unique nonzero character. The character
equivalence for groups of multiplicative type identifies the centre with `μ₂`,
which has two geometric points in characteristic zero. This verifies the kernel
hypothesis of `numberFieldScalarSpinCoverHasse`, which applies to the same group,
cover and cocycle.

The scalar spin Hasse principle appears in Kneser, *Lectures on Galois Cohomology
of Classical Groups* (1969), §5.9, printed pp. 93–95. The spinor-norm sequence used
by the Library's scalar spin proof appears in §5.11, printed p. 99. The retained
source is `kneser-1969-galois-cohomology-classical-groups`, SHA-256
`55309defa8ea7b311d5d6959832029ee6a0245330b7d0e45b2524e62283809a0`.
