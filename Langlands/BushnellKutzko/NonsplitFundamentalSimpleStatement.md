# Semisimplicity criterion for nonsplit fundamental strata

For `[𝔄,n,n−1,α]` nonsplit fundamental with `n ≥ 1`,
`NonsplitFundamentalSimpleStatement` asserts that the stratum is equivalent
to a simple stratum on the same chain and at the same levels if and only if
the residue centralizer `ℛ` is semisimple.

`Stratum.residueCentralizer` is the actual subalgebra of `𝔄/𝔓` consisting
of classes with a lift `x` satisfying `αx − xα ∈ 𝔓^{1−n}`. The quotient is
formed from the chain's two-sided first filtration ideal. Scalar reduction
acts on the quotient because the maximal ideal of the integer ring sends
each lattice forward by the period. The lemma
`Stratum.mk_mem_residueCentralizer_iff` checks the equivalent test on any
lift when `α ∈ 𝔓^{−n}`. The commutator changes sign when its entries are
reversed, so this test is the congruence `xα ≡ αx` in the source.
`IsSemisimpleRing` expresses semisimplicity of the resulting algebra.

The two clauses use the same `Stratum.NonsplitSimpleCriterion`. One uses
the valuation ring `𝒪[F]` of an arbitrary nonarchimedean local field `F`.
The other uses `subfieldIntegers F E`, the integral closure of `𝒪[F]` in an
arbitrary finite extension `E/F`. The latter clause applies directly to the
derived-stratum model in `End_E(V)` with `E = F[γ]`, as used in BK94 (5.5)
and (5.6). The criterion is independent of additive characters.

Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.4.13), printed p. 75 (PDF p. 87), proved in §2.5, pp. 76–83.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
Bushnell and Kutzko, *Simple types in GL(N): computing conjugacy classes*
(1994), (5.5)–(5.6), printed p. 133 (PDF p. 146). Literature ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA-256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
