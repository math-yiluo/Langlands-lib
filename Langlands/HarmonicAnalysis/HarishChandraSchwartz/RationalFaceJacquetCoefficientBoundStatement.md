# Facewise Jacquet coefficient growth on actual rational points

A derived prerequisite for the Xi upper bound.

`RationalFaceJacquetCoefficientBoundStatement` is an assertion at arbitrary
field universe `u` and coefficient-space universe `uV`. Let `F` be a
nonarchimedean local field and `G` a connected reductive affine group locally
of finite type over `F`. Fix a maximal split torus `i : S → G`, a generic
cocharacter, a subset `J` of the simple relative roots, and an existing standard
cocharacter for that face. Fix a closed matrix representation with a finite
nonempty index type, an arbitrary complex representation `π` of `G(F)` on `V`,
and a natural number `r`.

Assume that for every point of the cocharacter lattice annihilating `J`, the
normalized Jacquet operator at its uniformizer power differs from the identity
by an endomorphism whose `r`th power is zero. The normalization is by the inverse
square root of `standardUnipotentModulus`, the actual Haar modulus of conjugation
on the closed standard radical `U_J(F)`.

Then there is a natural degree `d`, chosen before the vector, algebraic Jacquet
functional, and ambient lattice translation. For every such vector `v`,
functional `ell`, and translation `m`, there is a nonnegative real constant `C`
such that for every face lattice point `x`,

`‖ell(j(π(ϖ^(x+m))v))‖ ≤ C sqrt(δ₀(ϖ^(x+m))) (1 + rationalHeight ρ (ϖ^(x+m)))^d`.

The quotient map is the actual unnormalized coinvariant map for `U_J(F)`.
The target uses the minimal modulus `rationalMinimalModulus`, evaluated through
`uniformizerPowersParabolic`, and the actual matrix height. No dominance
condition on `x`, `m`, or their sum is imposed. The vector space need not be
finite dimensional, the functional need not be continuous, and the statement
requires neither smoothness nor admissibility of `π`.

This is a derived assertion, rather than a transcription of a numbered
literature result. Its derivation combines the algebraic unipotent lattice
coefficient bound, Smith normal form on the face sublattice, the published
character-height estimate, and the published central modulus factorization.
Choose a sublattice basis before `m`; its coordinate sum is bounded by a
constant times one plus the height at `ϖ^(x+m)`. Apply the unipotent coefficient
bound to the normalized Jacquet action and the quotient of `π(ϖ^m)v`.
Undo Jacquet normalization at `ϖ^x`. Since this point is central in `M_J(F)`,
its radical modulus equals its minimal modulus. Multiplicativity then absorbs
the inverse square root of `δ₀(ϖ^m)` into `C`.

This module supplies a prerequisite statement and auxiliary lattice
constructions. It does not prove the Jacquet unipotence hypothesis, assemble
the finitely many faces using Casselman asymptotics, or prove the full Xi upper
bound. The statement is proved as `rationalFaceJacquetCoefficientBound` in
`RationalCentralLatticeBounds`.
