# The continuous congruence limit of finite Hecke avatars

`Langlands.GaloisRepresentation.heckeAvatarInverseLimit` proves
[`HeckeAvatarInverseLimitStatement`](HeckeAvatarInverseLimit.md). It starts with unique
finite characters matching the reductions of an integral idele-class character at
all places outside the same set `S`. At level `n`, the coefficients are the units
of the actual completed integer ring modulo `𝔪^(n + 1)`.

For `n ≤ m`, postcomposing the level-`m` character with
`completionUnitTransition` preserves inertia triviality. By
`completionUnitTransition_reduction`, its geometric Frobenius value is the
level-`n` reduction of the same idele-class value. Uniqueness at level `n` gives
the required equality of continuous characters.

The proof uses `isAdicComplete_adicCompletionIntegers` for both existence and
separation of limits. For a compatible residue sequence, choose a ring
representative at each level. The representatives at levels `n` and `m`
are congruent modulo `𝔪^(n + 1)` when `n ≤ m`, so they are an adic Cauchy
sequence. Adic precompleteness gives a limit. At exponent `n + 1` the limit
is congruent to the representative at level `n + 1`, which reduces to the
given residue at level `n`. Applying this to the values and to the inverses
of compatible quotient units gives two ring elements whose product reduces
to one at every level. Adic Hausdorffness makes them inverse to one another.
It also gives joint injectivity of the reductions, since congruence modulo
`𝔪^(n + 1)` implies congruence modulo `𝔪^n` for each `n`.

The completed integer units are compact by the closed embedding of units into
the product of the ring and its opposite. The product of the discrete quotient
unit groups is Hausdorff. The continuous injective map given by all reductions
is therefore a topological embedding. The pointwise lifts of the finite
characters define a continuous map in this initial topology. Joint injectivity
proves its homomorphism laws and carries up the inertia identity and the
Frobenius comparison for every indicated uniformizer and geometric lift.

This congruence-limit argument implements the continuous avatar step of the
paired statement. Serre constructs the adic representation through the abelian
Galois quotient and derives the unramified and Frobenius comparisons in
*Abelian l-Adic Representations and Elliptic Curves*, Chapter II §2.3,
pp. II-11–II-12, and §2.5, pp. II-18–II-20 (`serre-abelian-l-adic-1989`,
SHA-256 `971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4`).
