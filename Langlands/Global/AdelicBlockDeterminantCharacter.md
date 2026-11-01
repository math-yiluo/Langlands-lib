# Actual adelic block determinant characters

Author: Worker 2.

`Langlands.Global.AdelicBlockDeterminantCharacter` constructs continuous positive
characters on actual number-field matrix groups and their block parabolics.
The field `F : Type uF` has arbitrary universe, with `Field F` and `NumberField F`.
The rank is any natural number. `B : BlockShape n` supplies positive ordered block
sizes summing to that rank, and permits the empty shape at rank zero. The groups
and topologies are the actual units, subgroup and product constructions in
`Global/AdelicGL` and `Global/AdelicBlockParabolic`; no topology on `F` is chosen.
The positive coefficient group is `ℝ≥0ˣ` with its units topology.

`determinantNorm`, `finiteDeterminantNorm` and `infiniteDeterminantNorm` compose
the actual determinant maps with the full, finite and infinite characters of
`Global/IdeleAbsoluteValue`. Their multiplicativity and continuity follow from
those maps. The finite norms have Mathlib's normalized completion convention;
the infinite character raises each completion norm to its real/complex
multiplicity. Thus all normalization is inherited from the constructed idelic
absolute value, without a supplied modulus or local realization.

`determinantNorm_rational` is the product formula applied to the determinant of
an actual rational matrix. `determinantNorm_scalar` is the idelic absolute value
of the scalar raised to the matrix rank, by the determinant of a scalar matrix.
`determinantNorm_split` factors through the genuine infinite and finite matrix
projections; its proof uses determinant naturality under both coefficient
projections. `determinantNorm_ofFinite` computes the restriction to the finite
factor. `coe_determinantNorm_localInclusion` computes the real value at an actual
finite local matrix inserted into the full adelic group: it is the normalized
completion norm of its determinant. The latter two proofs reuse the published
actual determinant insertion identities.

`blockDeterminantNorm`, `finiteBlockDeterminantNorm` and
`infiniteBlockDeterminantNorm` apply the corresponding determinant norm to a
selected block of the actual full, finite or infinite Levi product. The three
continuous characters `leviCharacter`, `finiteLeviCharacter` and
`infiniteLeviCharacter` use the same ordered-pair formula:

\[
 \chi_B(m)=\prod_{i<j}
 \frac{|\det(m_i)|^{b_j}}{|\det(m_j)|^{b_i}},
 \qquad b_i=B.\mathrm{size}(i).
\]

The three `*_apply` theorems expand these finite products. A private helper
packages the finite product of homomorphisms and proves continuity from finite
products, powers and inversion. `leviCharacter_split` factors the full character
as the product of its infinite and finite characters under the actual Levi
splitting. Its proof distributes the determinant factorization over powers,
quotients and finite products.

`rationalLevi` applies the actual rational matrix embedding in each block.
`leviCharacter_rational` follows blockwise from the product formula.
`leviCharacter_scalar` proves value one when the same idele acts as a scalar in
every block: each ordered pair has equal exponents `b_i * b_j` in numerator and
denominator, so each factor is one.

`parabolicCharacter` inflates the full Levi character through the actual
continuous diagonal-block projection. Its section formula is the Levi
projection/section identity. It is one on the actual unipotent radical because
that subgroup is the kernel of the projection. `leviProjection_rational` checks
entrywise compatibility with the rational map, and
`parabolicCharacter_rational` deduces value one on the rational parabolic.

`leviPositiveHalf` uses the canonical square root of positive real units from
`Representation/Jacquet/PositiveCharacter`. Its continuity is proved from
continuity of square root in the units topology, including the archimedean
factor. `leviHalfCharacter` embeds this positive half into `ℂˣ`, continuously.
`leviPositiveHalf_sq` and `leviHalfCharacter_sq` prove the square identities;
`coe_leviHalfCharacter` identifies the complex value with the nonnegative real
square root. The complex half is one exactly when the original positive
character is one, by the published half-character kernel identity. Its rational
and common-scalar restrictions are consequently one.

`parabolicHalfCharacter` inflates this positive complex half through the same
Levi projection. It satisfies the section and square formulas and is one on the
actual radical and rational parabolic. The square is the complex embedding of
`parabolicCharacter`; the chosen half is positive, rather than its inverse.

The provenance is internal. This specializes published determinant, actual
adelic and block-group constructions, then applies finite products, the
constructed normalized idelic character and the published canonical positive
square root. Determinant naturality, the idelic product formula and the actual
Levi projection supply the intrinsic identities. The ordered-pair expression is
the same algebraic expression as the local `Group/GL/BlockModulus` API; this
module makes no new identification with original literature or a Haar modulus.
Identification with adelic Haar scaling, normalized global induction, isobaric
representations and automorphic existence remain separate obligations.
