# Complex determinant characters and twists on product Levis

This internal construction packages the published complex power of a positive
character over every block of an actual standard product Levi. For a p-adic
field `F`, compatible topological realization `T`, block shape `B` of total
rank `n`, and arbitrary vector `z : Fin B.length → ℂ`,
`T.leviComplexPowerCharacter B z` is the actual character

\[
\chi_z((m_i)_i)=\prod_i (|\det(m_i)|_F:\mathbb C)^{z_i}
\quad\text{in }\mathbb C^\times.
\]

The absolute value is the Library's residue-normalized `T.normalizedAbs`,
with uniformizer value `q⁻¹`. The definition is the finite product of
`Langlands.Shahidi.complexPower (T.blockDeterminantNorm B i) (z i)`;
its complex power is Mathlib's complex power of a positive real number.
The domain is the full group `B.Levi F.Carrier`. No tensor representation
or two-block identification is required.

## Evaluation, kernel and norms

`leviComplexPowerCharacter_apply` expresses the value as the product of
the existing `T.determinantComplexPower` characters on the actual blocks.
`coe_leviComplexPowerCharacter` gives the displayed complex value.
The zero, addition and negation identities follow from the corresponding
`Shahidi.complexPower` laws and finite-product identities.
`leviComplexPowerCharacter_ofReal` identifies the character at
`z i = (t i : ℂ)` with the published `T.leviRealPowerCharacter B t`.

`normOneLevi_le_ker_leviComplexPowerCharacter` evaluates each factor at one
on the simultaneous determinant-norm-one subgroup.
`isOpen_ker_leviComplexPowerCharacter` then uses
`T.isOpen_normOneLevi B` and `Subgroup.isOpen_mono`.
Openness refers to the actual product-Levi topology induced by `T`.

`norm_leviComplexPowerCharacter` proves

\[
\|\chi_z(m)\|=\prod_i|\det(m_i)|_F^{\operatorname{Re}(z_i)}.
\]

The proof takes the norm of the finite product and applies
`Complex.norm_cpow_eq_rpow_re_of_pos` to the positive normalized absolute
value of each invertible determinant.
`norm_leviComplexPowerCharacter_imaginary` specializes to
`z i = Complex.I * (u i : ℂ)`, for arbitrary real `u`, obtaining norm one
at every actual Levi element.

`coe_leviComplexPowerCharacter_blockScalar` records the actual scalar
coordinates:

\[
\chi_z((a_i I_{n_i})_i)
=\prod_i(|a_i|_F:\mathbb C)^{n_i z_i},\qquad n_i=B.\mathrm{size}(i).
\]

Here the tuple is `B.blockScalarLevi F.Carrier a`. Its proof uses the
published determinant-of-a-scalar formula and the positive-real complex
power law. The block sizes multiply the determinant exponents;
they are not absorbed into the parameter definition.
`leviComplexPowerCharacter_eq_topologicalData` identifies the characters
for compatible realizations of the same field using equality of their
determinant norms.

## Twists on the same carrier

For any complex representation `σ` of the actual product Levi,
`T.leviComplexPowerTwist B z σ` is the existing `Langlands.twist` by
`T.leviComplexPowerCharacter B z`. It retains `σ`'s complex module and has
action

\[
m\cdot_z v=\chi_z(m)\,(\sigma(m)v).
\]

The file proves this action formula, the zero-twist identity, addition as
iterated twisting, cancellation by the negative parameter in both orders,
and equality to `T.leviRealPowerTwist B t σ` for real complex parameters.
`isSmooth_leviComplexPowerTwist_iff` follows from the open character kernel
and the published `isSmooth_twist_iff`; it assumes no topology on the
representation carrier.

All constructions and identities cover every block shape, including
the empty shape at rank zero and a one-block shape. Empty products are
trivial characters, and no proof requires a positive rank.
The field universe `uF` and representation-carrier universe `uV` are
independent. No admissibility, irreducibility, temperedness, finite
dimension, support, chamber or zero-sum condition is imposed.

## Provenance and source convention

The product-Levi construction and its intrinsic proofs are derived
internally from `Langlands.Representation.Shahidi.Induction`,
`Langlands.Representation.Twist.LeviRealPower`, and their published
determinant, subgroup and scalar-twist dependencies.

The normalization is compared with A. J. Silberger,
*The Langlands quotient theorem for p-adic groups*, Math. Ann. 236
(1978), 95–104, printed p.96, one-based PDF page 2.
The registered source is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The original page image was inspected: its imaginary unit is obscured
by text extraction. Silberger defines

\[
\chi_\nu(m)=q^{\,i\langle\nu,H(m)\rangle},
\qquad \sigma_\nu(m)=\sigma(m)\chi_\nu(m).
\]

Under the established determinant-coordinate convention, the source
parameter `ν` corresponds to Library complex determinant exponent
`i*ν`. Thus source `ν = -i*t`, with `t` real, corresponds to Library
exponent `t`; a real source parameter `u` corresponds to `i*u`,
whose character has norm one by the proved imaginary-parameter formula.
Block-scalar weights still multiply these exponents by block sizes.
This coordinate explanation is motivation for the packaging, rather
than a formalization of the source's general reductive Lie-algebra map.

This pair supplies actual characters and twists and proves their
intrinsic laws. Induced complex families, analytic continuation,
selected class-exponent branches, collision persistence, preservation
of temperedness and multiplicity or quotient comparisons remain
separate obligations.
