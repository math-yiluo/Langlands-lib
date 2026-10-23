# Real determinant characters and twists on product Levis

This pair constructs a character of the actual product Levi of an ordered block
shape and its action on arbitrary complex representations of that Levi. All
intrinsic laws displayed in the Lean file are proved. This is an internal
composition of published constructions, not a new exponent criterion or a proof
of the Langlands quotient theorem.

For a p-adic field `F`, compatible topological realization `T`, block shape `B`
of total rank `n`, and arbitrary real vector `t : Fin B.length → ℝ`,
`T.leviRealPowerCharacter B t` is the monoid homomorphism

\[
 (m_i)_i \longmapsto \prod_i |\det(m_i)|_F^{t_i}\quad\text{in }\mathbb C^\times.
\]

The absolute value is the Library's residue-normalized `T.normalizedAbs`, with
uniformizer value `q⁻¹`. Each real power is positive and is embedded in the
complex units. The domain is `B.Levi F.Carrier`, the actual product of the block
matrix groups. No arbitrary character or character-existence hypothesis is
supplied. The definition is the finite product of `realPowerCharacter` applied
to `T.blockDeterminantNorm B i`. The evaluation lemmas expose both this product
of unit-valued characters and its complex value in terms of actual determinants.

The exponents have no regularity, sign or zero-sum restriction. The construction
also includes total rank zero: the block shape is then empty and the character
is the empty product, hence trivial. The field universe `uF` and representation
carrier universe `uV` remain independent.

## Character laws and scalar coordinates

`leviRealPowerCharacter_zero`, `leviRealPowerCharacter_add`, and
`leviRealPowerCharacter_neg` prove the trivial, product and inverse character
identities for zero, sum and negative vectors. They follow pointwise from the
published real-power laws and finite-product identities.

`normOneLevi_le_ker_leviRealPowerCharacter` proves that the simultaneous
norm-one determinant subgroup lies in the character kernel. Its proof evaluates
each factor at one. The published `T.isOpen_normOneLevi B` and
`Subgroup.isOpen_mono` then prove `isOpen_ker_leviRealPowerCharacter` for the
product-Levi topology induced by `T`. This is the precise smoothness property
needed for scalar twisting; no topology on a representation carrier is assumed.

For block scalars `a = (a_i)_i`, the lemma
`coe_leviRealPowerCharacter_blockScalar` proves

\[
 \chi_t(\operatorname{diag}(a_i I_{n_i}))
 = \prod_i |a_i|_F^{n_i t_i},\qquad n_i=B.\mathrm{size}(i).
\]

Here the displayed block-diagonal notation denotes the tuple
`B.blockScalarLevi F.Carrier a` in the product Levi, not an assumed abstract
centre. The proof combines the published determinant-of-a-scalar formula with
`Real.rpow_natCast_mul`. This distinguishes determinant coordinates `t_i` from
split-centre coordinates `n_i t_i`. The lemma
`coe_leviRealPowerCharacter_scalar` specializes to a common scalar `a`, obtaining
`|a|_F^(∑ i, n_i*t_i)` by the finite-sum exponent law and positivity of the
normalized absolute value of a unit.

`leviRealPowerCharacter_eq_topologicalData` proves that compatible realizations
`T` and `U` of the same field give equal characters, using the published equality
of their determinant norms.

## Twisting arbitrary Levi representations

`T.leviRealPowerTwist B t σ` is the published scalar-twist construction on the
same complex module as the actual representation `σ` of `B.Levi F.Carrier`.
Its action is `χ_t(m) • σ(m)`. No tensor decomposition, irreducibility,
admissibility, central character or temperedness is an input.

The paired file proves the action formula, zero-twist identity, addition of
exponents as iterated twisting, cancellation in both orders by the negative
vector, and `isSmooth_leviRealPowerTwist_iff`. The algebraic identities reuse the
published scalar-twist laws; smoothness uses the open kernel proved above and
`isSmooth_twist_iff`. In particular, removing and restoring an arbitrary real
Levi twist is an actual representation construction.

## Provenance and scope

This is an internal finite-product specialization of the current Library's
`Langlands.Representation.Twist.RealPower`,
`Langlands.Representation.Twist.AlgebraProof`,
`Langlands.Group.GL.BlockModulus`, and
`Langlands.Group.GL.BlockIwahoriDefinitions`. It imports those modules directly
and preserves their determinant normalization and scalar-twist convention.
There is no additional external theorem claim or unproved intrinsic obligation.

The intended downstream application is the maximal-cone construction for
Langlands exhaustion: one needs to remove the real central part from an
arbitrary selected Levi constituent. This pair only supplies that twist and
its coordinate formulas. It does not select a constituent, prove a whole-Jacquet
quotient exists, prove temperedness after untwisting, identify opposite-Jacquet
normalizations, or establish any induction compatibility or quotient theorem.
Those are separate proposition families and proof obligations.
