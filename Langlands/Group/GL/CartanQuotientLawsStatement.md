# Intrinsic algebraic laws for concrete Cartan quotient cells

Author: Worker 454.

The declaration
`Langlands.GeneralLinear.CartanQuotient.CartanQuotientLawsStatement.{uF}`
is a closed `Prop` definition. It universally quantifies over every natural
prime parameter `p`, its `Fact p.Prime` instance, every
`F : PadicField.{uF} p`, and each supplied `T : F.TopologicalData`. No algebraic
law below is assumed as a structure field. This pair states a proof target;
it proves none of the new laws. It imports the published
`Langlands.Group.GL.CartanQuotientDefinitions` by module name and changes no
definition or analytic criterion.

Write `q = T.residueCardinality`, `a(lam) = representative T lam`, and
`π = quotientMap F n` in the explanations below. All rank-indexed clauses
range over every `n : ℕ`, including zero, except the last-coordinate clause,
which is stated at rank `m + 1`. There is no representation carrier, hence
no identification of its universe with the independent field universe `uF`.
The proposition is the conjunction of the following six groups, in this order.

## 1. Membership and containment

The first two clauses repeat exactly the already proved `mem_cell` and
`mem_subgroupCell` equivalences: membership means existence of two elements
of the specified subgroup whose double-coset product has quotient image `x`.
The third states
`H ≤ J → subgroupCell T H lam ⊆ subgroupCell T J lam`
for arbitrary ambient subgroups. Taking `J = maximalCompact T n` gives the
required containment in `cell T lam` whenever `H ≤ maximalCompact T n`.
The proof route reuses the two membership theorems and transports the same
two witnesses along the subgroup inclusion.

## 2. Scalars and common shifts

The actual quotient of `GL_n(F)` by its entire center satisfies
`π (scalar a) = 1` for every field unit `a`, and its value on `g` is unchanged
by multiplication by `scalar a` on either side. These three clauses hold
also at rank zero; no scalar embedding or positive-rank hypothesis is used.
One proof route uses the centrality certificate `GeneralLinear.scalarToCenter`;
alternatively Mathlib's
`Matrix.GeneralLinearGroup.center_eq_range_scalar` identifies the quotient
kernel on these scalars. Multiplicativity of `π` gives the two product clauses.

For every integer `c`, the matrix equality is
`a(shift lam c) = scalar (uniformizerUnit T ^ c) * a(lam)`.
Entrywise diagonal multiplication and integer exponent addition prove it.
The order of multiplication agrees with the declared equality; field
commutativity permits the scalar factor to be written first.
The next three clauses state equality of the quotient representatives,
of `subgroupCell T H (shift lam c)` and `subgroupCell T H lam` for **every**
subgroup `H`, and of the corresponding `cell` sets. In the cell proof, apply
the quotient homomorphism to the products and discard the scalar image.
The same witnesses in `H` work in both directions, so this requires no
assumption that `H` contains scalars.

## 3. Radial weights

The five clauses assert
`degree (shift lam c) = degree lam`,
`delta T (shift lam c) = delta T lam`,
`Antitone lam → 0 ≤ degree lam`,
`0 < delta T lam`, and `0 < height lam`.
For the first, each summand is unchanged because
`(lam i + c) - (lam j + c) = lam i - lam j`.
The second follows by unfolding `delta`. For the third, `i < j` and
antitonicity imply `lam j ≤ lam i`, so every summand is nonnegative.
For the fourth, the published residue-cardinality bound `q > 1` gives a
positive real base, and every integer power of a positive real is positive.
For the fifth, all integer absolute values, and thus their finite sum and
real coercion, are nonnegative; the added one makes the result positive.
Both positivity clauses apply to arbitrary tuples, without normalization.
There is no shift-invariance clause for `height`.

## 4. Entries and chamber orientation

The diagonal-entry clause is exactly
`T.normalizedAbs (a(lam) i i) = (q : ℝ) ^ (-lam i)`.
It uses the normalized absolute value from the supplied `T`, rather than
an unrelated field norm. Off-diagonal entries vanish whenever `i ≠ j`.
These follow from `Iwasawa.torus_val`, the diagonal matrix formulas, and
`LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs`.
The last clause says that `Antitone lam` makes the function of diagonal
normalized absolute values **Monotone**. Indeed `i ≤ j` gives
`-lam i ≤ -lam j`, and integer exponentiation is monotone for the base
`(q : ℝ) > 1` (for example, use `zpow_le_zpow_right₀`).

## 5. Actual Levi/Borel matrices and the full upper modulus

The first clause compares underlying matrices: the value of the singleton
`leviEmbedding` on `representativeLevi T lam` equals `(a(lam)).val`.
The second compares the matrix of `representativeBorel T lam`, after its
subgroup coercion to the ambient general linear group, with that same matrix.
Use `BlockShape.leviEmbedding_singletonLevi_val` and `Iwasawa.torus_val`;
the Borel comparison follows from the existing `leviInParabolic` construction.
No replacement Levi, Borel, or matrix realization is introduced.

The remaining clauses identify the real number `delta T lam` separately
with the real coercion of
`T.leviModulus (BlockShape.singletons n) (representativeLevi T lam)` and of
`T.parabolicModulus (BlockShape.singletons n) (representativeBorel T lam)`.
Each coercion first takes the unit's value in `ℝ≥0`, then its real value.
The singleton parabolic is the **upper** Borel, and these are its full
positive modulus characters. They are not inverse or half modulus characters.

For the proof route, `T.leviModulus_singletonLevi` expresses the first
character as the product over `i < j` of
`normalizedAbsUnits (uniformizerUnit T ^ lam i) /
 normalizedAbsUnits (uniformizerUnit T ^ lam j)`.
Coercing to real numbers and using the uniformizer absolute-value formula
turns each factor into `q ^ (-(lam i - lam j))`. Combining the integer
powers over the two finite products yields `q ^ (-degree lam)`.
The second modulus equality then follows from
`T.parabolicModulus_section`. This is an algebraic identification with
published characters, not a new Haar-scaling or cell-volume theorem.

## 6. Normalization and countability

For every `m : ℕ` and `lam : Fin (m + 1) → ℤ`, the statement is
`Normalized lam ↔ Antitone lam ∧ lam (Fin.last m) = 0`.
This expresses all positive ranks without choosing a nonexistent index in
rank zero. For an antitone tuple, the last coordinate is minimal.
An attained zero and nonnegativity therefore force it to be zero.
Conversely, last-coordinate zero forces every coordinate to be nonnegative,
and that last coordinate supplies the required zero witness.

At rank one the exact clause is `Normalized lam ↔ lam = 0`, where zero is
the zero function `Fin 1 → ℤ`. The preceding equivalence and the unique
coordinate of `Fin 1` prove both directions. The final clause
`∀ n, Countable (NormalizedTuple n)` exposes an existing inherited instance:
a function on a finite type with integer values is countable, and so is
its subtype. It is a goal satisfied by instance synthesis, not a new
countability hypothesis.

## Source correspondence and boundaries

Original: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
I.1, printed pp.239–242 (one-based PDF pp.5–8).
Source ID `waldspurger-2003-plancherel`; SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The original retained PDF is
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
These four original pages were read for this pair. No source-specific erratum
was found in the available project or published notes.

Printed p.239 defines the closed positive chamber by nonnegative simple-root
coordinates; p.240 chooses the sign
`q ^ (-⟨χ, H_G(g)⟩) = |χ(g)|` and fixes the special maximal compact subgroup.
Equation (4), p.241, gives the Cartan double-coset decomposition.
Equation (5), pp.241–242, uses the **inverse** upper modulus to estimate
cell volumes. Thus for `GL_n`, decreasing integer exponents give
nonnegative root differences, increasing diagonal absolute values, and
the full upper modulus `q ^ (-degree lam)` that appears in this statement.
The inverse in the volume comparison does not reverse this modulus formula.

The scalar quotient, finite integer tuples, exact shift identities,
subgroup monotonicity, finite root sum, normalization equivalence, and
countability are derived algebraic specializations of the published
concrete definitions; they are not quoted as Waldspurger's verbatim results.
The height `1 + ∑ |lam i|` is an internal coordinate weight. Waldspurger's
`sigma` on p.242 is defined using a matrix norm and is not this height.
This pair asserts no comparison between them. It also asserts no Cartan
covering, uniqueness of cells, topology, measure bound, convergence,
representation hypothesis, or temperedness criterion. Those are separate
targets.
