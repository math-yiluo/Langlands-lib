# Intrinsic laws of concrete Cartan quotient cells

Author: Worker 553.

The theorem
`Langlands.GeneralLinear.CartanQuotient.cartanQuotientLaws.{uF}`
proves the exact closed Library proposition
`Langlands.GeneralLinear.CartanQuotient.CartanQuotientLawsStatement.{uF}`.
It imports `Langlands.Group.GL.CartanQuotientLawsStatement` and changes neither
that pair nor any definition it imports. The field universe `uF` is unrestricted.
The theorem adds no hypotheses: it quantifies over `p : ℕ`, `[Fact p.Prime]`,
`F : PadicField.{uF} p`, and `T : F.TopologicalData`, exactly as the statement
does. All rank-general clauses apply to `n = 0` as well.

All public helpers below are in
`Langlands.GeneralLinear.CartanQuotient`. In the formulas write
`q = T.residueCardinality`, `u = uniformizerUnit T`, and
`π = quotientMap F n`. The quotient is the actual quotient by the entire
center of the actual matrix general linear group.

## Membership, scalar quotient, and shifts

`subgroupCell_mono T H J lam hHJ` transports the same two subgroup witnesses
along `hHJ : H ≤ J`. The final theorem reuses the published `mem_cell` and
`mem_subgroupCell` equivalences directly.

`quotientMap_scalar F n a` uses the centrality certificate
`GeneralLinear.scalarToCenter a` and `QuotientGroup.eq_one_iff` to prove
`π (scalar a) = 1`. `quotientMap_scalar_mul F n a g` and
`quotientMap_mul_scalar F n a g` follow by multiplicativity of `π`.
These arguments use no injectivity of the scalar homomorphism, so they also
apply in rank zero.

`representative_shift T lam c` has the exact orientation
`representative T (shift lam c) =
 scalar (u ^ c) * representative T lam`.
The proof applies equality of underlying unit values, unfolds
`Iwasawa.torus_val`, and multiplies two diagonal matrices. The remaining
entrywise equality is `u ^ (lam i + c) = u ^ c * u ^ lam i`, by integer
exponent addition and commutativity. Here the powers are taken in
`F.Carrierˣ`, then coerced into the field for matrix entries.

`quotientMap_representative_shift T lam c` discards the scalar image.
`subgroupCell_shift T H lam c` applies the quotient homomorphism to each
double-coset product and rewrites its middle image using this equality.
Thus the same witnesses work in both directions for every subgroup `H`;
no assumption that `H` contains scalars occurs.
`cell_shift T lam c` specializes this equality to `maximalCompact T n`.

## Radial weights and diagonal entries

`degree_shift lam c` cancels the common integer summand in each difference
of the finite root sum. `delta_shift T lam c` unfolds `delta` and uses it.
`degree_nonneg lam hlam` applies finite-sum nonnegativity twice; a filtered
index has `i < j`, so antitonicity gives `lam j ≤ lam i`.
`delta_pos T lam` uses `T.residueCardinality_gt_one` to obtain a positive
real base and then positivity of integer powers.
`height_pos lam` uses nonnegativity of integer absolute values and their
finite sum, its real coercion, and the strictly positive added one.
The last two helpers apply to arbitrary tuples.

`representative_diagonal_abs T lam i` evaluates the diagonal entry in
`Iwasawa.torus_val` and applies
`LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs`. Its result is
`T.normalizedAbs (representative T lam i i) = (q : ℝ) ^ (-lam i)`.
`representative_offDiagonal T lam i j hij` uses the same matrix formula
when `hij : i ≠ j`.
`representative_diagonal_abs_monotone T lam hlam` compares the displayed
powers by `zpow_le_zpow_right₀`: antitonicity of `lam` makes `-lam`
monotone, and `(q : ℝ) ≥ 1`.

## Actual Levi and Borel matrices and modulus

`representativeLevi_val T lam` is the published
`BlockShape.leviEmbedding_singletonLevi_val` at the family
`fun i => u ^ lam i`; its diagonal matrix is definitionally the value of
`representative T lam`.
`representativeBorel_val T lam` reuses this equality because the
`leviInParabolic` coercion has that same ambient matrix.

`delta_eq_leviModulus T lam` starts with the defining real integer power
`(q : ℝ) ^ (-degree lam)`. The private helper `real_zpow_sum`, proved by
finite-set induction using `zpow_add₀` at a nonzero real base, converts the
two negated finite sums into a product of
`(q : ℝ) ^ (-(lam i - lam j))` over `i < j`.
The other side is expanded with `T.leviModulus_singletonLevi`.
The proof moves each finite product and quotient through the unit-value
coercion into `ℝ≥0`, then through its coercion into `ℝ`.
`T.normalizedAbsUnits_coe` and `uniformizerUnit_zpow_abs` identify each
factor with `(q : ℝ) ^ (-lam i) / (q : ℝ) ^ (-lam j)`.
Finally `zpow_sub₀` and integer arithmetic give the same exponent
`-(lam i - lam j)`. Nonzeroness of the base follows from `q > 1`.
The coercion in the conclusion is exactly from the modulus unit to its
value in `ℝ≥0`, then to `ℝ`.

`delta_eq_parabolicModulus T lam` uses the already defined
`representativeBorel` and `T.parabolicModulus_section` to reduce to the
Levi equality. These identify `delta` with the **full upper** positive
modulus characters; no inverse or square root is introduced.

## Normalization and assembly

`normalized_iff_antitone_last_eq_zero m lam` applies to
`lam : Fin (m + 1) → ℤ` and proves
`Normalized lam ↔ Antitone lam ∧ lam (Fin.last m) = 0`.
For the forward implication, an attained zero bounds the last coordinate
above by zero using antitonicity and `Fin.le_last`; normalization bounds
it below by zero. Conversely, a zero last coordinate and antitonicity
make every coordinate nonnegative, and the last coordinate witnesses an
attained zero.

`normalized_one_iff lam` specializes this result to rank one.
All indices of `Fin 1` equal `Fin.last 0`, so the function is the zero
function precisely when it is normalized.
The final closed theorem assembles these helpers in the statement's six
groups and obtains `Countable (NormalizedTuple n)` by the existing
inherited instance. It creates no replacement membership or countability
proof.

## Provenance and scope

Original: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333,
I.1, printed pp.239–242 (one-based PDF pp.5–8).
Source ID `waldspurger-2003-plancherel`; SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Retained original:
`/home/taskhub/central-library/Waldspurger--La formule de Plancherel pour les groupes p-adiques d'apres Harish-Chandra--2003.pdf`.
These four original pages were read for this proof. No matching
source-specific erratum was located in the available project notes.

Printed p.239 defines the positive chamber by nonnegative simple roots;
p.240 specifies `q ^ (-⟨χ, H_G(g)⟩) = |χ(g)|`.
For `GL_n` this gives decreasing integer exponents, nonnegative differences
`lam i - lam j` for `i < j`, and increasing diagonal absolute values.
Equation (4), p.241, states the Cartan decomposition; equation (5),
pp.241–242, estimates cell volumes using the inverse modulus.
The upper modulus proved here is the direct product of the root quotients,
`q ^ (-degree lam)`, with this same sign convention.

The scalar quotient, exact shift identities, finite root sum, and
normalization are derived algebraic specializations of the published
constructions, not verbatim theorems from Waldspurger. The coordinate
height `1 + ∑ |lam i|` is internal; Waldspurger's `sigma` on p.242
comes from a matrix norm, and no comparison or height shift invariance is
claimed. This proof establishes exactly the closed intrinsic-laws target;
it supplies no normalized Cartan covering or disjointness, scalar valuation
factorization, quotient-equality lifting, volume estimate, summability,
or representation-theoretic conclusion.
