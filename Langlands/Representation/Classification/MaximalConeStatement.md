# Maximal-cone selection of an essentially tempered Jacquet quotient

Author: Worker 19.

`Langlands.GLMaximalConeJacquetQuotientStatement` is a derived proposition
definition for the selection step in the proof of Silberger (1978),
Proposition 7.2. It retains the exponent before coarsening, its concrete
restriction, maximality among all occurring exponents, and an actual quotient
of the whole normalized opposite Jacquet module. The quotient becomes
analytically tempered after removing its real determinant character. This
file does not prove that assertion.

## Quantifiers and actual objects

The field and representation carrier have independent universes `uF` and
`uV`. For every prime `p`, actual finite extension `F` of `Q_p` with compatible
topological data `T`, positive rank `n`, and complex representation
`A : Rep.{uV} ℂ (GL_n(F))`, assume irreducibility and admissibility.
Admissibility includes smoothness. Irreducibility includes nontriviality.
There is no finite-dimensionality or unitarity assumption on `A`, and no
exponent, quotient, or decomposition certificate is part of the input.

The statement supplies positive ordered block shapes `B` and `C` of total
size `n`; smooth split-center characters `χ` and `χC`; a real vector `r` on
`B`; a grouping map `q` from the blocks of `B` to those of `C`; a real
vector `t` on `C`; and a representation `S` of the actual product Levi of
`C`. The carrier of `S` is existentially chosen in `Type uV`, the same universe
as the source: the intended witness is a quotient of a quotient of `A`.
It need not be the same type as `A`. No tensor factorization of `S` is required.

`T.IsDualJacquetExponent B A χ` asserts a nonzero eigenspace in the full
transpose dual of the actual normalized opposite Jacquet module and an open
kernel for `χ`. Transposition on the commutative split center has no inversion.
`T.IsRealPartOf χ r` is the equality

```text
||χ(a)|| = product_i |a_i|^(r_i)
```

for every tuple of units, with the residue-normalized absolute value
`|x| = q_F^(-ord_F(x))`. These are the scalar exponents: determinant exponent
`t_i` corresponds to scalar exponent `n_i t_i` in a block of size `n_i`.

## Concrete cone coarsening and maximality

The formulas are the numerical clauses of the published
`GLParabolicRootWeightConeStatement`, repeated explicitly so no arbitrary
cone predicate is supplied. They require:

- `q` is monotone and surjective, so its fibers are nonempty consecutive runs.
- Each size `C.size j` is the sum of the old block sizes in its fiber.
- `t` is strictly decreasing.
- The sum of `r_i` over a fiber is `(C.size j) t_j`.
- Every prefix within a fiber has nonpositive sum of `r_i - (B.size i) t_(q i)`.

The actual upper block parabolic and embedded Levi for `B` are contained in
those for `C`, as subgroups of `GL_n(F)`. These are conclusions about the
published matrix subgroups. Only the actual field is quantified here; the
separate numerical cone target gives containments over every commutative ring.

The final clause tests every other actual dual exponent of `A`, on every
standard block shape `B'`, and every real part and grouping satisfying those
same five numerical clauses. Its coarsened shape `C'` has at most as many
blocks as `C`. The comparison imposes no already known temperedness or
quotient condition on the competitor. It does not restrict competitors to
refinements of the selected `B` or `C`.

For positive total rank every coarsened shape has at least one block. Its
number of boundaries is `C.length - 1`, the cardinality of the positive-weight
support in Silberger's Lemma 7.1. Thus maximizing `C.length` is exactly the
source's maximization of that cardinality. There is no claim that the
maximizing exponent, original shape, quotient, or coarsening is unique.

## Restricted exponent and the whole Jacquet quotient

The source's restriction to the coarser split center is expressed pointwise:

```text
χC(a) = χ(a ∘ q).
```

The coarser tuple acts as the same scalar in every old block in a fiber.
The statement asserts that `χC` is an actual dual exponent of `A` at `C`
and that its scalar real part is `j ↦ (C.size j) t_j`. These are conclusions;
restriction is not declared to preserve occurrence by definition.

`S` is irreducible and admissible, and the actual homomorphism
`C.blockScalarLevi F.Carrier` acts on it by `χC`. There exists a surjective
complex-linear intertwiner

```text
oppositeJacquet(T, C, A) → S.
```

Its domain is the whole normalized opposite Jacquet module, not a chosen
subrepresentation. An arbitrary class subquotient would be weaker and would
not supply this quotient witness. The source explicitly selects a quotient
in the middle of p.104. No such selection is an input to this statement.

The opposite Jacquet construction quotients by the actual lower block
unipotent group. Its normalization uses the inverse full upper modulus,
whose inverse square root is the positive upper half modulus. This is the
normalized version of the source's displayed quotient of the unnormalized
opposite Jacquet representation. When subsequently used for reciprocity,
the matching upper normalized induction has positive-half-modulus covariance
and right translation. This file does not assert that reciprocity theorem.

## Temperedness and central twists

The remaining conclusion is analytic temperedness of

```text
T.leviRealPowerTwist C (-t) S.ρ
```

on the same carrier, for every Borel Haar measure on the actual quotient of
`C.Levi F.Carrier` by its full center. The published character construction
acts at `(m_j)` by `product_j |det m_j|^(-t_j)`. Its block-scalar restriction
has exponents `-(C.size j) t_j`; hence this twist removes exactly the real
part of `χC`. Its open kernel and preservation of smoothness are proved in
`Twist/LeviRealPower`. This is an actual scalar twist of an arbitrary Levi
representation, not an assumed decomposition into factors.

`IsTemperedModCenter` includes admissibility, a scalar unitary central
character, and membership of every smooth matrix coefficient in `L^(2+ε)`
for every real `ε > 0`. The quantification over measures is nonvacuous:
`T.exists_isHaarMeasure_leviCentralQuotient` supplies a Borel Haar measure.
The full center of a product of positive-rank general linear groups consists
of these block scalars.

The source first works with a unitary central exponent of `A`, then restores
the central twist. This statement includes that restoration explicitly in
its unrestricted real vectors. If `c` is the real determinant exponent of
the ambient central twist, removing it changes `r_i` to `r_i - n_i c` and
`t_j` to `t_j - c`. Fiber-average equalities and residual sums are unchanged,
as are strict differences and the maximizing support. Restoring it shifts
all coarse determinant exponents by `c`. Thus no sum-zero condition, individual
positivity of `t_j`, or unitary central-character hypothesis is imposed on
`A`. Positivity is positivity of adjacent differences, expressed by
`StrictAnti`. The one-block case has vacuous strict decrease; it includes the
essentially tempered case with arbitrary real central twist.

## Original correspondence and retained proof obligations

The main original is A. J. Silberger, *The Langlands quotient theorem for
p-adic groups*, Math. Ann. 236 (1978), 95–104, literature ID
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
retained PDF SHA256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The article was read in full; the original page images at pp.103–104 were
checked for the cone signs, quotient selection, and weak final inequality.
PDF page 1 is printed p.95.

| Original location | Lean content |
| --- | --- |
| Section 1, pp.96–97; Section 3, p.98 | Scalar exponents and normalization, positive real twists from the source parameter `-iν`, and weak tempered bounds. |
| Lemma 7.1 and its preparation, p.103 | Consecutive cone coarsening, strict drops of averaged determinant exponents, and nonpositive residual prefix sums. The coordinate calculation is detailed in the paired `ParabolicConeStatement.md`. |
| Proof of Proposition 7.2, p.104, first two paragraphs | Maximum over all standard pairs and all occurring exponents; restriction to the coarser split center; regular positive parameter; selection of an irreducible quotient of the whole opposite Jacquet module. |
| Proof of Proposition 7.2, p.104, remaining paragraphs | Essential temperedness from maximality and the finer exponent bounds. The last inequality is `≤ 1` in the original image, even though text extraction can render it as `< 1`. |

The source applies to reductive groups. This proposition restricts it to
`GL_n` over finite extensions of `Q_p`, its standard upper block parabolics,
and their actual product Levis. In these coordinates Lemma 7.1 has exactly
the averages and prefix sums above, as derived in the published numerical
cone pair. Neither induction irreducibility for arbitrary reductive groups
nor grouping of equal determinant exponents is added. Equal consecutive
averages are merged by the cone decomposition itself.

The analytic tempered convention is a derived translation of the source's
weak exponent criterion. For a product Levi with unitary scalar central
character, apply the weak coefficient bound `|c(g)| ≤ C Ξ(g)(1+length(g))^d`.
On its chamber modulo the center, Cartan volume is comparable to `δ_0(a)^(-1)`
and `Ξ(a)` is bounded by `δ_0(a)^(1/2)` times a polynomial. For every `ε > 0`,
the resulting integral is bounded by a lattice sum of `δ_0(a)^(ε/2)` times a
polynomial, which converges. The product group has product Cartan measures
and moduli, so this argument needs no tensor factorization of `S`.
This is the direction needed for the stated tempered conclusion.

The retained original sources for that bridge are Silberger (1979), Theorem
4.5.1 and the tempered definition, pp.183–184, and Lemma 4.5.3, pp.185–186
(`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`);
and Waldspurger (2003), I.1(5), p.241, Lemma II.1.1, p.251, and Section III.2,
Proposition III.2.2, pp.265–266 (`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
Those passages were read for the previously published exponent and
product-Levi tempered-induction families. The latter's paired Markdown
provides the detailed analytic correspondence and the Haar-existence proof.
No retained errata for these sources were found in the Library.

This statement isolates the actual maximal-cone construction, not the final
regular Langlands exhaustion theorem. Future proofs must supply finite
spectrum and class-exponent comparison, the numerical cone theorem,
restriction through larger Levis, quotient selection, finer Jacquet
transitivity, the maximality argument, and the analytic bridge. The source's
older Casselman and Langlands preprints are not identified with retained
later editions; no reading or formalization of every transitive original
proof source is claimed. Deriving the final head statement additionally
requires quotient reciprocity, the regular-head theorem and the separate
GL block representation results. None is a proved premise or an axiom here.
