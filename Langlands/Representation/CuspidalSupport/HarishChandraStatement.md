# Harish-Chandra's compact-coefficient criterion for product Levis

Author: Worker 180.

`Langlands.CuspidalSupport.LeviHarishChandraTheorem.{uF,uV}` is a
`Prop`-valued definition of a future proof target. It universally quantifies
`p : ℕ` with `Fact p.Prime`, an actual `F : PadicField.{uF} p`,
compatible `T : F.TopologicalData`, every `n : ℕ`, every
`B : BlockShape n`, and every actual smooth complex representation
`A : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`. The field and
representation carrier universes are independent. The definition explicitly
installs `T.topology` before forming the smooth representation category and
the coefficient condition.

Writing `G = B.Levi F.Carrier` and
`G° = determinantUnitSubgroup T B`, its assertion is exactly

\[
 \operatorname{IsLeviQuasicuspidal}(B,A)
 \quad\Longleftrightarrow\quad
 \operatorname{HasCompactSmoothDualCoefficients}(A|_{G^\circ}).
\]

The left side is the accepted predicate on `A.representation`: every proper
standard block refinement has a subsingleton unipotent coinvariant quotient.
The right side applies the accepted compact-coefficient predicate to the
actual action `determinantUnitRestriction T B A.representation`. This
restriction retains the carrier of `A` and evaluates a subgroup element by
its inclusion in `G`. The subgroup requires normalized determinant absolute
value one in every block, and carries its subgroup topology inside the
product Levi.

In detail, for `ρ₀ = determinantUnitRestriction T B A.representation`,
the right side says that for every vector `v : A` and every algebraic
linear functional `ℓ : Module.Dual ℂ A`,
`IsSmoothVector ρ₀.dual ℓ` implies
`HasCompactSupport (matrixCoefficient ρ₀ ℓ v)`.
Thus smoothness of the functional is tested for the dual of the
**restricted action**. The predicate is reused verbatim; it does not
quantify only over a chosen subspace of functionals or over the dual of
the original action by definition. Compact support is compactness of the
closure of the nonzero locus in `G°`.

The only representation hypothesis is the smoothness built into `A`.
There is no admissibility, irreducibility, finite length, finite dimension,
semisimplicity, scalar central character, or nonzero-carrier assumption.
The pair states the equivalence; it neither proves nor postulates its truth.

## Original source and conventions

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys **31**:3 (1976), 1–68, English
translation (BZ76).

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- PDF SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Read directly for this pair: §§2.39–2.40, printed/PDF p.26; §§3.18
  and 3.20–3.23, printed/PDF pp.34–35. No corresponding errata note
  was present in the current Library.

Section 3.18 defines quasicuspidality through vanishing of the Jacquet
modules for proper refinements of the product group. Section 3.20
defines the open determinant-unit subgroup `G°` block by block.
Theorem 3.21 asserts equivalence of quasicuspidality, its condition (1),
with finiteness of the restriction to `G°`, its condition (4), for every
smooth complex representation. Here “finite” has the meaning of
§2.40(a): compact support of all matrix elements against smooth
contragredient vectors. It does not mean finite dimension.
Sections 3.22–3.23 supply the source's remaining argument via averaging,
unipotent coinvariants, and Cartan parameters. That argument is not
implemented in this statement unit.

The coefficient in §2.39 is `g ↦ ℓ (ρ₀ g⁻¹ v)`, whereas the
Library's `matrixCoefficient` is `g ↦ ℓ (ρ₀ g v)`. Inversion is a
homeomorphism of the topological group `G°`; it carries the closure of
one nonzero locus onto that of the other. Consequently the two
coefficients have compact support simultaneously. Smoothness makes
these coefficients locally constant, so the nonzero locus is also
closed, agreeing with the source's support convention. The source
also observes in the proof of (3) ⇒ (4) that an open subgroup gives
the same smooth contragredient vectors. The formal statement uses the
restricted dual directly and assumes no separate dual-identification
theorem.

The actual p-adic fields and their compatible topologies specialize the
source's nonarchimedean local fields. Positive ordered block shapes
encode its product groups and their standard refinements.

## Rank zero and dependencies

The inclusion of `n = 0` is an elementary internal extension, stated
separately from the positive-rank literature. Since every block has
positive size and the sizes sum to zero, the shape is empty. Its Levi
and determinant-unit subgroup are one-element groups. There is no
proper standard refined parabolic, making the left side vacuous.
Every coefficient on a one-element group has compact support, making
the right side hold for any carrier dimension. This explains the
boundary of the proposed equivalence; no rank-zero proof is supplied
in this pair.

The three imports are the published
`Langlands.Representation.CuspidalSupport.LeviDefinitions`,
`Langlands.Representation.CuspidalSupport.DeterminantUnit`, and
`Langlands.Representation.CompactCoefficient.Classes`.
Their Lean/Markdown pairs are unchanged. These imports supply the
actual quasicuspidality predicate, determinant-unit restriction, smooth
category, and coefficient predicate. There are no new axioms or
placeholder theorems. A proof of this universally quantified proposition
is a separate task.
