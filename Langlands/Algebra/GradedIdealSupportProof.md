# Positive generation of graded proper-ideal support

`Langlands.Algebra.GradedIdealSupport.positiveGeneration` proves exactly the
published proposition `PositiveGenerationStatement.{u, v, w}`. The field `k`,
the commutative Noetherian domain `R`, and the additive commutative grading
group `Λ` have independent universes. The ideal `I` is proper, and only `I`
is internally graded by the `k`-submodules `W χ`. The multiplication hypothesis
is the one in the statement: products add labels. The proof neither constructs
nor assumes a grading of the whole ring.

This is an internal commutative algebra generalization motivated by
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3,
Example 3.3.2, printed pp.107–108 / PDF pp.133–134. The registered original is
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source proves the augmentation-weight assertion using a local filtration.
The Lean proof instead uses Krull intersection directly for the given proper
ideal; it is not a separately numbered assertion of the book.

The private helper `homogeneousProjection` inverts the internal direct-sum
map and takes its component at a label. It is a `k`-linear endomorphism of
`I`, acts as the identity on that component, and kills every component with
a different label. `homogeneous_induction` expresses that an additive
predicate on `I` follows from its zero, homogeneous, and addition cases.
`square_induction` uses Mathlib's dependent ideal-product induction: a
predicate closed under addition and true on all products of two elements
of `I` holds on every element whose underlying ring element lies in `I²`.
This uses the actual ideal product; ring coefficients are already absorbed
in its two factors.

The key helper `excluded_mem_pow` fixes any additive subsemigroup `S`
containing `cotangentLiftSupport I W` and proves the following by induction
on `n`: if `χ ∉ S` and `x ∈ W χ`, then the underlying element of `x` belongs
to `Iⁿ`. The initial case is `I⁰ = R`. At the induction step, the actual
class `I.toCotangent x` must vanish, since otherwise `χ` would belong to `S`.
Mathlib's `Ideal.toCotangent_eq_zero` therefore gives `x ∈ I²`.

Project an ideal-square expression for `x` onto `χ`. To check each projected
product, apply homogeneous induction to both factors. A product of labels
`α` and `β` projects to zero unless `α + β = χ`. In the latter case at least
one of `α` and `β` is outside `S`, since `S` is closed under addition. That
factor belongs to `Iⁿ` by the induction hypothesis; multiplying by the other
factor in `I` gives membership in `Iⁿ⁺¹`. Linearity and square induction give
the same membership for the projection of `x`, which equals `x`. No
homogeneity assumption on ideal powers or on the quotient is used.

For the first inclusion in the theorem, set `S` to the positive additive
semigroup closure of the cotangent lift support. A nonzero homogeneous
element with label outside `S` would belong to every `Iⁿ`.
`Ideal.iInf_pow_eq_bot_of_isDomain`, using Noetherianity, the domain assumption,
and properness, makes that element zero, a contradiction.

For the other inclusion, a homogeneous lift with nonzero cotangent class is
itself nonzero. Induction on `AddSubsemigroup.closure` combines witnesses
using multiplication in the domain, so their product remains nonzero and has
the sum label. This induction has only generator and addition cases. It
inserts no empty-sum zero, handles empty support, and retains a zero label
precisely when it occurs. The proof has no field-characteristic restriction,
no ordered-grading hypothesis, and no quotient support-realization premise.
