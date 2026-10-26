# The scalar action on segment inductions and their constituents

Author: Worker 264.

The closing theorem
`Langlands.Classification.segmentConstituentCentralCharacter F T`
proves exactly the published proposition
`Langlands.Classification.SegmentConstituentCentralCharacter.{uF, uV} F T`
from [SegmentConstituentCompatibilityStatement](SegmentConstituentCompatibilityStatement.md).
The field universe `uF` and the supercuspidal carrier universe `uV` are
independent and arbitrary. The proof covers every prime `p`, every
`F : PadicField.{uF} p`, every `T : F.TopologicalData` and every segment `Δ`.
The statement pair and the pairs it imports are unchanged.

Fix the representative `A` of `Δ.base`, with rank `r = Δ.rank` and length
`m = Δ.length`. Assume that `A` has scalar character `ω`. Then the theorem
shows that `z · 1_{mr}` acts by
`ω(z)^m · ν^((m-1)/2)(z · 1_{mr})` on the increasing induction
`T.segmentInduced A.obj m _`, on the decreasing induction
`T.segmentInducedDown A.obj m _`, and on every irreducible subrepresentation
or irreducible quotient of the increasing induction. Here `ν^s` on `GL_k` is
`T.determinantPowerCharacter k s`.

The proof is an internal algebraic calculation. It uses the actual
normalized parabolic induction, the actual block tensor product and the
actual scalar matrices. It adds no hypotheses: no unitarity, open kernel for
`ω`, smoothness of the Levi representation, admissibility, finite
dimensionality or irreducibility of the induced representation. The general
lemmas below hold for every block shape, every rank including `0`, and every
carrier universe. The proof uses no classification, square-integrability,
temperedness, exhaustion, nonlinkage or linked-head result. The source
provenance of the formula is that of the published statement, whose Markdown
explains why the formula is derived. This module adds no claim from the
original literature.

## Declarations

`HasScalarCharacter ρ z ω` is the published predicate
`∀ c v, ρ (z c) v = (ω c : ℂ) • v` from `Classification.ConstituentRelations`.

| Declaration | Content |
| --- | --- |
| `GeneralLinear.BlockShape.scalarLevi B R` | The monoid map `Rˣ →* B.Levi R` sending `a` to the constant block scalar `(a · 1, …, a · 1)`. It is `B.blockScalarLevi R` composed with the constant map. |
| `scalarLevi_apply` | Its `i`-th block is `GeneralLinear.scalar a` (by `rfl`). |
| `leviEmbedding_scalarLevi` | `B.leviEmbedding R (B.scalarLevi R a) = GeneralLinear.scalar a`. |
| `scalarParabolic B R` | The same scalars in the upper block parabolic `B.parabolic R`, through `B.leviInParabolic R`. |
| `coe_scalarParabolic` | Its underlying matrix is `GeneralLinear.scalar a`. |
| `leviProjection_scalarParabolic` | Its Levi projection is `B.scalarLevi R a`. |
| `hasScalarCharacter_blockTensor` | If each block factor `σ i` has scalar character `c i`, then `B.blockTensor σ` has scalar character `∏ i, c i` along `B.scalarLevi R`. |
| `Classification.hasScalarCharacter_twist` | If `ρ` has scalar character `ω`, then `twist χ ρ` has scalar character `ω * χ.comp GeneralLinear.scalar`. |
| `Classification.sum_fin_val_real` | `∑ i : Fin m, (i : ℝ) = m (m - 1) / 2`. |
| `Classification.sum_fin_rev_val_real` | `∑ i : Fin m, ((m - 1 - i : ℕ) : ℝ) = m (m - 1) / 2`, with natural subtraction. |
| `T.leviHalfModulus_scalarLevi` | The positive half modulus `T.leviHalfModulus B` is `1` there. |
| `T.parabolicHalfModulus_scalarParabolic` | The inflated half modulus `T.parabolicHalfModulus B` is `1` on `B.scalarParabolic F.Carrier a`. |
| `T.hasScalarCharacter_normalizedParabolicInduced` | For every Levi representation `σ` on `V : Type uV`, a scalar character `ω` of `σ` along `B.scalarLevi F.Carrier` is the scalar character of `T.normalizedParabolicInduced B σ` along `GeneralLinear.scalar`. |
| `T.hasScalarCharacter_normalizedProductInduced` | If each `σ i` has scalar character `c i`, then `T.normalizedProductInduced B σ` has scalar character `∏ i, c i`. |
| `T.coe_determinantPowerCharacter_scalar` | `ν^s(a · 1_k) = |a|^(k s)` in `ℂ`, where `|a|` is `T.normalizedAbsUnits a` and the power is the real power. |
| `T.prod_twistedScalarCharacter` | For exponents `e : Fin m → ℝ` with `∑ i, e i = m (m - 1) / 2`, `∏ i, (ω * ν_r^(e i) ∘ scalar) = ω^m * ν_{mr}^((m-1)/2) ∘ scalar`. |
| `T.hasScalarCharacter_segmentFactor` | `T.segmentFactor A s` has scalar character `ω * ν_r^s ∘ scalar`. |
| `T.hasScalarCharacter_segmentInduced` | The increasing induction has scalar character `ω^m * ν_{mr}^((m-1)/2) ∘ scalar`. |
| `T.hasScalarCharacter_segmentInducedDown` | The decreasing induction has the same scalar character. |
| `Classification.segmentConstituentCentralCharacter` | The exact target. |

The first six declarations are in `Langlands.GeneralLinear.BlockShape`, for
an arbitrary commutative ring `R`. The declarations written with `T.` are in
`Langlands.PadicField.TopologicalData`. In the three `segment` lemmas `A`
is an arbitrary smooth representation of `GL_r(F)` with carrier in `uV`. In
the two induction lemmas `r > 0`, and `m` is arbitrary, including `m = 0`.

## Implemented proof

**Scalars in the Levi and the parabolic.** `leviEmbedding_scalarLevi`
compares matrices. By definition the embedded constant block scalar is
`B.blockScalar R (fun _ => a)`. The published `coe_blockScalar` identifies it
with the diagonal matrix with constant entry `a`, which is the scalar matrix.
The parabolic element `scalarParabolic` is the Levi section applied to
`scalarLevi`. Its Levi projection is computed by the published
`leviProjection_section`.

**The tensor product.** In `hasScalarCharacter_blockTensor`, induction on
`PiTensorProduct` reduces the claim to elements `r • ⨂ f i`. The published
`blockTensor_tprod` applies each `σ i` to its factor. Each factor is then
multiplied by `c i a`, and `MultilinearMap.map_smul_univ` pulls out the
product `∏ i, c i a`. Additivity handles sums.

**The modulus.** The proof reuses the published
`T.leviModulus_scalar` directly, since `B.scalarLevi F.Carrier a` is definitionally
`fun i => GeneralLinear.scalar a`. The half-modulus statements follow from
the published `T.leviHalfModulus_eq_one` and `parabolicHalfModulus_apply`.

**Covariance and right translation.** In
`hasScalarCharacter_normalizedParabolicInduced`, an element `f` of the
induced space is compared pointwise after two subtype extensions. The action
of `z = a · 1_n` is right translation, so `(z · f)(x) = f(x z)` holds by
definition. Since the scalar matrix commutes with `x`
(`Matrix.GeneralLinearGroup.scalar_commute`), `x z = p x` with
`p = scalarParabolic F.Carrier a`. The published
`T.normalizedParabolicInduced_covariant` gives
`f(p x) = sqrt(δ(m)) · σ(m) (f x)` with `m` the Levi projection of `p`. Here
`m = scalarLevi F.Carrier a`, `δ(m) = 1` by `T.leviModulus_scalar`, and
`σ(m) (f x) = ω(a) · f x` by the hypothesis. Hence `(z · f)(x) = ω(a) · f(x)`.
The general product case `hasScalarCharacter_normalizedProductInduced` is this
lemma applied to `σ = B.blockTensor σ` with `hasScalarCharacter_blockTensor`.
Its representation is definitionally
`T.normalizedParabolicInduced B (B.blockTensor σ)`.

**The determinant powers.** `coe_determinantPowerCharacter_scalar` unfolds the
real power character and uses the published `T.determinantNorm_scalar`:
`|det(a · 1_k)| = |a|^k`. It then rewrites `(|a|^k)^s` as `|a|^(k s)`. In
`prod_twistedScalarCharacter` both sides are evaluated at `a`. The left side
becomes `∏ i, ω(a) · |a|^(r e_i) = ω(a)^m · |a|^(r ∑ e_i)`, by
`Finset.prod_mul_distrib` and `Real.rpow_sum_of_pos` (`|a| > 0` because `a`
is a unit). The hypothesis on `∑ e_i` and a ring identity give
`|a|^(r · m (m-1)/2) = |a|^((m r) (m-1)/2)`, which is the right side.

**The two segment inductions.** `segmentFactor A s` is the twist of `A` by
`ν_r^s`, so `hasScalarCharacter_segmentFactor` is `hasScalarCharacter_twist`.
The published `segmentInduced_representation` and
`segmentInducedDown_representation` identify both inductions with
`T.normalizedProductInduced` over the uniform shape of `m` blocks of size
`r`. The increasing factors have exponents `e i = i`, summed by
`sum_fin_val_real` (induction on `m` with `Fin.sum_univ_castSucc`). The
decreasing factors have exponents `e i = m - 1 - i` (natural subtraction).
`sum_fin_rev_val_real` reindexes this sum by `Fin.revPerm`; since
`Fin.rev i = m - 1 - i` for `i < m`, it reduces to `sum_fin_val_real`. Both
segment lemmas then rewrite the target character with
`prod_twistedScalarCharacter` and apply
`hasScalarCharacter_normalizedProductInduced`.

**Constituents.** The closing theorem applies the two segment lemmas to
`A.obj`, with rank `Δ.rank`, length `Δ.length` and the given character.
The degree `Δ.degree` is definitionally `Δ.length * Δ.rank`. For a candidate
`π`, the published `isSegmentSubrepresentation_iff` and
`isSegmentQuotient_iff` (with the given representative `A` and `hA`) turn
the segment relation into an irreducible subrepresentation or quotient
relation for `T.segmentInduced A.obj Δ.length Δ.rank_pos`. These relations
supply an injective, respectively surjective, intertwiner. The published
`HasScalarCharacter.of_injective` and `HasScalarCharacter.of_surjective`
transport the scalar character of the increasing induction to `π`. Both
carriers lie in `max uF uV`, as these transport lemmas require.
