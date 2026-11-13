# Nonvanishing of the L-polynomial of a unitary generic pair on `Re(s) ≥ 1`

Author: Worker 3657.

This module defines the proposition
`Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement.{uF,uV,uW}`.
It is a statement target, not a proof. It states the non-Archimedean case of
Getz–Hahn, Theorem 11.5.2, for p-adic fields: for irreducible admissible
generic unitary representations `π` and `σ` of general linear groups,
`L(s, π × σ)` is holomorphic and nonzero for `Re(s) ≥ 1`. The module imports
`PadicPairFactors`, `Whittaker.GeneralLinear` and `Unitary.Basic`. It changes
no published file and introduces no new factor.

## Source

Getz and Hahn, *An introduction to automorphic representations*, 2024
(registered source `getz-hahn-2024-automorphic-representations`):

- §11.5, printed page 304 (PDF page 315): `F` is a local field, `ψ` a
  nontrivial additive character, and `π`, `π'` are irreducible admissible
  generic representations of `GL_n(F)` and `GL_m(F)`. The display above
  (11.19) takes `W ∈ 𝒲(π, ψ)` and `W′ ∈ 𝒲(π′, ψ̄)`: the second
  representation uses the Whittaker model for the complex conjugate
  character `ψ̄`. The bar is visible on the rendered page; text extraction
  drops it. Displays (11.19) (`m < n`) and (11.20) (`m = n`) define the
  local Rankin–Selberg integrals on these Whittaker models.
- Proposition 11.5.1, printed pages 304–305 (PDF pages 315–316), for
  non-Archimedean `F`: (a) for unitary `π` and `π'` the integrals converge
  absolutely for `Re(s) ≥ 1`; (b) they are rational functions of `q^(-s)`;
  (c) there is a unique polynomial `P_(π,π')` with `P_(π,π')(0) = 1` whose
  reciprocal at `q^(-s)` generates the span of the integrals as a
  `C[q^s, q^(-s)]`-module. The spans in (c) also run over
  `𝒲(π, ψ) × 𝒲(π′, ψ̄)`. Display (11.21) sets
  `L(s, π × π') = P_(π,π')(q^(-s))^(-1)`.
- Theorem 11.5.2, printed page 305 (PDF page 316): "If `π` and `π'` are
  unitary, then `L(s, π × π')` is holomorphic and nonzero for `Re(s) ≥ 1`."
  The text adds that this follows from Proposition 11.5.1 in the
  non-Archimedean case and refers to [BR94a, §2] for the Archimedean case.

The genericity of `π` and `π'` is part of the standing hypotheses of §11.5,
so it is a hypothesis of the theorem.

## Quantifiers and hypotheses

The binders follow the published `SquareIntegrableLPolynomialNonvanishingStatement`
in the same directory:

- every `p : ℕ` with a `Fact p.Prime` instance and every
  `F : PadicField.{uF} p`, a finite extension of Mathlib's `ℚ_p`, with its
  canonical topological data `F.canonicalTopologicalData`;
- every `ψ : UnitaryAdditiveCharacter F.Carrier` for the canonical topology.
  The structure bundles continuity, unit-circle values and nontriviality;
- every `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`,
  an additive Haar measure self-dual for `ψ`; the relation uses `ν.val`;
- every `r t : ℕ`, so the ranks `r + 1` and `t + 1` are arbitrary positive
  integers in either order, and every `V : Type uV`, `W : Type uW` in
  independent universes with their `AddCommGroup` and `Module ℂ` structures;
- every actual representation
  `π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V` and
  `σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W`;
- the hypotheses `Whittaker.IsGeneric ψ r π`, `IsUnitarizable π`,
  `Whittaker.IsGeneric ψ t σ` and `IsUnitarizable σ`, with the genericity
  predicates read in the canonical topology.

`Whittaker.IsGeneric ψ n π` is the published predicate of
`Whittaker.GeneralLinear`: `π` is irreducible, admissible (smooth, with
finite-dimensional fixed vectors for every open subgroup) and has a nonzero
linear form transforming by the standard character of `ψ` on the upper
unipotent subgroup. This is GH's "irreducible admissible generic".
`IsUnitarizable π` is the published predicate of `Unitary.Basic`: `π` admits
a positive definite Hermitian form invariant under every group element, with
no topology or completion on the carrier. This is GH's "unitary".

GH's hypothesis "generic" names no character. Their displayed integrals use
the `ψ`-Whittaker model of the first representation and the `ψ̄`-Whittaker
model of the second. These model choices are separate from the Lean
genericity hypotheses, which say that both representations are generic for
the same `ψ`, as in the published
`GenericLanglandsQuotientLFactorStatement`. This loses nothing: the published
theorem `Langlands.PadicField.TopologicalData.isGeneric_iff_character`
(module `Whittaker.PadicCharacterIndependence`) shows that, over a p-adic
field, genericity for one continuous nontrivial unitary additive character is
equivalent to genericity for any other. This is the classical change of
character by conjugation with a diagonal matrix. In particular,
`ψ`-genericity is equivalent to genericity for `ψ.scale (-1)`, whose values
are `ψ(-x) = ψ(x)⁻¹ = conj ψ(x)` (`complex_scale_neg_one`, module
`HarmonicAnalysis.RowFourierMeasure`). Since `ψ` is unitary, `ψ̄ = ψ⁻¹`.
A scratch check (not part of this module) confirmed that
`isGeneric_iff_character` applies directly to the genericity hypotheses as
written here and gives genericity for `ψ.scale (-1)`.

The p-adic restriction is a scope restriction: GH's non-Archimedean case
also contains local fields of positive characteristic, which this module does
not cover. GH fix no measure. The Library's L-polynomial relation needs an
additive Haar measure for the unequal-rank integrals, and the module uses
the self-dual normalization of the published pair-factor statements;
relations for other Haar measures are not covered.

## Conclusion

The conclusion is

```lean
∀ P : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
  ∀ s : ℂ, 1 ≤ s.re →
    P.eval ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s)) ≠ 0
```

`IsPadicSymmetricLPolynomial` is the published relation of
`PadicPairFactors`. When `t ≤ r` it is
`IsPadicPairLPolynomial F ψ ν.val π σ P`, and when `r < t` it is
`IsPadicPairLPolynomial F ψ ν.val σ π P`: the pair is read with the larger
rank first, the convention of JPSS (2.12) and of GH's display (11.19), where
`m < n`. Equal ranks are included. The relation requires that a compatible
quotient measure exists and that, for every compatible quotient measure,
`P` is the normalized generator of the zeta values of all Whittaker
functionals and coefficient-model vectors of the pair (and, in equal rank,
all Schwartz–Bruhat functions). This is GH's Proposition 11.5.1(c). The
relation uses standard `ψ`-Whittaker functionals for the first member and
functionals for `inverseStandardCharacter ψ = (standardCharacter ψ)⁻¹` for
the second. This is the JPSS convention, and it agrees with GH's: for the
unitary character `ψ` the inverse character is the conjugate `ψ̄`, which is
the character of GH's `𝒲(π′, ψ̄)`. The module uses the published relation
unchanged.

The number `q = F.canonicalTopologicalData.residueCardinality` is the residue
cardinality that the relation itself uses. Since
`L(s, π × σ) = P(q^(-s))^(-1)`, the conclusion says that `L(s, π × σ)` has no
pole for `Re(s) ≥ 1`. The "nonzero" half of GH's theorem needs no separate
clause, because the reciprocal of a complex number is never zero. In the
variable `z = q^(-s)` the condition `Re(s) ≥ 1` is `0 < ‖z‖ ≤ q^(-1)`.

## What is not asserted

- Existence of `P` is neither asserted nor assumed. For a pair with no
  polynomial satisfying the relation the conclusion holds vacuously, so this
  proposition alone does not establish the existence of `L(s, π × σ)`.
  The relation has at most one solution (`IsPadicSymmetricLPolynomial.unique`).
- The Archimedean case of GH's theorem (proved in [BR94a, §2] of GH's
  bibliography, which is not in the project literature) and the
  positive-characteristic non-Archimedean case are not covered.
- No statement is made about other definitions of the local L-factor, such
  as the Langlands-classification factor `IsLanglandsPairLPolynomial`; for
  generic pairs the published `GenericLanglandsQuotientLFactorStatement`
  compares that factor with this relation.

## Relation to published statements

- `SquareIntegrableLPolynomialNonvanishingStatement` (same directory) has the
  same conditional form for square-integrable pairs and the larger region
  `Re(s) > 0` (`‖z‖ < 1`). Neither proposition implies the other as
  stated: unitary generic representations need not be square-integrable, and
  the region `Re(s) ≥ 1` is smaller than `Re(s) > 0`.
- `UnitaryEqualRankConvergenceStatement` (module `EqualRankEulerStatement`,
  Jacquet–Shalika, Euler products I, Proposition (1.5)(i)) states the
  equal-rank half of GH's Proposition 11.5.1(a). As of Library commit
  `77763a3f` it has no proof, and no unequal-rank analogue exists.
- Global link: the published theorems `cuspidalUnitaryLocalGenericity` and
  `cuspidalUnitaryLocalUnitarity` (modules
  `Automorphic.CuspidalUnitaryLocalGenericity` and
  `Automorphic.CuspidalUnitaryLocalUnitarityProof`) show that every
  irreducible admissible finite local component of a spectral presentation of
  a cuspidal realization with unitary central character is generic for every
  nontrivial unitary additive character and unitarizable. These are the
  hypotheses of this proposition for such components. The genericity
  predicate there is read with `canonicalGeneralLinearTopology (r + 1)`; a
  scratch check (not part of this module) confirmed by `Iff.rfl` that it is
  definitionally the predicate used here.

## Intended proof route

This route is described here and is not proved in this module. It follows
GH's deduction from Proposition 11.5.1 and the implemented proof of the
square-integrable case (`SquareIntegrableLPolynomialNonvanishingProof`):

1. From the relation, take a compatible quotient measure for which `P` is the
   normalized generator of the zeta-value sets.
2. Prove absolute convergence and holomorphy of all the integrals generating
   these sets on `Re(s) ≥ 1` (GH Proposition 11.5.1(a)); in equal rank this is
   `UnitaryEqualRankConvergenceStatement` together with holomorphy, and in
   unequal rank the corresponding bound for the block integrals.
3. Use `holomorphicRationalContinuation` to obtain regularity of each
   rational continuation at the points `q^(-s)` with `Re(s) ≥ 1`.
4. Conclude with `IsNormalizedGenerator.eval_ne_zero_of_regularAt`
   (module `NormalizedGeneratorRegularityProof`).

An alternative route uses the unitary generic classification, whose
statements are published in `Classification.UnitaryGenericStatement`
(complementary-series exponents in the open interval `(-1/2, 1/2)`),
together with multiplicativity of the L-polynomial and the square-integrable
case.

## Lean checks

The module compiles with `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (diagnostic `36f9a6fb`) with no errors
or warnings. Inspection of `UnitaryGenericLPolynomialNonvanishingStatement`
reports a definition returning `Prop`, with universe parameters `uF uV uW`,
using only `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry` and no new axiom.
