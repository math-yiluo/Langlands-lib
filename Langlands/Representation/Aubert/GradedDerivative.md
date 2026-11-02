# The Bernstein–Zelevinsky derivative on the actual graded exact K0

This module constructs the total Bernstein–Zelevinsky derivative
`𝒟 : ℛ → ℛ` of Bernstein–Zelevinsky 1977, §4.5, on the published graded
exact Grothendieck group `GradedGrothendieckGroup F T = ⨁ n, K0(GL_n)`. It proves
that `𝒟` is multiplicative for the published actual induction product and fixes
the published rank-zero unit, so it is a ring endomorphism of
`gradedInductionRing F T hx hl`. It also proves Zelevinsky's two-term formula
`𝒟(⟨Δ⟩) = ⟨Δ⟩ + ⟨Δ⁻⟩` (Zelevinsky 1980, Theorem 3.5) on the published
segment-socle classes.

All declarations are in namespace `Langlands.Aubert`. The parameters are
`F : PadicField.{uF} p`, `T : F.TopologicalData` and a unitary additive character
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`. The
derivatives are the published actual functors
`Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk`, from smooth
representations of `GL_n` to smooth representations of `GL_(n-k)`, on
carriers in `Type (max uF uV)`. The coefficients are complex. The K0 groups are
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier`, the
published quotient by all actual short exact sequences. The universes `uF` and
`uV` are independent. The published type `UnitaryAdditiveCharacter` consists of
continuous nontrivial characters `F → Circle`; no further condition on `ψ` is
imposed.

## Homogeneous derivatives

- `generalLinearDerivative_preservesFiniteLength F T ψ n k hk` and
  `generalLinearDerivative_preservesShortExact F T ψ n k hk` repackage the
  published theorems `Derivative.generalLinearDerivativeFiniteLength` and
  `Derivative.generalLinearDerivativeExactness`. They are stated in the form
  required by the published `SmoothRep.FiniteLengthGrothendieckGroup.map`.
- `derivativeK0 F T ψ n k hk : K0(GL_n) →ₗ[ℤ] K0(GL_(n-k))` is that induced map.
  `derivativeK0_ofObject` and `derivativeK0_ofRepresentation` state
  `derivativeK0 [A] = [A^(k)]` for every actual finite-length `A`.
  `derivativeK0_zero` states that the order-zero map is the identity. The proof
  checks this on generators: the zeroth derivative of `A` has the same class as
  `A`, by `rfl`.
- `derivativeComponent F T ψ n k : K0(GL_n) →ₗ[ℤ] GradedGrothendieckGroup F T`
  is `gradedInclusion (n-k) ∘ derivativeK0` when `k ≤ n` and `0` otherwise.
  `derivativeComponent_of_le` and `derivativeComponent_of_lt` unfold the two cases.

## The total derivative

- `gradedDerivative F T ψ : GradedGrothendieckGroup F T →ₗ[ℤ] GradedGrothendieckGroup F T`
  is `DirectSum.toModule` of `∑ k ∈ range (n+1), derivativeComponent F T ψ n k`
  on rank `n`. This is BZ77 §4.5's `𝒟π = ∑_{k=0}^{n} π^(k)`, extended `ℤ`-linearly.
- `gradedDerivative_homogeneous n x` evaluates it on a homogeneous class.
- `gradedDerivative_ofRepresentation n A hA` states
  `𝒟 (gradedInclusion n [A]) = ∑ k : Fin (n+1), gradedInclusion (n-k) [A^(k)]`
  for every actual finite-length representation `A` of `GL_n`.

## Leibniz rule and multiplicativity

BZ77 Lemma 4.5 says that `(ρ × ω)^(k)` is glued from the representations
`ρ^(i) × ω^(k-i)`. It deduces that `𝒟` is a ring homomorphism. The Library
proves the gluing as `Derivative.generalLinearDerivativeLeibnizFiltration`: a
finite filtration of the functor `(ρ, ω) ↦ (ρ × ω)^(d)`, indexed through an
equivalence `e` by `Derivative.LeibnizIndex a b d`. The graded pieces are
naturally isomorphic to the functors `leibnizPieceFunctor F T ψ a b d x`:
derivatives of orders `x = (i, j)`, the published binary normalized product
`T.binaryNormalizedProductFunctor (a-i) (b-j)`, then the rank cast
`Derivative.generalLinearRankCast` to rank `(a+b)-d`.

- `gradedInclusion_generalLinearRankCast` and `gradedInclusion_castRank` show
  that the derivative rank cast and the classification rank cast `T.castRank`
  do not change homogeneous graded classes, for any finite-length proof. Both
  proofs substitute the rank equation and use `rfl`. The first name differs
  from the published `gradedInclusion_rankCast` of
  `GradedInductionCommutativityProof`, which is not imported here. That lemma
  fixes one particular finite-length proof.
- `leibnizPiece_class hx a b d x A B h` computes the graded class of one piece.
  It is `gradedMultiplication F T hx` applied to the two derivative components.
  The proof uses the published `binaryProductK0_classes` and
  `gradedMultiplication_homogeneous`.
- `derivativeComponent_binaryProduct hx a b d hd A B` is the K0 Leibniz formula
  for one order `d ≤ a+b`:
  `derivativeComponent (a+b) d (binaryProductK0 [A] [B])` equals the sum over
  `x ∈ Derivative.leibnizIndices a b d` of the products of the derivative
  components. The proof applies the published
  `SmoothRep.filtrationGrothendieckStatement`: the class of a functorially
  filtered object is the sum of the classes of its graded pieces. It then
  reindexes along `e.symm` with `Fintype.sum_equiv`.
- `sum_range_leibnizIndices a b f` is a finite-sum identity. Summing over the
  index sets `leibnizIndices a b d` for `d ∈ range (a+b+1)` gives the rectangle
  `range (a+1) × range (b+1)`.
- `gradedDerivative_mul_homogeneous hx a b x y` and `gradedDerivative_mul hx x y`
  state `𝒟 (x · y) = 𝒟 x · 𝒟 y` for the published `gradedMultiplication F T hx`.
  The homogeneous case is reduced to generators by the published
  `GradedAssociativityProof.induction_on`, and the general case to homogeneous
  classes by `GradedAssociativityProof.graded_induction`. On generators the proof
  combines the per-order Leibniz formula, the rectangle identity and
  `Finset.sum_comm`.
- `gradedDerivative_unit` states `𝒟 (gradedUnit F T) = gradedUnit F T`. The
  rank-zero unit has only the zeroth derivative.
- `gradedDerivativeRingHom F T ψ hx hl` is `𝒟` as a ring homomorphism of
  `gradedInductionRing F T hx hl`, for any `hx : BinaryProductExactnessStatement F T`
  and `hl : GradedInductionRingLawsStatement F T hx`. Here `hx` and `hl` are only
  the parameters of the published ring structure. Multiplicativity and the unit
  law do not use `hl`. `gradedDerivativeRingHom_apply` states that its
  underlying function is `gradedDerivative F T ψ`, by `rfl`.

## Segment socles

`gradedSegmentSocle F T Δ` is the published graded class of the published
segment socle `⟨Δ⟩`. For a segment `Δ`, `Δ.degree = Δ.length * Δ.rank`.

- `gradedInclusion_eq_gradedUnit hm V hV h1`: for `m = 0`, every actual
  representation of `GL_m` with `finrank = 1` has the graded class
  `gradedUnit F T`. The group `GL_0` is trivial (published
  `GeneralLinear.subsingleton_of_rank_eq_zero`). A linear equivalence with the
  published unit `T.binaryProductUnit` (`T.finrank_binaryProductUnit`) is
  therefore an equivalence of representations. The proof then applies the
  published `ofRepresentation_eq_of_equiv`.
- `derivativeComponent_segmentSocle_eq_zero Δ k hk hpos hne`: for
  `0 < k ≤ Δ.degree` with `k ≠ Δ.rank`, the order-`k` component of the segment
  socle class is zero. The derivative is subsingleton by the first clause of the
  published `Classification.segmentSocleDerivatives`. Its class is zero by the
  published `SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton`.
- `gradedDerivative_segmentSocle_of_length_eq_one Δ h`: if `Δ.length = 1`, then
  `𝒟 (gradedSegmentSocle Δ) = gradedSegmentSocle Δ + gradedUnit F T`.
- `gradedDerivative_segmentSocle_of_two_le Δ h`: if `2 ≤ Δ.length`, then
  `𝒟 (gradedSegmentSocle Δ) = gradedSegmentSocle Δ + gradedSegmentSocle ⟨Δ.base, Δ.length - 1, _⟩`.

In both formulas the sum over orders keeps only `k = 0` and `k = Δ.rank`
(`Finset.sum_eq_add_of_mem`). The order-zero term is the class itself, by
`derivativeK0_zero`. The order-`Δ.rank` term uses the second or third clause of
`Classification.segmentSocleDerivatives`. For length one, the derivative is
one-dimensional on `GL_0`, so its class is the unit. For length at least two,
the transported derivative `T.castRank hdeg (⟨Δ⟩^(Δ.rank))` is a segment socle
of the shortened segment. The proof identifies its class with the published
chosen class by `segmentSocleClass_of_object` and removes the rank cast by
`gradedInclusion_castRank`. The shortened segment has the same base and one
position fewer. This is Zelevinsky's `Δ⁻ = Δ ∖ {ρ'}` for `Δ = [ρ, ρ']`, with
`⟨∅⟩ = 1` in the length-one case.

## Provenance and scope

This is a derived construction. The total derivative and its multiplicativity
are BZ77 §4.5 (printed p.455, one-based PDF page 16), and the result there is
stated as Lemma 4.5 together with its ring-homomorphism reformulation. The
segment formula is Zelevinsky 1980, Theorem 3.5 (printed p.182, one-based PDF
page 19): `𝒟(⟨Δ⟩) = ⟨Δ⟩ + ⟨Δ⁻⟩`. The Lean development is formulated on
the Library's actual graded exact K0 and its actual induction product. It uses
only published proved theorems: derivative exactness, finite length and the
Leibniz filtration, the filtration class formula, the binary product class
formulas, the graded induction principles, the subsingleton-class lemma, and
`Classification.segmentSocleDerivatives`. It uses no unproved statement
parameter beyond the published ring parameters `hx` and `hl`.

No classification result is asserted or used here, and no injectivity or
surjectivity of `segmentPolynomialEvaluation` is proved. The module is an
internal ingredient for the proof of `SegmentPolynomialComparisonStatement`.
