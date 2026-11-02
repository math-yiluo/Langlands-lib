# Derivatives of segment socles (Zelevinsky 1980, Theorem 3.5)

Author: Worker 818, for proof task 209027ca-f49c-472a-af2a-f2fc0006950e (revision 1).

This module proves the published proposition
`Langlands.Classification.SegmentSocleDerivatives.{uF, uV} F T`, statement (b) of
`Langlands.Representation.Classification.SegmentSocleDerivativesStatement`
(statement task 8e5b4563-0365-41c7-b134-70f2a0b36292, statement artifact
c27c6879-9906-43fa-8d88-cf1808b55f2d). The statement module and everything it imports
are unchanged.

## The theorem

```lean
theorem Langlands.Classification.segmentSocleDerivatives
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSocleDerivatives.{uF, uV} F T
```

There is no other premise. The outer telescope is the target's own:
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`. The proof
installs the supplied topology `T.topology` and never substitutes another one. The
field universe `uF` and the segment universe `uV` are independent; the level
parameters of the theorem are exactly `[uF, uV]`. All representations in the
statement and the proof have carriers in `Type (max uF uV)`. The supercuspidal
representatives of the segment data have carriers in `Type uV`, as in
`IsSegmentSocle`.

Unfolded, the theorem says: for every continuous nontrivial unitary additive character
`ψ` (quantified, not assumed to exist), every segment `Δ` and every `π` with
`T.IsSegmentSocle Δ π`, writing `n = Δ.degree`, `r = Δ.rank`, `m = Δ.length`, and `D_k`
for the published `Derivative.generalLinearDerivative T ψ n k hk`:

1. `D_k π` is `Subsingleton` for every `0 < k ≤ n` with `k ≠ r`;
2. if `m = 1`, then `Module.finrank ℂ (D_r π) = 1`;
3. if `m ≥ 2`, then for every proof `hdeg : n - r = (m - 1) * r`,
   `T.IsSegmentSocle ⟨Δ.base, m - 1, _⟩ (T.castRank hdeg (D_r π))`, so the order-`r`
   derivative is a socle of `Δ⁻`, the segment with the same beginning and one
   element fewer.

The rank-bound and rank-equality proofs and every `finrank` conjunct are kept exactly
as in the statement. The derivative functors are the published ones, with their
determinant inverse-half normalization (`Derivative.Iteration`).

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
  irreducible representations of GL(n)* (1980), literature ID
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. Printed page =
  zero-based PDF index + 164. Used: Proposition 3.4 (pp.181–182), Theorem 3.5 (p.182),
  Proposition 3.7 (p.182), 3.8–3.10 (p.183).
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups I* (1977), literature ID `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Printed page =
  zero-based PDF index + 440. Used: 4.4 (p.454), Lemma 4.5 and Corollary 4.6 (p.455,
  proved in 4.14, p.458), Lemma 4.7 (p.455).

No errata for either source are registered in the project literature index or the
public notes.

### The source argument

Ze80 3.10 derives Theorem 3.5 from three ingredients:

- **3.7–3.8.** The order-`k` derivative is the partial derivative of the Jacquet
  module along `(n - k, k)`. On `σ ⊗ τ` this is `σ ⊗ τ^(top)`.
- **3.4.** The Jacquet module of `⟨Δ⟩` along `(l, n - l)` vanishes unless `r ∣ l`. Along
  `(q r, (m - q) r)` it is `⟨Δ_initial⟩ ⊗ ⟨Δ_terminal⟩`.
- **3.9.** The top derivative of `⟨Δ⟩` vanishes when `m ≥ 2`. The proof of 3.9 treats
  `m = 2` with BZ77 4.7(b) and the Leibniz rule BZ77 4.5. For `m ≥ 3` it embeds `⟨Δ⟩`
  into a product with a factor whose top derivative vanishes.

The implemented proof follows this route. It differs from the source in three places,
all described below:

- It works with actual representations and actual isomorphisms, not with the
  Grothendieck-group identity 3.8.
- For `m ≥ 3` it obtains the embedding by Frobenius reciprocity from 3.4 at `q = 1`,
  not from socle uniqueness.
- For `m = 2` it applies BZ77 4.7(b) to the quotient of `ρ × νρ` by `⟨Δ⟩`. It embeds that
  quotient in `νρ × ρ` by Frobenius reciprocity.

## The implemented proof

All helper declarations are in namespace
`Langlands.Classification.SegmentSocleDerivativesProof`. The final theorem is in
`Langlands.Classification`.

### Rank and order transports (section `Casts`)

The derivative `D_k` lands in `GL_(n-k)`. Comparisons with the shorter segments need the
published rank transports `Derivative.generalLinearRankCast` and
`T.castRank`. The lemmas `subsingleton_rankCast_iff`,
`subsingleton_derivative_order_iff` and `subsingleton_topDerivative_iff` show, by `subst`
on the rank or order equality, that these transports and a change of the proof of `k ≤ n`
do not change the carrier. `tensor_subsingleton`: a tensor product with a zero factor
is zero.

### Derivatives from two-block Jacquet modules (section `TwoBlock`, Ze80 3.7)

Fix `a, b > 0` with `a + b = N`. The Jacquet module of `π` along
`BlockShape.ofPair a b` is the shape that the socle Jacquet formula uses. After `subst`
on `a + b = N`, this shape is definitionally `Shahidi.twoBlocks a b`.

- `subsingleton_derivative_of_jacquet`: if that Jacquet module is zero, then `D_b π` is
  zero. The published Ze80 3.7(b), `Derivative.partialDerivativeJacquetComparison`,
  identifies `D_b π`, rank-cast to `GL_a`, with the partial derivative of the Jacquet
  module. That partial derivative is a quotient of a zero space
  (`partialDerivativeMk_surjective`).
- `nonempty_derivative_equiv`: if the Jacquet module is isomorphic to the external tensor
  product of `A` (on `GL_a`) and `B` (on `GL_b`), then the rank-cast `D_b π` is
  equivalent to `A ⊗ B^(top)` with `GL_a` acting on `A`. The proof combines 3.7(b) with
  the published Ze80 3.7(a), `Derivative.partialDerivativeTensor`. It also uses two
  published helpers from `Classification.TwoSupercuspidalPartialDerivatives`:
  `nonempty_twoBlockTensor_equiv` identifies the Levi tensor with the binary exterior
  tensor, and `nonempty_partialDerivative_equiv` lets the partial derivative transport
  equivalences. This generalizes that module's `derivative_of_twoBlockJacquet` from a
  supercuspidal second factor to an arbitrary one.
- `subsingleton_derivative_of_jacquet_tensor` (`B^(top) = 0` gives `D_b π = 0`) and
  `nonempty_derivative_equiv_first` (`finrank B^(top) = 1` gives `D_b π ≃ A`, by the
  published `nonempty_firstFactor_equiv`).

### The top derivative of a binary product (section `TopProduct`, BZ77 4.5/4.14)

The published all-rank Leibniz filtration
(`Derivative.generalLinearDerivativeLeibnizFiltration`) at order `a + b` has exactly one
grade, `(a, b)` (`leibnizIndices_top`).

- `nonempty_graded_equiv_of_length_one`: the only graded piece of a length-one filtration
  is linearly equivalent to the source.
- `nonempty_binaryProduct_rank_zero_equiv`: a binary product with a rank-zero second factor
  is the tensor product of the factors (`ZeroRankTensor.binaryRightZeroEquiv`).
- `subsingleton_top_binaryProduct`: the top derivative of `D × P` vanishes if that of `P`
  does.

### Embedding by Frobenius reciprocity (section `Embedding`)

- `exists_injective_of_jacquet_equiv`: if `π` is irreducible and its normalized Jacquet
  module along `B` is equivalent to a nonzero Levi representation `σ`, then `π` embeds in
  the normalized induction of `σ`. The map is the inverse of the published first
  adjointness `Parabolic.FirstAdjointness.equiv` (Casselman, Proposition III.3.5),
  applied to the equivalence. It is nonzero, hence injective by irreducibility.
  `exists_injective_of_jacquet_iso` is the same statement for a Jacquet isomorphism with
  an external tensor product of nonzero factors.
- `nonempty_ofPairProductIso`: the normalized product on `BlockShape.ofPair a b` of
  `(A, B)` is isomorphic to the published binary product
  `T.binaryNormalizedProductFunctor a b`. The two shapes agree up to a pointwise
  equality of block sizes; the published `T.normalizedProductRankCastIso` handles this.
- `subsingleton_top_of_jacquet`: let `π` be irreducible with Jacquet module `A ⊗ B` along
  `(a, b)`, with `A, B ≠ 0` and `B^(top) = 0`. Then `π^(top) = 0`. Indeed `π` embeds in
  `A × B`, the top derivative is exact (published `generalLinearDerivativeExactness`),
  and `(A × B)^(top) = 0`.

### Segment socles (section `Socles`)

- `isIrreducibleSocle_of_targetEquiv` and `isSegmentSocle_of_equiv`: the strong socle
  relation is transported along an equivalence of the socle.
  `isIrreducible_of_isSegmentSocle`: a socle is irreducible.
- `supercuspidal_of_isSegmentSocle_length_one` and `exists_equiv_castRank_of_length_one`:
  let `π` be a socle of a one-term segment, and `A` its supercuspidal representative. The
  socle embedding into the one-block induction, composed with the published
  `singletonSegmentInducedEquiv`, is a nonzero map into the irreducible rank transport of
  `A`. So it is an equivalence: `π ≃ castRank A`, and `π` is irreducible and
  supercuspidal (`GeneralLinear.isSupercuspidal_of_equiv`).
- `supercuspidal_derivatives_of`: the published proof of statement (a),
  `Classification.supercuspidalDerivatives`, in an arbitrary positive rank.
  `finrank_topDerivative_of_length_one`: the top derivative of a one-term socle is a line.
- `finrank_derivative_order_eq` and `castRank_derivative_eq`: order and rank transport
  identities, proved by `subst`.

### Lemma 3.9 (sections `TopVanishing`, `BaseTools`, `BaseCase`, `Assembly`)

Statement (`top_subsingleton`): if `T.IsSegmentSocle Δ π` and `2 ≤ Δ.length`, then the
top derivative `D_n π` vanishes.

**Induction on the length (`top_subsingleton_of_base`).** For `Δ` of length `m + 3`,
the published socle Jacquet formula (Ze80 3.4, `segmentSocleJacquetFormula`) at `q = 1`
gives socles `π₁` of `[ρ]` and `π₂` of `[νρ, ν^(m+2) ρ]`. It also gives an isomorphism
of the Jacquet module of `π` along `(r, (m+2) r)` with `π₁ ⊗ π₂`. By induction, `π₂`
has zero top derivative, and `subsingleton_top_of_jacquet` concludes. This replaces the
source's embedding `⟨Δ⟩ ⊂ ⟨Δ'⟩ × ⟨Δ''⟩`, which uses socle uniqueness.

**Length two (`top_subsingleton_length_two`).** This is the case that needs BZ77 4.7(b).

- `top_subsingleton_length_two` takes the Jacquet formula at `q = 1`. The two singleton
  socles are equivalent to rank transports of supercuspidal representatives `A₁` of `ρ`
  and `A₂` of `νρ`, with `A₂.isoClass = T.supercuspidalClassRealPowerTwist r 1 A₁.isoClass`.
  The factorwise equivalences are tensored by `blockTensorEquiv`.
- `top_subsingleton_of_jacquet_pair` removes the rank transports by `subst`.
- The core lemma `top_subsingleton_core` assumes that `π` is irreducible and that its
  Jacquet module along `twoBlocks k k` is equivalent to `A₁ ⊗ A₂`. It proves that
  `π^(top) = 0` by contradiction, in two steps.

1. `exists_quotient_of_nontrivial_top`. Frobenius reciprocity embeds `π` in
   `P = A₁ × A₂`; let `S` be its image.
   - `S ≠ ⊥`, and `S ≠ ⊤` because `P` is reducible (published
     `twoSupercuspidalAdjacentProductReducible`, Ze80 1.11).
   - The top derivative of `P` is a line (`finrank_top_twoBlocks`: the Leibniz top grade
     and statement (a)).
   - If `π^(top) ≠ 0`, exactness of the top derivative forces the top derivative of
     `Q = P / S` to vanish (`subsingleton_top_quotient`).
2. `false_of_quotient` and `false_of_highest_derivative`. For `Q`:
   - The published Ze80 1.11 package `twoSupercuspidalProductStructure` gives that `Q`
     is irreducible with Jacquet module `A₂ ⊗ A₁`. Frobenius reciprocity therefore embeds
     `Q` in `A₂ × A₁`, written as the actual cuspidal product
     `T.cuspidalProductInduced (pairData …) … (pairReps …)` (`cuspidalProductInduced_pairData`).
   - The published `twoSupercuspidalAdjacentProductMiddleDerivatives` gives
     `Q^(k) ≃ A₂` after rank transport.
   - For `k < j < 2k`, `P^(j) = 0`: every Leibniz grade contains a supercuspidal
     derivative of order strictly between `0` and `k`
     (`subsingleton_middle_derivative_binary`, `subsingleton_of_graded`, `subsingleton_binary`).
     So `Q^(j) = 0` as a quotient (`subsingleton_derivative_quotient`).
   - With `Q^(2k) = 0` from step 1, the restriction `W` of `Q` to the mirabolic subgroup
     `P_(2k)` has `level W = k`. This uses the published `level_eq_iff` and the
     restriction bridge `generalLinearDerivative_obj_eq_restriction`.
   - `σ = Q^(k)` is irreducible, and `isSupercuspidalSupport_singleton` shows that its
     supercuspidal support is `{[A₂]}`. The one-block product is identified with `A₂` by
     the published `singleBlockNormalizedProductEquiv` and `castRankEquiv`.
   - The published BZ77 Lemma 4.7(b), `cuspidalProductMirabolicSupportShift`, then gives
     `ν[A₂] ∈ {[A₂], [A₁]}`. Both are impossible by `twist_ne_self`: `ν[A₂] = [A₂]`, and
     `ν[A₂] = ν²[A₁] = [A₁]`. `twist_ne_self` says that no nonzero real power of `ν`
     fixes a cuspidal datum; it rests on the published central-character lemma
     `OrderedCuspidalProductTwistOne.exponent_eq_zero`.

To avoid expensive definitional unfolding between the two presentations
`(k' + 1 + k') + 1` and `(k' + 1) + (k' + 1)` of the rank `2k`, the proof rewrites with
the `rfl` lemma `derivative_obj_rank_congr`. It also uses the top-level definitions
`pairReps` and `pairData` instead of local `let` data.

### The three conjuncts (`segmentSocleDerivatives`)

**Conjunct 1** (`0 < k ≤ n`, `k ≠ r`). There are three cases.

- **`k = n`.** Then `m ≥ 2`, since otherwise `n = r`. Lemma 3.9 applies.
- **`k < n` and `r ∤ k`.** Put `l = n - k`. Then `r ∤ l`, because `r ∣ n`. The first
  conjunct of the socle Jacquet formula gives a zero Jacquet module along `(l, n - l)`.
  `subsingleton_derivative_of_jacquet` and an order transport `n - l = k` conclude.
- **`k = r j` with `2 ≤ j < m`.** The formula at `q = m - j` gives `π₁ ⊗ π₂`, where `π₂` is
  a socle of the terminal segment of length `j ≥ 2`. Its top derivative vanishes by
  Lemma 3.9, and `subsingleton_derivative_of_jacquet_tensor` concludes.

**Conjunct 2** (`m = 1`). `π` is irreducible and supercuspidal on `GL_(1·r)`. Statement
(a) gives top `finrank` one, transported from order `n` to order `r = n`.

**Conjunct 3** (`m ≥ 2`). The formula at `q = m - 1` gives `π₁ ⊗ π₂`.

- `π₁` is a socle of the initial segment `⟨Δ.base, m - 1, _⟩`. This is definitionally the
  target's `⟨Δ.base, Δ.length - 1, _⟩`; the positivity proofs agree by proof irrelevance.
- `π₂` is a socle of the one-term terminal segment `[ν^(m-1) ρ]`, whose top derivative
  is a line.
- `nonempty_derivative_equiv_first` gives `D_r π ≃ π₁` after rank transport.
  `castRank_derivative_eq` identifies the target's `T.castRank hdeg (D_r π)` with that
  transport, for the target's own `hdeg`.
- `isSegmentSocle_of_equiv` transports the socle relation.

### Normalization

The proof uses the published derivative, partial-derivative, Jacquet and induction
functors as they are, with their determinant normalizations. It never compares a Haar
modulus `mod_U` with `|det|` itself. The modulus comparison of tasks a622f240/f947a735
(`Group.GL.MirabolicModulusStatement` and `MirabolicModulusProof`) enters the closure only
inside published inputs that use it: the Leibniz filtration proof, the socle Jacquet
proof and the two-supercuspidal structure proof. All normalizations are therefore those
of independently accepted proofs.

## Published inputs (direct imports)

| Module | Content | Introducing artifact / task |
| --- | --- | --- |
| `Classification.SegmentSocleDerivativesStatement` | target statement | c27c6879 / 8e5b4563 |
| `Classification.SegmentSocleJacquetProof` | Ze80 3.4 (required `socle_jacquet`) | dbcb1209 / b95105c6 |
| `Classification.SupercuspidalDerivativesProof` | statement (a), BZ77 4.4 (required `supercuspidal_derivatives`) | fd42c8ef / 2e5183b1 |
| `Classification.TwoSupercuspidalPartialDerivatives` | tensor/partial-derivative helpers, middle derivatives of adjacent products | 80bf7d22 / a4ce78f2 |
| `Derivative.GeneralLinearDerivativeExactnessProof` | exactness of the derivatives | 79bbad40 / 44f58b77 |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | BZ77 4.5/4.14 Leibniz filtration | c4c5439d / 4e10058b |
| `Derivative.ZeroRankTensor` | rank-zero binary products | 2057375a / 3231134e |
| `Derivative.LevelCalculus` | short-exact and level lemmas | e85cf101 / b711af72 |
| `Parabolic.NaturalFirstAdjointness` | normalized first adjointness | bundled in ec16d6b6 / eb76bbde |
| `Classification.CuspidalProductMirabolicSupportShiftProof` | BZ77 4.7(b), mirabolic form | 4b8c7a7c / 0b3bf4c1 |
| `Classification.TwoSupercuspidalProductStructureProof` | Ze80 1.11 | f10f67f3 / ab61f565 |
| `Classification.TwoSupercuspidalDerivativeBridge` | GL derivative = mirabolic derivative of restriction | bundled in 98cc1114 / 3c9849a4 |
| `Derivative.OrderedCuspidalProductTwistOne` | `exponent_eq_zero` (central character) | bundled in bfc08f82 / 451717b1 |

These modules are reached transitively:

| Module | Content | Introducing artifact / task |
| --- | --- | --- |
| `Derivative.PartialDerivativeJacquetComparisonProof` | Ze80 3.7(b) | 998f43e6 / a4119dcc |
| `Derivative.PartialDerivativeTensorProof` | Ze80 3.7(a) | 96b73e12 / e339f766 |
| `Classification.TwoSupercuspidalAdjacentReducibilityProof` | Ze80 1.11(b) reducibility | 5d030a71 / 0988a3e0 |

Mathlib: `Mathlib.LinearAlgebra.PiTensorProduct.Basis`, `Mathlib.LinearAlgebra.Basis.VectorSpace`.

## Independence audit

### Rulings and closure

The proof uses neither the (c) theorem `highestDerivativeSupportShift` (proof 61c4254f)
nor any later unit (f), (d), (e). The operator ruled on the BZ77 4.7(b) input in response
**10df3136f50c5901b1061d52c6b92e07**. This proof may import
`cuspidalProductMirabolicSupportShift` (BZ77 4.7(b), proof task 0b3bf4c1) with its
published closure, including bf38b454, for the length-two case of Ze80 3.9. Per that
response, the definition-only modules listed below are infrastructure in the sense of
response 2b34e4035a5b5dafad7ad84d5a8c0dd8 and may remain.

The audit was run at Library commit `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`:

- The import closure of the module (all `Langlands` modules) has 1176 modules. 1158 of
  them belong to published artifacts; their owning tasks number 920.
- The 18 modules without an artifact manifest are infrastructure modules relocated in the
  Library: `Group.GL.{BlockScalarCenter, OneBlockShape, RankReindex, ReindexCongr,
  Transvection}`, `HarmonicAnalysis.{FiniteProductMeasureScaling, PadicLatticeTopology}`,
  `Representation.Compact.OrbitMeanTranslation`,
  `Representation.CuspidalSupport.WholeLeviTransport`,
  `Representation.Derivative.{MirabolicDeterminant, ShortExactFunctorLaws}`,
  `Representation.Geometric.CoarseLeviReversal`, `Representation.OrbitSpan`,
  `Representation.Parabolic.{InducedMapSurjectivity, OppositeJacquetMap}`,
  `Representation.Smooth.Transfer.GroupEquivalence`, `Representation.Tensor.OneFactor`,
  `Topology.CompactNormCharacter`.
- Following contract requirements transitively from the 920 owning tasks gives 924 tasks.

These were compared with all 25 excluded task IDs of this task, the two proof successors
0c90f7e4 and ba6ec030 of 7ff2a1e9, and the later units f81d9b36 (c), 4e152d19 (f),
60b25b28 (d) and 6c126713 (e). The only modules owned by those tasks are:

| Module | Artifact (kind) | Owner task | How it is reached |
| --- | --- | --- | --- |
| `Classification.TrivialGroupQuotient` | 1e56ed7e (definition) | 20e4e1c6 | target statement chain |
| `Classification.SegmentProductPermutation` | 0095a4c4 (definition) | 8252833d | target statement chain |
| `Classification.OrderedMultisegmentHeadReduction` | 6529dc85 (definition) | ebea9a8a | target statement chain |
| `Classification.SegmentSocleProductData` | 29cea4fd (definition) | f3a69bc8 | target statement chain |
| `Classification.SingletonSegmentSocle` | 8aac8ad9 (definition) | f3a69bc8 | target statement chain |
| `Combinatorics.RelationInversions` | 9e971abc (definition) | f3a69bc8 | required inputs SegmentSocleJacquetProof and SupercuspidalDerivativesProof; also TwoSupercuspidalPartialDerivatives and TwoSupercuspidalProductStructureProof |
| `Filtration.ObjectTransport` | 68054cb0 (definition) | f3a69bc8 | required input SegmentSocleJacquetProof; also TwoSupercuspidalProductStructureProof |
| `Classification.CuspidalProductDerivativeQuotientSupport` | bf38b454 (definition, quotient form of BZ77 4.7(a)) | f81d9b36 | CuspidalProductMirabolicSupportShiftProof (approved in 10df3136) |

Each of these is a definition artifact. None proves an excluded statement or a later
unit, and none imports the (c) theorem. The target statement chain is
`SegmentSocleDerivativesStatement ← SingletonSegmentSocle ← SegmentSocleProductData ←
OrderedMultisegmentHeadReduction`, plus `TrivialGroupQuotient` and
`SegmentProductPermutation` below it. That chain also reaches the statement module
`Classification.MultisegmentClassificationStatement` (statement artifact 0baefc8e, task
f72fff19). It mentions `OrderedMultisegmentSocleExistence` and
`SquareIntegrableLanglandsClassification` only as proposition definitions. No closure
module proves any of the excluded propositions.

An identifier scan of all 1176 closure Lean files looked for every excluded declaration
name and the later-unit names `HighestDerivativeSupportShift`,
`SegmentSocleProductHighestDerivative`, `NonjuxtaposedSegmentSocleConstituentLevel` and
`NonjuxtaposedSegmentSocleDerivativeStrictMono`. It finds them only in two statement
modules: the target module `SegmentSocleDerivativesStatement` (its own Prop definitions
of the later units) and `MultisegmentClassificationStatement`. The modules
`HighestDerivativeSupportShiftProof`, `HighestDerivativeSupportShiftBoundary`,
`TwoSupercuspidalTopDerivatives`, `SegmentHeadTopDerivative`, `TopProduct`,
`FiniteTopLine`, `UniformJacquetVanishing`, `NondivisibleDerivativeVanishing`,
`SegmentSocleDecreasingHead`, `IrreducibleCompositionFactors` and
`OrderedCuspidalProductNondegeneracyProof` are not in the closure.

### Exclusion table

| Excluded item | Status |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, task 23e98d90 | absent |
| `LinkedSegmentSocleReverseProductStructure`, task a55c4267 | absent |
| `LinkedSegmentSoclePairReducible`, task 8fa9f68b | absent |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, task 7ff2a1e9 and proof successors 0c90f7e4, ba6ec030 | absent |
| `SegmentSocleProductIrreducibility`, task 2ae5cbe5 | absent |
| `AdjacentUnlinkedSegmentSocleSwap`, tasks e3634665, cded83f3 | absent |
| `TwoSegmentSocleCommutation`, tasks 426911b4, 66e3b87c | absent |
| `LinkedSegmentSocleGluing`, tasks c84cd52c, 6780b79c | absent |
| `OrderedMultisegmentSocleExistence`, task 23189526 | absent (named only in the statement module `MultisegmentClassificationStatement`) |
| socle exhaustion f3a69bc8 | definition modules only, listed above |
| segment analytic classification aca8805b | absent |
| special-head multisegment exhaustion 3bfb61fa | absent |
| ordered special-head existence ebea9a8a | definition module `OrderedMultisegmentHeadReduction` only (target chain) |
| quotient coverage 20e4e1c6 | definition module `TrivialGroupQuotient` only (target chain) |
| ordered conversion 8252833d | definition module `SegmentProductPermutation` only (target chain) |
| tempered block uniqueness 52e97845 | absent |
| `GenericSegmentProductUniqueness`, task 30341ae4 | absent |
| `SquareIntegrableLanglandsClassification`, task 1cb45da2 | absent (named only in `MultisegmentClassificationStatement`) |
| square-integrable exhaustion cd8ab97c | absent |
| regular exhaustion bf433f0a | absent |
| forward special-segment essential square-integrability 5eece9e8 | absent |
| `SegmentHeadProductIrreducibility`, task 8364e73f, and its conclusions | absent (no `TopProduct`, `FiniteTopLine`, `TopLine` or `SegmentHead…` derivative module) |
| later units (c) f81d9b36, (f) 4e152d19, (d) 60b25b28, (e) 6c126713 | (c) theorem absent; only the approved definition bf38b454; (f), (d), (e) absent |

The audit tools and their outputs (closure list, owner map, requirement-graph trace) are
private records of the author. The claims above can be reproduced from the Library tree
and the published artifact manifests.

## Adapted code

A few short helpers adapt published Library code:

- `blockTensorEquiv` is the private `blockTensorEquiv` of
  `CuspidalSupport.LeviTensorFactorizationProof` (Worker 82).
- `nontrivial_piTensorProduct` follows `Tensor.ExternalSubquotient`.
- `subsingleton_binary` follows `Derivative.ProductVanishing.subsingleton_binary`.
- `twist_ne_self` generalizes `OrderedCuspidalProductTwistOne.twist_one_ne_self` (proof by
  Worker 1168) from `ν` to `ν^s`, `s ≠ 0`.
- The length-one filtration and binary-product top-derivative lemmas follow the author's
  `Derivative.OrderedCuspidalProductNondegeneracyProof`.

No reused draft or unpublished code is included.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with the declaration
`Langlands.Classification.segmentSocleDerivatives`: Lake build with 0 errors and 0
warnings; axioms `propext`, `Classical.choice`, `Quot.sound`; level parameters
`[uF, uV]` (diagnostic aa489941, at Library base `0ebc0efd`). No `sorry`, `admit` or
new axiom.
