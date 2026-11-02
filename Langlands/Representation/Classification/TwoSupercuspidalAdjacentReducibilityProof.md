# Reducibility of adjacent two-supercuspidal products (proof)

Authors: Worker 1023.

## Statement proved

```lean
theorem Langlands.Classification.twoSupercuspidalAdjacentProductReducible
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalAdjacentProductReducible.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.TwoSupercuspidalAdjacentProductReducible.{uF,uV} F T`
from `Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement`,
unchanged and with no further hypotheses.
For every positive rank `k` and actual supercuspidal representations `ρ, ρ'`
of `GL_k(F)` with `ρ' ≅ νρ` or `ρ ≅ νρ'`, the actual upper normalized
product `ρ × ρ'` is not irreducible. Here `ν = |det|` is
`T.determinantPowerCharacter k 1`, `ρ` occupies the first (upper left) block
and `ρ'` the second block of `Shahidi.twoBlocks k k hk hk`, and normalized
induction is the Library's (positive half-modulus covariance, right
translation), as recorded in the statement's Markdown. The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The universes `uF` (field) and `uV` (input carriers) stay independent, and
induced carriers live in `max uF uV`.

## Route

The proof follows the sketch of Zelevinsky 1980, Proposition 1.11(b),
printed p.175 / PDF p.12. The family is written as
`π_s = ν^s ρ₀ × ν^(-s) ρ₀`. The original writes `ν^(-s)ρ₀ × ν^sρ₀`, which is
the same family with `s` replaced by `-s`. Only the alternative `ρ' ≅ νρ` is
treated analytically. The other alternative reduces to it by the irreducible
product swap.

### Case `ρ' ≅ νρ`, analytic core (`unitaryHalfProduct_not_isIrreducible`)

Let `ρ₀` be an actual supercuspidal representation of `GL_k(F)` whose
representation is unitarizable. Suppose that
`π_(-1/2) = ν^(-1/2) ρ₀ × ν^(1/2) ρ₀` is irreducible, and put `J = (-∞, 0]`.

1. Irreducibility on `J`. At `s = -1/2` this is the assumption. For `s ≤ 0`
   with `s ≠ -1/2`, `member_isIrreducible` applies the published nonadjacent
   theorem `twoSupercuspidalNonadjacentProductIrreducible`
   (`TwoSupercuspidalNonadjacentProductIrreducible`) to the supercuspidal twists
   `ν^s ρ₀` and `ν^(-s) ρ₀` (`scTwist`, built with `SupercuspidalRep.twist`).
   `exponent_eq_of_class_eq` rules out both adjacency conditions. A class
   equality `[ν^a ρ₀] = [ν (ν^b ρ₀)]` gives an isomorphism
   `ν^a ρ₀ ≅ ν^(1+b) ρ₀`, hence `a = 1 + b` by the published
   `IntegralTwistFreeness.exponent_eq_zero_of_equiv`: an irreducible
   admissible representation of positive rank is not isomorphic to a
   nontrivial real determinant twist of itself. With `(a, b) = (-s, s)` this
   would force `s = -1/2`. With `(a, b) = (s, -s)` it would force
   `s = 1/2 > 0`.
2. Common carrier. The published `glParabolicCompactScalarIntegral` (at rank
   `k + k`) supplies a compact open subgroup `K` with `G = P K`, a Haar
   probability measure on `K` and the compact scalar integral. The published
   `exponentHeight` of `ExponentFamily` (exponent vector `![1, -1]`) gives a
   family `π s` of representations on the single space of smooth functions
   induced from the untwisted coefficient `δ_P^(1/2) ⊗ (ρ₀ ⊠ ρ₀)`.
   `exponentFamilyEquiv` gives an equivalence of `π s` with the actual member
   `T.twistedProductInduced B (ρ₀, ρ₀) ![s, -s]` (`member_equiv`;
   `s • ![1, -1] = ![s, -s]`).
3. The hypotheses of `unitarizabilityContinuation`
   (`UnitarizabilityContinuationStatement`) hold for this family on `J`:
   - agreement on `K`: `IwasawaHeight.family_apply_eq_of_mem`;
   - admissibility: `member_isAdmissible`. Each twisted block is admissible by
     `isAdmissible_twist_iff`, the external tensor by
     `FiniteTensor.isAdmissible_external`, and normalized induction by
     `Parabolic.normalizedInductionAdmissibility`. The result is transported
     along the equivalence with `isAdmissible_of_equiv`;
   - irreducibility: step 1, transported with `isIrreducible_iff_of_equiv`;
   - a nonzero invariant sesquilinear form on each `π s` with `s ∈ J`. The
     compact pairing `c = normalizedIntegralForm … .toInnerProductCore` is
     built from an invariant positive form on `ρ₀ ⊠ ρ₀`
     (`FiniteTensor.invariantPositiveForm`) and satisfies
     `c (π s g v) (π (-s) g w) = c v w` (`normalizedIntegralForm_family_neg`).
     Since `π_s` is irreducible, `member_swap` (the swap theorem applied to the
     irreducible blocks `ν^s ρ₀`, `ν^(-s) ρ₀`) gives `π_s ≅ π_(-s)`.
     Composing with the equivalences of step 2 yields
     `e : (π s).Equiv (π (-s))`. Then `pairingSesquilinear c e` is invariant
     (`pairingSesquilinear_invariant`) and nonzero
     (`pairingSesquilinear_ne_zero`, using that an irreducible representation
     has a nontrivial carrier, `nontrivial_of_isIrreducible`);
   - weak continuity in `s`: `IwasawaHeight.continuous_family_apply`;
   - unitarizability at `s₀ = 0`: `familyZeroForm`, the compact pairing as a
     positive invariant form for `π 0`.
4. The continuation theorem makes `π s` unitarizable at `s = -k/2 - 1 ∈ J`,
   hence the actual member too (`isUnitarizable_iff_of_equiv`). This
   contradicts `twoBlockLargeExponentNonUnitarizable`
   (`TwoBlockLargeExponentNonUnitarizable`: no member with `s < -k/2` is
   unitarizable), applied to the irreducible unitarizable `ρ₀`.

### Case `ρ' ≅ νρ`, reduction to the analytic core (`adjacentProduct_not_isIrreducible`)

Assume `ρ × ρ'` is irreducible. The published real unitarization
`supercuspidalRealUnitarization` (`SupercuspidalRealUnitarizationStatement`)
gives `t` with `ν^t ρ` unitarizable. Let `ρ₀ = ν^t ρ` and `C = ν^(1/2 - t) ρ₀`. The blocks satisfy
`ρ ≅ ν^(-1/2) C` and `ρ' ≅ ν ρ ≅ ν^(1/2) C`, because real twists compose
additively (`segmentFactorTripleIso`, `segmentFactorZeroIso`). The product
functor (`twoBlockProductIso`) therefore makes `ν^(-1/2) C × ν^(1/2) C`
irreducible. By the published `twistedProductCharacterTwist` with the scalar
character `χ = |·|^(1/2 - t)`, this product is equivalent to the `χ ∘ det`
twist of `π_(-1/2) = ν^(-1/2) ρ₀ × ν^(1/2) ρ₀`. Then `isIrreducible_twist_iff`
makes `π_(-1/2)` irreducible, contradicting the analytic core.

### Case `ρ ≅ νρ'`

If `ρ × ρ'` is irreducible, the published swap theorem
`irreducibleTwoFactorProductSwap` gives `ρ × ρ' ≅ ρ' × ρ`. So `ρ' × ρ` is
irreducible, and the previous case applied to the pair `(ρ', ρ)` gives a
contradiction.

## Helpers in this module

Besides the main theorem, the two case theorems
`unitaryHalfProduct_not_isIrreducible` and `adjacentProduct_not_isIrreducible`
described above are public. All other helpers are private.

- `segmentFactorSegmentFactorIso`, `segmentFactorZeroIso`,
  `segmentFactorTripleIso`: real determinant twists compose additively
  (`twist_twist`, `realPowerCharacter_add`), and `ν^0` is the identity. These
  are equalities of representations turned into isomorphisms.
- `exponent_eq_of_iso`, `exponent_eq_of_class_eq`: the exponent rigidity of
  step 1.
- `twoBlockProductIso`, `twistedProductInduced_twoBlocks`: the product functor
  on blockwise isomorphisms, and the twisted product of two equal blocks as the
  product of the twisted blocks.
- `scTwist`, `member_isIrreducible`, `member_swap`, `member_isAdmissible`,
  `member_equiv`, `nontrivial_of_isIrreducible`: as in steps 1–3.

## Inputs

| Input | Lean name | Status |
| --- | --- | --- |
| unitarizability continuation | `Langlands.unitarizabilityContinuation` (`Langlands.Representation.Unitary.UnitarizabilityContinuationProof`) | published (task `7071b052`, artifact `ec26db35`) |
| large-exponent non-unitarizability | `Langlands.Classification.twoBlockLargeExponentNonUnitarizable` (`Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`) | published (task `a0b83fd9`, artifact `ee4360e4`) |
| irreducible product swap | `Langlands.Classification.irreducibleTwoFactorProductSwap` | published |
| nonadjacent irreducibility | `Langlands.Classification.twoSupercuspidalNonadjacentProductIrreducible` (`Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`) | published (task `3c9849a4`, artifact `98cc1114`, Worker 745) |
| real unitarization | `Langlands.supercuspidalRealUnitarization` (`Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof`) | published (task `733b7c5a`, artifact `ad033912`) |
| exponent family and compact pairing | `exponentHeight`, `exponentFamilyEquiv`, `normalizedIntegralForm_family_neg`, `familyZeroForm`, `glParabolicCompactScalarIntegral` | published |
| twist freeness | `IntegralTwistFreeness.exponent_eq_zero_of_equiv` | published |
| character twist of products | `twistedProductCharacterTwist` | published |

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
  Ann. Sci. ENS (4) 13 (1980), Proposition 1.11 and its proof sketch, printed
  p.175 / PDF p.12. Literature ID `zelevinsky-1980-induced-ii`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), Remark 4.2(2), printed
  p.454 / PDF p.15. Literature ID `bernstein-zelevinsky-1977-induced-i`.

## Independence audit

Import closure: the module's transitive `Langlands` imports were computed by a
recursive scan of the `import` lines over Library commit
`a5dff2ff93bd3637a67ee8847f67f811efc82f01`. There are 738 modules, this module
included. Without the nonadjacent theorem the closure has 363 modules. The
other 375, mostly the derivative, mirabolic and Whittaker modules, enter only
through the published proof of `twoSupercuspidalNonadjacentProductIrreducible`.
The closure was checked against the task's Independence list as follows.

- *Excluded tasks and declarations.* No Lean file in the closure contains the
  ID of any task on the Independence list (scan for the 22 task-ID prefixes and
  for `8e5b4563`). No Lean file mentions `SegmentFullJacquetFormula`,
  `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
  `SegmentSpecialJacquetExponentNormFormula`,
  `SegmentSocleProductIrreducibility`, `MultisegmentSocleExhaustion`,
  `OrderedMultisegmentSocleExistence`, `GenericSegmentProductUniqueness`,
  `SquareIntegrableLanglandsClassification` or
  `SegmentSpecialEssentialSquareIntegrability`.
- *Segment-named modules.* The closure reaches
  `Langlands.Representation.Classification.Segments`, `Tempered`,
  `LanglandsData`, `ConstituentRelations` and `ConstituentCompatibility`. They
  contain only definitions and elementary transport lemmas: segments, linkage,
  juxtaposition, real twists, the segment socle/head predicates, segment
  product data, tempered and square-integrable predicates, and compatibility
  propositions. None of them states or proves an existence, Jacquet-formula,
  irreducibility, classification, exhaustion or square-integrability result.
  None of them is used as a premise here.
- *Jacquet and Whittaker modules.* The Jacquet modules in the closure
  (`Langlands.Representation.Jacquet.*`, `CuspidalSupport.*Jacquet*`, natural
  Jacquet duality) are the general Jacquet functor, its exactness, duality and
  cuspidal-support comparisons. They are not segment formulas.
  `CuspidalJacquetMultiplicityStatement` is a proposition definition and is
  not used as a premise. The Whittaker modules and the Gelfand–Kazhdan
  modules (`Smooth.Contragredient.GelfandKazhdan*`) come from the published
  proof of BZ77 4.4 inside the nonadjacent proof.
- *Square-integrable coefficients.* The closure contains
  `Langlands.Representation.Unitary.SquareIntegrableProof`, the general fact
  that a representation with square-integrable coefficients modulo the centre
  is unitarizable (`squareIntegrableUnimodularUnitarity`). It comes in only
  through the published `supercuspidalRealUnitarization` and the
  `leviCuspidalRealUnitarization` it specializes (supercuspidal
  representations are unitarizable after a real twist). It is not on the
  Independence list and uses no segment, Ze80 9.3 or classification result.
- *Mathematical dependencies.* The proof uses only the inputs in the table
  above. None of them is, or uses, a result of the listed tasks. The proof
  uses no segment product irreducibility criterion (Ze80 4.2 or 9.7), no
  analytic or square-integrability classification (Ze80 9.3) and no
  classification or exhaustion theorem. In particular Ze80 4.2's linked-pair
  converse is not used, so the proof is not circular with Ze80 §2. The swap
  theorem is the published `irreducibleTwoFactorProductSwap`. It proves the
  weaker consequence of Ze80 Theorem 1.9 that the sketch needs (the
  irreducible equal-rank case) with the Gelfand–Kazhdan involution, and its
  own Markdown records its audit. This module itself uses no derivative.

### Derivative route of the nonadjacent input

The Independence section forbids assuming a derivative formula (Ze80 §3.5 or
§9.6, or BZ77 derivative results). The nonadjacent theorem is proved with
Bernstein–Zelevinsky derivatives. The trusted operator's decision on request
`a8463ee15d57588c8de10306748b2538` (correspondence file
`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`,
`sender_role: operator`, reproduced in this task's context) allows a fully
proved derivative route under five conditions. They hold condition by
condition:

1. *Only BZ77's general derivative theory.* The derivative inputs in the
   closure are the derivative functors (`Derivative.Iteration`,
   `Derivative.Homogeneity`), exactness of derivatives, detection by
   derivatives, BZ77 Proposition 3.8, the Leibniz filtration BZ77 4.14(c) and
   the derivatives of supercuspidal representations BZ77 4.4. The last of
   these is proved via Whittaker multiplicity one and Gelfand–Kazhdan. The
   nonadjacent proof itself is the argument of BZ77 Theorem 4.2. No closure
   Lean file contains a segment derivative statement. In particular
   `SegmentSocleDerivatives` (Ze80 3.5) does not occur, and no Ze80 §9.6
   formula is stated or used.
2. *Every derivative result proved, accepted and published.* The exactness
   (task `44f58b77`), detection, BZ77 3.8 (task `a925b519`), BZ77 4.4 (task
   `2e5183b1`) and Leibniz (task `4e10058b`) proofs listed in the nonadjacent
   proof's Markdown are in the Library at the base commit. So is the
   nonadjacent proof itself (artifact `98cc1114`, task `3c9849a4`). This
   module uses all of them only through the theorem
   `twoSupercuspidalNonadjacentProductIrreducible`, which has no premises. No
   derivative statement is a hypothesis of any theorem here.
3. *Excluded tasks.* By the scans above, the closure contains none of
   `ed48ae06`, `b95105c6`, `55ad1e10`, `92aea10f`, `2ae5cbe5`, `8364e73f` or
   any other Independence task, nor their named declarations. Task `8e5b4563`:
   its segment-socle statements (b)–(f) (`SegmentSocleDerivatives`,
   `HighestDerivativeSupportShift`, `NonjuxtaposedSegmentSocleConstituentLevel`
   and the two later statements) and the exact rank transport `castRank` occur
   in no closure Lean file. Only its cuspidal part enters, as the proposition
   `SupercuspidalDerivatives` in its own module
   `Classification.SupercuspidalDerivativesStatement` with its separate proof
   (task `2e5183b1`). The scan of the whole closure covers that proof's
   closure too.
4. *Reuse of the derivative infrastructure.* The nonadjacent proof uses the
   published functors `Derivative.generalLinearDerivative` (task `d3e94f0f`)
   and `level` (task `dfae49d8`, `Derivative.Homogeneity`). The
   Gelfand–Kazhdan realization (`Smooth.Contragredient.GelfandKazhdanProof`,
   task `2206daa6`) enters through the proof of BZ77 4.4. No derivative
   functor is redefined, here or in the nonadjacent proof.
5. *Audit recorded.* This section records it. The nonadjacent proof's
   Markdown records the same audit for its own closure in more detail.
