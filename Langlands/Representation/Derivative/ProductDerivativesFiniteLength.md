# Finite length of the derivatives of products of supercuspidal representations

Author: Worker 237.

This helper module serves the proof of
`Langlands.Derivative.GeneralLinearDerivativeFiniteLengthStatement` (task
`2306027f-f763-44b8-89d1-6311d80d5204`). Its main theorem is

```
theorem Langlands.Derivative.productDerivativesFiniteLength
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (hn : 0 < n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hσ : letI := T.topology; ∀ i, (σ i).IsIrreducible ∧
      GeneralLinear.IsSupercuspidal (σ i).representation)
    (k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    ((generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
      ((T.normalizedProductInductionFunctor B).obj σ)).HasFiniteLength
```

The level parameters are `uF, uV`. The theorem says this: let `B` be a block shape
of positive total rank `n`, and let every factor `σ i` be an irreducible
supercuspidal smooth representation with carrier in `Type (max uF uV)`. Then every
actual derivative of order `k ≤ n` of the published normalized product
`(T.normalizedProductInductionFunctor B).obj σ` has finite length over the complex
group algebra of `GL_(n-k)`. The functor is the published `generalLinearDerivative`,
with codomain `GeneralLinear (n - k)`.

The carrier universe is `max uF uV`, because normalized products of factors in
`Type uV` live in `Type (max uF uV)`. Over carriers in `Type (max uF uV)` the product
universe `max uF (max uF uV)` reduces to `max uF uV`. So the product's derivative is
again one at carrier universe `max uF uV`. The universe comparison back to the
target's `uV` is not done here. It is part of the final proof module.

The theorem is a step of the proof, not the target statement. It adds no premise to
the target, and it does not claim finite length of derivatives of arbitrary
finite-length representations.

## Implemented proof

All helpers are in the namespace
`Langlands.Derivative.ProductDerivativesFiniteLength`.

### Generic finite-length facts

Here `IsFiniteLength k[G] ρ.asModule` is finite length of the module over the group
algebra.

- `isFiniteLength_of_equiv`: transfer along an actual equivalence of
  representations, using the published `repAsModuleEquiv`.
- `isFiniteLength_of_finiteDimensional`: a finite-dimensional representation has
  finite length, since it is Noetherian and Artinian by the scalar tower.
- `finiteDimensional_of_isFiniteLength`: for a finite group, finite length implies
  finite dimension, since the group algebra is a finite `k`-algebra.
- `isFiniteLength_comp`: precomposing with a surjective group homomorphism keeps
  the subrepresentation lattice. It therefore keeps the length, by Krull dimension
  of isomorphic orders.
- `isFiniteLength_secondFactor`, `isFiniteLength_firstFactor`: let `V` be
  finite-dimensional and `σ` of finite length. Then `V ⊗ σ`, with the group acting
  on the second factor, has finite length. It is the image of `σ^(dim V)` under
  `w ↦ ∑ bᵢ ⊗ wᵢ`. The first-factor version follows by the tensor swap.
- `isFiniteLength_of_filtration`: for a finite actual functor filtration
  `RepFunctorFiltration M n`, finite length of every graded value at `X` implies
  finite length of `M.obj X`. The proof applies the published
  `repLength_eq_sum_of_filtration` to the object filtration
  `ObjectRepFiltration.ofSubrepresentations`, then uses `ENat.sum_ne_top`.

### Smooth representations

1. **Transport.** `hasFiniteLength_of_iso` transfers finite length along an
   isomorphism of smooth representations. `hasFiniteLength_rankCast` does the same
   for `generalLinearRankCast`, by `subst`. `derivatives_of_iso` and
   `derivatives_transport` transfer the property "all derivatives have finite
   length" along an isomorphism (by `Functor.mapIso`) and along a rank equality.
2. **Binary products** (`binaryProduct_hasFiniteLength`). Let `X.1` and `X.2` be of
   finite length, of ranks `a` and `b`. Then the published
   `T.binaryNormalizedProductFunctor a b` sends `X` to a representation of finite
   length, in every rank:
   - `a = 0`: `GL_0` is finite, so `X.1` is finite-dimensional. The published
     `T.binaryLeftZeroTensorEquiv` identifies the product with `X.1 ⊗ X.2`, the
     group acting through the surjection `GeneralLinear.reindex`. Then
     `isFiniteLength_secondFactor` and `isFiniteLength_comp` apply.
   - `b = 0`: the same argument with `T.binaryRightZeroTensorEquiv` and
     `isFiniteLength_firstFactor`.
   - `0 < a`, `0 < b`: the published `T.binaryNormalizedProductPositiveIso`
     identifies the product with the block-shape product of
     `GeneralLinear.BlockShape.binary a b`. The published
     `Classification.admissibleFiniteLengthProductPreservation` (at carrier
     universe `max uF uV`) gives its finite length. It needs each factor
     admissible and of finite length. The published `finiteLengthAdmissibility`
     gives admissibility from finite length.
3. **Leibniz step** (`binaryProduct_derivatives`). Suppose all derivatives of `A`
   (rank `a`) and of `B` (rank `b`) have finite length. Let `d ≤ a + b`. The
   published `generalLinearDerivativeLeibnizFiltration` (at carrier universe
   `max uF uV`), through
   `GeneralLinearDerivativeLeibnizFiltrationStatement.filtration`, gives an actual
   finite filtration of `leibnizSource T ψ a b d hd`. Its graded pieces are
   isomorphic to the pieces `leibnizPiece T ψ a b d x`, one for each feasible index
   `x = (i, j)` with `i + j = d`, `i ≤ a`, `j ≤ b`. At `(A, B)` the source is the
   derivative `(generalLinearDerivative T ψ (a + b) d hd).obj (A × B)`. The piece is
   the rank transport of the binary product `A^(i) × B^(j)`. Each piece has finite
   length by the hypotheses, step 2 and `hasFiniteLength_rankCast`. Then
   `isFiniteLength_of_filtration` gives the conclusion.
4. **Block-shape form** (`binaryStep`). The same conclusion holds for the
   block-shape product of `BlockShape.binary a b`, transported to rank `n = a + b`.
   It follows from step 3 by `binaryNormalizedProductPositiveIso` and an equality
   of factor families.
5. **One block** (`singletonStep`). For a shape with one block, the published
   `normalizedProductInductionObjEquiv` and `singleBlockTransportedProductEquiv`
   identify the product with the rank transport of the single factor. Then
   `derivatives_transport` applies. The equality of the transported families uses
   two private transport-cancellation lemmas (`transport_symm_cancel`,
   `singleFamily_eq`), following `FiniteTopLine`.
6. **Induction on the number of blocks** (`product_derivatives`). This is strong
   induction on `l = B.length`, for every `n > 0`. The case `l = 0` is impossible,
   since `n` is the sum of the block sizes. The case `l = 1` is step 5. For
   `l = m + 2`, the published `T.headTailProductInductionIso` identifies the
   product with the binary product of the lifted head factor
   `SmoothRep.universeLift (σ head)` and the product of the tail shape. That tail
   shape has `m + 1` blocks. The induction hypothesis covers the tail. The head's
   derivatives transfer along `SmoothRep.universeLiftEquiv`. Step 4 then gives the
   product.
7. **Supercuspidal factors** (`supercuspidal_derivatives`). Let `A` be irreducible
   supercuspidal of rank `m > 0`. The published
   `Classification.supercuspidalDerivatives` gives two facts: derivatives of order
   `0 < k < m` are subsingletons, and the top derivative has `finrank` one. So
   every derivative has finite length. Order `0` is `A` itself, a simple module
   (`Representation.irreducible_iff_isSimpleModule_asModule`). Middle orders are
   subsingletons. The top order is finite-dimensional.
8. **Main theorem.** `productDerivativesFiniteLength` applies step 6 with
   `l = B.length`, and step 7 to each factor (each block has positive size).

## Source and provenance

The registered original is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I*, Ann. Sci. ÉNS (4) 10 (1977), 441–472, source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The hash was
rechecked. Pages are printed numbers, with one-based PDF pages in parentheses. The
following passages were read:

- §3.5, printed p.452 (PDF page 13), and §4.3, printed p.454 (PDF page 15): the
  derivatives `π^(0) = π`, `π^(k) = (π|_(P_n))^(k)`.
- §4.4, printed p.454 (PDF page 15): Gelfand–Kazhdan. For quasicuspidal `π`,
  `π^(k) = 0` for `0 < k < n`. For irreducible cuspidal `π`, `π^(n)` is
  one-dimensional.
- Lemma 4.5, printed p.455 (PDF page 16): `(ρ × ω)^(k)` is glued from
  `ρ^(i) × ω^(k-i)`. Corollary 4.14(c), printed p.458 (PDF page 19), restates it
  and proves it. The same page (p.455) states Corollary 4.6, `𝒟(ρ₁ × … × ρ_r) =
  𝒟ρ₁ × … × 𝒟ρ_r`, in the Grothendieck ring of finite-length modules. That ring
  already presupposes the finite length of the derivatives of such products.

No applicable errata entry was found in the central-library literature index
(`/home/taskhub/pilot/literature/_central-library-pointers.md`) or the public notes.

### What comes from the source and what is derived

- **Source assertions, used through published theorems.** Cuspidal derivatives
  (§4.4) enter only through `Classification.supercuspidalDerivatives`. Leibniz
  gluing (Lemma 4.5 = Corollary 4.14(c)) enters only through
  `generalLinearDerivativeLeibnizFiltration`. This module proves neither.
- **General finite-length inputs.** These are not BZ77 derivative theory. Finite
  length of normalized products of admissible finite-length factors is the
  published `admissibleFiniteLengthProductPreservation`. Its Markdown derives it
  from Casselman 1995, Corollary 6.3.8. Admissibility of finite-length
  representations is the published `finiteLengthAdmissibility`. Its Markdown
  cites Bernstein–Zelevinsky 1976, Theorems 3.25 and 4.1, and Casselman's notes.
- **Internal conclusion.** The source does not state as a numbered result that
  every derivative of a product of irreducible cuspidal representations has finite
  length. It uses this only tacitly, in §4.5 and Corollary 4.6. This module derives
  the fact internally. It combines finite length of the glued pieces with
  additivity of length along a filtration, and inducts on the number of blocks
  through the head–tail regrouping. It also handles the rank-zero factors of the
  Leibniz pieces (the order-`a` and order-`b` derivatives live on `GL_0`)
  separately, by tensor descriptions. The source's ring-homomorphism formulation
  (Corollary 4.6) is not formalized or used.

## Imports and independence

The direct imports are:

- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`;
- `Langlands.Representation.Parabolic.HeadTailProductInduction`;
- `Langlands.Representation.Classification.SupercuspidalDerivativesProof`;
- `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`;
- `Langlands.Representation.Smooth.Admissibility.FiniteLengthProof`;
- `Langlands.Representation.Filtration.RepresentationLength`;
- `Mathlib.Data.ENat.BigOperators`.

The transitive project import closure has 855 `Langlands` modules, excluding this
module. All of them are byte-identical (Lean and Markdown) to Library commit
`46ad94719738ee676dd6e863d6e924cca8fec970`.

The closure was checked against the exclusions of task `2306027f`:

- No Lean source in the closure names a conclusion excluded there. The search
  covered `GenericSegmentProductUniqueness`,
  `SquareIntegrableLanglandsClassification`, `SegmentHeadProductIrreducibility`,
  `SegmentSocleProductIrreducibility`, the unlinked and linked segment-socle
  structures, `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
  `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`,
  `SegmentSocleDerivatives`, `HighestDerivativeSupportShift`,
  `NonjuxtaposedSegmentSocle…` and `IsSegmentSocle`.
- No closure Lean source names any excluded task ID. The closure Markdown files that
  name excluded tasks or conclusions do so only in "not imported and not used"
  independence sections.
- The segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292` is not in
  the closure. That part is `Classification.SegmentSocleDerivativesStatement`,
  `HighestDerivativeSupportShiftProof`, the `SegmentSocleProduct…` modules and
  `SingletonSegmentSocle`. The cuspidal-derivative part is the separate module
  `Classification.SupercuspidalDerivativesStatement` with its proof
  `SupercuspidalDerivativesProof`. That proof imports only that statement,
  `SupercuspidalTopDerivative`, `Whittaker.MultiplicityOneProof` and
  `LocalField.Normalization.Proof`. The segment-socle statement module imports the
  cuspidal one, not the reverse.
- The only segment module in the closure is `Classification.Segments`. It contains
  definitions (segments, multisegments) plus elementary transport and unfolding lemmas and is reached through
  `SupercuspidalSupport` ← `CuspidalTensorStatement` ← `CuspidalTensorProof` ←
  `IrreducibleProductFiniteLengthProof` ← `NormalizedProductFiniteLengthProof`.
- The closure also contains `Derivative.Homogeneity` and `Derivative.LevelCalculus`.
  `Homogeneity` defines derivative level and homogeneity (Zelevinsky 1980 §4.3,
  §§5.1–5.2). `LevelCalculus` proves elementary facts about maps, short exact
  sequences and levels. They are reached through `RightMixedProductDerivativePositive`
  ← `RightMixedProductDerivativeFiltrationProof` ←
  `GeneralLinearDerivativeLeibnizFiltrationProof`. Neither states or uses a
  segment, socle or segment-derivative result, and neither is one of the
  statements of task `8e5b4563`.
- Only two closure Lean sources cite Zelevinsky 1980: `SupercuspidalSupport` (§1.10)
  and `RelationInversions` (§6.7, combinatorics). The closure Markdown cites
  Zelevinsky 1980 only for definitions and elementary facts:
  - §1.5, products (`BlockFactors`);
  - §1.10, quasicuspidality of tensor products and supercuspidal support
    (`SupercuspidalSupport`, `LeviTensorFactorizationStatement`,
    `LeviTensorReflectionStatement`);
  - §§3.1, 4.1, 6.1, 6.5 and 9.1, segments, linkage, heads and socles (`Segments`,
    `ConstituentRelations`);
  - §4.3 and §§5.1–5.2, level and homogeneity (`Homogeneity`, `LevelCalculus`);
  - §5.3, a subgroup lemma for the mixed-product embedding
    (`Mirabolic.LeftMixedProductSuccessor`).

  Other closure Markdown files mention §§3.5 and 9.6, for example
  `SupercuspidalDerivativesProof.md` and `MirabolicDerivativeDetectionStatement.md`.
  Each of these mentions is an explicit "not used" or exclusion remark. No segment
  derivative formula of Zelevinsky 1980 is used.

The published theorems used are `generalLinearDerivativeLeibnizFiltration`
(through `GeneralLinearDerivativeLeibnizFiltrationStatement.filtration`),
`Classification.supercuspidalDerivatives`,
`Classification.admissibleFiniteLengthProductPreservation`,
`finiteLengthAdmissibility` and `repLength_eq_sum_of_filtration`. Also used are
the published constructions and isomorphisms `binaryNormalizedProductFunctor`,
`binaryNormalizedProductPositiveIso`, `binaryPairFamilyFunctor`,
`binaryLeftZeroTensorEquiv`, `binaryRightZeroTensorEquiv`,
`normalizedProductInductionObjEquiv`, `singleBlockTransportedProductEquiv`,
`headTailProductInductionIso`, `SmoothRep.universeLift` and `universeLiftEquiv`.
Exactness of the derivative is not used in this module.

## Development validation

The module was compiled with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library base `46ad9471`, with no errors
or warnings. Declaration inspection of `productDerivativesFiniteLength` reports
kind `theorem`, level parameters `uF, uV`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, `admit` or new axiom is used.
These checks are separate from independent review and publication.
