# Derivative supports of a special head: orders `0` and `deg Δ`, and segments of length one and two

Author: Worker 256 (task `65a3925f-2cf6-464e-8486-d823160921a1`, shared with
Worker 890).

Module `Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo`,
namespace `Langlands.Classification.SegmentHeadDerivativeSupportLengthTwo`.

This module proves the base cases of the support-only terminal truncation bound
`Langlands.Classification.SegmentHeadDerivativeSupportTruncation.{uF,uV} F T`
(module `Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement`).
It covers derivative orders `0` and `deg Δ` for segments of any length, and every
derivative order for segments of length one and two. It does not prove the
target statement. The step for segments of length at least three
(`SegmentHeadSupportStep`) and the final assembly
(`SegmentHeadDerivativeSupportTruncationProof`) are separate modules by
Worker 890 and are not described here. The step module does not import this
module: it takes the length-one and length-two cases as hypotheses. Only the
final assembly imports this module, and it supplies `lengthOne_support` and
`lengthTwo_support` for those hypotheses.

## Exported results

Every exported result has the outer parameters
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)` and
works under `T.topology`. The universes `uF` (field) and `uV` (supercuspidal
carriers) are independent, and the head and its derivatives have carrier universe
`max uF uV`, exactly as in the target. Write `Concl Δ σ` for the target's
conclusion,

```lean
∃ (s : Multiset (T.CuspidalDatum.{uV, uF})) (B : Option (T.Segment.{uV, uF})),
  T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation B Δ ∧
    {ρ | ρ ∈ s} = Segment.optionalSupport B
```

and `D_k π` for `(generalLinearDerivative T ψ Δ.degree k hk).obj π`.

| Theorem | Arguments after `F T` | Conclusion |
| --- | --- | --- |
| `orderZero_support` | `ψ Δ π (hπ : T.IsSegmentHead Δ π) k hk (hk0 : k = 0) σ (hσ : σ.IsIrreducible) (hsub : SmoothRep.IsSubquotient σ (D_k π))` | `Concl Δ σ` |
| `topOrder_support` | `Δ k (hkt : k = Δ.degree) σ (hσ : σ.IsIrreducible)` | `Concl Δ σ` |
| `lengthOne_support` | `ψ Δ (hΔ : Δ.length = 1) π hπ k hk σ hσ hsub` | `Concl Δ σ` |
| `lengthTwo_support` | `ψ Δ (hΔ : Δ.length = 2) π hπ k hk σ hσ hsub` | `Concl Δ σ` |

Here `ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`,
`Δ : T.Segment.{uV, uF}`,
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)`,
`hk : k ≤ Δ.degree` and
`σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier)`.
`topOrder_support` needs no head and no subquotient relation. Every irreducible
representation of the rank-zero group has the empty support.
`lengthOne_support` and `lengthTwo_support` add only the length equation to
the target's hypotheses. No reducibility, finite-length, nonvanishing or
multiplicity premise is used. The reducibility of `ρ × νρ` is proved inside
the module from the published theorem described below.

The witnesses are:

- order `0`: `s = Δ.cuspidalContent` and `B = some Δ`;
- order `deg Δ`: `s = 0` and `B = none`;
- length two, order `rank Δ`: `s = {νρ}` and `B = some [νρ]`, the segment of
  length one with base `Δ.member 1 = νρ`, where `ρ = Δ.base`;
- the remaining orders: there is no irreducible subquotient, and the proof
  derives a contradiction.

Every other declaration of the module is a helper with its own docstring. The
helpers are public so that a downstream module can reuse them. None of them
states more than its Lean type.

## Implemented proof

### Order `0` (`orderZero_support`)

After `subst hk0` the order-`0` derivative of `π` is `π` itself, definitionally.
The head relation supplies a supercuspidal representative `A` of `Δ.base` and a
surjection from `i(A) = T.segmentInduced A.obj Δ.length Δ.rank_pos` onto `π`.
`segmentInduced_eq_cuspidalProductInduced` (`rfl`) identifies `i(A)` with the
cuspidal product of the members `ν^i ρ`, represented by `memberRep F T Δ A i`, the
real twist of `A` by `ν^i`. Hence `σ` is a subquotient of that cuspidal product.
This is the support datum for `Δ.cuspidalContent`. The terminal truncation
`some Δ` holds because `Δ.last ∈ Δ.support`, and its support is
`{ρ | ρ ∈ Δ.cuspidalContent}` by `Segment.mem_cuspidalContent`.

### Order `deg Δ` (`topOrder_support`)

Here `σ` is a representation of `GL_0`. The empty cuspidal family has total rank
`0`. Its normalized product is one-dimensional by `rankZeroProductLinearEquiv`
(evaluation at the identity of the trivial group, followed by the empty tensor
product). An irreducible representation of the trivial group is a line, so `σ` is
equivalent to that product and is a subquotient of it. This gives
`IsSupercuspidalSupport σ 0`, `B = none` and the empty support.

### Segments of length one (`lengthOne_support`)

Orders `0` and `deg Δ` are the two cases above. For `0 < k < deg Δ`:
`lengthOne_segmentInduced` identifies `i(A)` with the reindexed single block `A`
(`singleBlockNormalizedProductEquiv`), so `i(A)` is irreducible and supercuspidal.
The surjection from `i(A)` onto the irreducible head `π` is nonzero, hence
injective. So `π` is supercuspidal (`lengthOne_head_isSupercuspidal`). By BZ77
4.4 (the published `supercuspidalDerivatives`), `D_k π` is zero for
`0 < k < deg Δ` and has no irreducible subquotient.

### Segments of length two (`lengthTwo_support`)

Let `r = rank Δ`, `A0 = A` and `A1 = νA` (the member representatives), so that
`[A1] = ν[A0]`. Orders `0` and `2r` are handled as above.
`segmentInduced_eq_binary` identifies `i(A)` with the rank cast (`r + r = deg Δ`)
of the binary normalized product `A0 × A1`. The published
`segmentHeadTopDerivativeNontrivial` gives `D_{2r} π ≠ 0`. The theorem `core`
then shows that `0 < k < 2r` forces `k = r`, and that `σ` is a subquotient of
the rank cast of `A1`. `support_of_isSubquotient` turns this into
`IsSupercuspidalSupport σ {[A1]}`, using the published
`OrderedCuspidalProductHeadShift.irreducible_support_of_injective` applied to the
identity map. Since `[A1] = Δ.member 1 = Δ.last`, the segment `[νρ]` of length one
is a terminal truncation of `Δ` with support `{νρ}`.

`core` works on `GL_n` with `n = r + r`:

1. **Orders other than `r`.** The Leibniz filtration (BZ77 Corollary 4.14(c),
   published as `generalLinearDerivativeLeibnizFiltration`) gives `(A0 × A1)^(k)`
   a filtration with pieces `A0^(i) × A1^(j)`, `i + j = k`. By BZ77 4.4 both
   factors have zero derivatives of intermediate order and a one-dimensional top
   derivative (`SupercuspidalDerivativePattern`). So for `0 < k < 2r` with
   `k ≠ r` every piece is zero (`subsingleton_derivative_binary`). Exactness of
   the derivative (`generalLinearDerivativeExactness`) makes `D_k π` a quotient
   of zero, so it has no irreducible subquotient.
2. **Order `r`** (`core_mid`). Let `K` be the kernel of `q : A0 × A1 ↠ π`.
   - `K ≠ 0`. Otherwise `q` is bijective and `A0 × A1 ≅ π` is irreducible. The
     binary product equals the normalized product of `twoBlockFactors A0 A1` on
     `Shahidi.twoBlocks r r` (`binaryNormalizedProductFunctor_obj_eq_twoBlocks`),
     and the published `twoSupercuspidalAdjacentProductReducible`, with the
     alternative `[A1] = ν[A0]`, says that this product is not irreducible
     (`not_isIrreducible_binary`). This is the module's only use of that theorem.
   - `K^(k) = 0` for every `0 < k ≠ r`. For `k < 2r` this follows from step 1
     and exactness, since `K^(k)` injects into `(A0 × A1)^(k)`. For `k = 2r`,
     `(A0 × A1)^(2r)` is one-dimensional (`finrank_top_binary`). A nonzero vector
     of `K^(2r)` would span its image in this line and map to zero, so the
     surjection onto `D_{2r} π` would be zero, contradicting
     `segmentHeadTopDerivativeNontrivial`.
   - So the restriction of `K` to the mirabolic subgroup is nonzero and has
     level exactly `r`, and `K^(r) ≠ 0` (`LevelCalculus`, `level_le` and the
     `RestrictionBridge` comparisons of mirabolic and general-linear derivatives).
   - `(A0 × A1)^(r)` has a filtration `0 ⊂ S ⊂ (A0 × A1)^(r)` with irreducible
     factors, one of them equivalent to the rank cast of `A1`
     (`exists_twoStep_filtration_binary`). The Leibniz pieces of order `r` with
     indices other than `(0, r)` and `(r, 0)` are zero. The published
     `zeroFactorDeletionTheorem` removes them. The remaining pieces are
     `A0 × A1^(r) ≅ A0` and `A0^(r) × A1 ≅ A1`, because a top derivative of a
     supercuspidal representation is a line on `GL_0`.
   - The rank cast of `A1` does not embed in `K^(r)` (`no_shifted_embedding`).
     BZ77 Lemma 4.7(b), published as `cuspidalProductMirabolicSupportShift`,
     says the following. For the level-`r` subrepresentation `K` of the cuspidal
     product `A0 × A1`, every irreducible subrepresentation `τ` of the level-`r`
     mirabolic derivative of `K` has `ν · supp(τ) ≤ {[A0], [A1]}`. An embedding
     of `A1` would give `ν[A1] ∈ {[A0], [A1]}`. But `ν[A1] = ν²[A0] ≠ [A0]` by
     `cuspidalIntegralTwistFreeness` (exponent `2`), and `ν[A1] ≠ [A1]` by
     `OrderedCuspidalProductTwistOne.twist_one_ne_self`
     (`twist_not_mem_pairDatum`).
   - The exact sequence `K^(r) ↪ (A0 × A1)^(r) ↠ D_r π` and the abstract lemma
     `twoStep_quotient` make `D_r π` a quotient of the rank cast of `A1`. Hence
     `σ` is a subquotient of it.

`twoStep_quotient` is elementary lattice theory for a representation `X` with
a filtration `0 ⊂ S ⊂ X` whose two factors are simple, one of them equivalent
to `ξ`. Take a nonzero subrepresentation `K' ⊆ X` into which `ξ` does not embed,
and a surjection `X ↠ θ` with kernel `K'`. If `S ≅ ξ`, then `S ⊄ K'`, so
`S ∩ K' = 0` and `S + K' = X`, and `S ↠ θ`. If `X/S ≅ ξ`, then `S ⊆ K'`, since
otherwise `S ∩ K' = 0`, `S + K' = X` and `K' ≅ X/S ≅ ξ`. So `θ` is a quotient of
`X/S`. Simplicity is used through `LengthCriterionProof.hasSimpleFactors_iff_covBy`.

The argument uses no multiplicity count, length formula or Jacquet module of the
head, and it does not identify `D_k π`. It also uses no part of Ze80 1.11 beyond
the reducibility statement.

## Provenance of adapted helpers

Some generic helpers repeat arguments from published modules that this module
deliberately does not import:

- Section `BinaryProducts`, and `binary_eq_twoBlocks`,
  `normalizedProductInductionFunctor_obj_congr` and
  `binaryNormalizedProductFunctor_obj_eq_twoBlocks`, are adapted from
  `Classification.TwoSupercuspidalBinaryProductBridge` (Worker 745, task
  `3c9849a4`).
- Section `Leibniz` (the Leibniz-piece case analysis and the top-order
  dimension) is adapted from `Classification.NonadjacentLeibnizPieces`
  (Worker 745, task `3c9849a4`). The index information for the pieces `(0, b)`
  and `(a, 0)`, and the two-step filtration, are new here.
- `rankZeroProductLinearEquiv` is adapted from
  `rankZeroNormalizedProductLinearEquiv` in
  `Classification.OrderedMultisegmentHeadReduction`, with the rank given by an
  equation.

The copied arguments are general facts: binary products with zero or rank-zero
factors, Leibniz pieces of products of factors with the BZ77 4.4 pattern, and
the rank-zero normalized product. They contain no conclusion of Ze80 1.11 or of
any excluded task. The two Worker 745 modules are in this module's closure only
through the authorized reducibility import (below). They are not imported
directly, and none of their declarations is used. `OrderedMultisegmentHeadReduction`
is not in the closure.

## Authorization

The operator responses below govern the target task. Each is cited in full at
its path in `/home/taskhub/pilot/correspondence/`.

- [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
  (request `7bd9e666c60d53469eff04b2962e1acf`) authorizes a new proof of exactly
  the support-only statement from published general derivative theory and
  the permitted individual-head constructions.
- [bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md)
  (request `a8463ee15d57588c8de10306748b2538`) permits a fully proved route
  through BZ77's general derivative theory and excludes Ze80 3.5/9.6.
- [0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
  (request `d910ee3b12f2515f9568a4f2f2f1442f`) admits BZ77 4.11, Ze80 3.7(b)
  through the Lemma 4.7(b) closure, Ze80 5.3 and the nine generic modules.
- [09565d9017ef55faa68ad9890c242aed](/home/taskhub/pilot/correspondence/09565d9017ef55faa68ad9890c242aed.md)
  (request `f489243c6b4e5a93a776216687d56d51`) admits
  `cuspidalProductMirabolicSupportShift` with its whole closure as general
  derivative theory. It is incorporated by 0edda612.
- [2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md)
  (request `64f1e681367a5c0d9de435c691ff88dc`, from this author) permits
  task `65a3925f` to import `twoSupercuspidalAdjacentProductReducible` (proof
  task `0988a3e0`) with its published closure, including the Ze80 1.11(a)
  conclusion of `3c9849a4` used inside it, solely to obtain the reducibility
  of `ρ × νρ`. Nothing else from Ze80 1.11 may be used, in particular not
  `TwoSupercuspidalProductStructureProof` or its length-two and Jacquet parts.
  The Whittaker modules inside that closure are covered only as part of it.

The ruling is needed because the target implies this reducibility. Suppose
`ρ × νρ` were irreducible for `Δ = [ρ, νρ]`. Then it would be its own special
head, and its derivative of order `rank ρ` would have the Leibniz piece
`ρ × (νρ)^(rank ρ) ≅ ρ` as an irreducible subquotient. Its support `{ρ}` is not
the support of any terminal truncation of `Δ`.

Permission is not proof. Each input below is an independently accepted
theorem in the published Library.

## Published input verification

The audit base is Library commit `df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e`.
The module was compiled with `lean_check` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` against that Library with zero errors
and zero warnings. The final checks `4d72b3a0`, `0f55d7ae`, `787ea759` and
`c6e61513` inspected `lengthOne_support`, `topOrder_support`,
`orderZero_support` and `lengthTwo_support`. Each has level parameters exactly
`uF, uV` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. The module has no `sorry`, `admit` or new axiom. Compilation is
preparation evidence, not acceptance.

Recheck at Library commit `7a2e42fd31831029d34cafb155ffad911920df25`: all 1,163
published modules in the closure are byte-identical (`.lean` and `.md`) to
`df7769b3`. The audit script reproduces the same counts, and the module
recompiles there with zero errors and zero warnings (`lean_check` `6244c86f`).
The counts and listings below therefore hold for both commits.

All 1,163 project modules in the closure (including the 19 direct imports) are published
Lean/Markdown pairs. The workspace copies used for compilation are
byte-identical to the audit Library, and no paired Markdown is missing. The
reducibility theorem is `Langlands.Classification.twoSupercuspidalAdjacentProductReducible`
in `Classification.TwoSupercuspidalAdjacentReducibilityProof` (Worker 1023). Its
type is exactly the published proposition
`TwoSupercuspidalAdjacentProductReducible.{uF,uV} F T`. Its route (Ze80 1.11(b),
printed p.175) uses the published nonadjacent irreducibility, the irreducible
product swap, unitarizability continuation, large-exponent non-unitarizability
and real unitarization of supercuspidals. It has no segment, head, socle,
Jacquet-formula, 3.5/9.6 or classification input, as its own Markdown audit and
ruling 2b33898b record.

## Complete import closure

A recursive scan follows project imports (`Langlands.*`) from this module. The
scan strips block comments, line comments and string literals before reading
`import` lines. There are 1,164 project modules including this root, and 315
distinct external import roots. If the authorized import
`TwoSupercuspidalAdjacentReducibilityProof` is removed from the roots, the
closure of the other 18 direct imports has 1,110 modules. The remaining 53
modules are reached only through the authorized import and are marked `*` in
the appendix.

| Direct import, prefixed by `Langlands.Representation.` | Project closure, including that import | Role in this module |
| --- | ---: | --- |
| `Classification.SegmentTruncationObstructionStatement` | 51 | Definitions `Segment.IsTerminalTruncation` and `Segment.optionalSupport` used by the target |
| `Induction.BinaryProduct` | 36 | Binary normalized product functor, its unit and zero-factor equivalences, rank-zero group facts |
| `Induction.SingleBlock` | 32 | `singleBlockNormalizedProductEquiv` and `Induction.smoothInducedTopEquiv` |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | 324 | BZ77 Corollary 4.14(c) Leibniz filtration, with `leibnizPiece` and `leibnizIndices` |
| `Derivative.GeneralLinearDerivativeExactnessProof` | 73 | Exactness of the general-linear derivative functors |
| `Derivative.RestrictionBridge` | 86 | Mirabolic versus general-linear derivatives; nontriviality transport through rank casts |
| `Classification.SupercuspidalDerivativesProof` | 304 | BZ77 4.4 `supercuspidalDerivatives`, the cuspidal-derivative part of `8e5b4563` |
| `Classification.CuspidalProductMirabolicSupportShiftProof` | 607 | BZ77 Lemma 4.7(b) `cuspidalProductMirabolicSupportShift` |
| `Classification.SegmentHeadTopDerivative` | 1,095 | `segmentHeadTopDerivativeNontrivial` |
| `Classification.CuspidalIntegralTwistFreenessProof` | 55 | `cuspidalIntegralTwistFreeness` (`ν^2 ρ ≠ ρ`) |
| `CuspidalSupport.JacquetVanishingHelpers` | 48 | `CuspidalSupport.objectFiltrationAt`, evaluation of a functor filtration at an object |
| `Exponents.WeylBranchPiecesSubquotient` | 126 | Representation-level subquotient lemmas `of_equiv`, `of_surjective`, `trans` |
| `Tensor.SmoothSubquotients` | 148 | `SmoothRep.isSubquotient_iff_representation` |
| `Filtration.ZeroFactorDeletionProof` | 4 | `ObjectRepFiltration.zeroFactorDeletionTheorem` |
| `Filtration.SubsingletonProof` | 27 | `objectRepFiltrationSubsingleton` |
| `Filtration.FunctorLengthTwoDetection` | 12 | `FunctorLengthTwo.subtypeMap`; brings `LengthCriterionProof` and `LengthTwoMatching` |
| `Classification.SegmentCuspidalContent` | 51 | `Segment.cuspidalContent` and `Segment.mem_cuspidalContent` |
| `Derivative.OrderedCuspidalProductHeadShift` | 612 | `irreducible_support_of_injective`; brings `OrderedCuspidalProductTwistOne` |
| `Classification.TwoSupercuspidalAdjacentReducibilityProof` | 739 | `twoSupercuspidalAdjacentProductReducible`, authorized by 2b33898b |

Closure sizes overlap and are not additive. `SegmentHeadTopDerivative` alone
reaches 1,095 modules. Its complete closure and proof routes are audited in its
published Markdown (Worker 357), under response 0edda612.

The 53 modules reached only through the authorized import, with prefix
`Langlands.Representation.` except where fully written, are:

- the reducibility pair `Classification.TwoSupercuspidalAdjacentReducibility{Statement,Proof}`
  and its proof inputs
  `Classification.IrreducibleTwoFactorProductSwap{Statement,Proof}`,
  `Classification.TwoBlockExponentNonUnitarizability{Statement,Proof}`,
  `Classification.TwistedProductCharacterTwistProof`,
  `Classification.ExponentFamily`,
  `Unitary.UnitarizabilityContinuation{Statement,Proof}`,
  `Unitary.SupercuspidalRealUnitarization{Statement,Proof}` and
  `Unitary.LeviCuspidalRealUnitarization{Statement,Proof}`;
- the Ze80 1.11(a) proof `Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`
  with its helpers `Classification.Nonadjacent{Assembly,LeibnizPieces,Specialization,TwoBlock}`,
  `Classification.TwoSupercuspidal{BinaryProductBridge,DerivativeBridge,ProductDualTwist}`
  and the statement module `Classification.TwoSupercuspidalProductStructureStatement`;
- general unitary, Hermitian and integral-form infrastructure:
  `Unitary.{CentralCharacterStatement,CentralCharacterProof,HermitianDual,Twist,SquareIntegrableStatement,SquareIntegrableProof}`,
  `Tensor.Unitary{Statement,Proof}`,
  `MatrixCoefficient.{HermitianProduct,NormRegularityStatement,NormRegularityProof}`,
  `Induction.{CompactIntegralForm,CovariantRescaling,NormalizedIntegralForm}`,
  `Filtration.{InvariantBilinearSubquotientBounds,SmoothDualEvaluation}`,
  `Parabolic.{InverseTransposeProductStatement,InverseTransposeProductProof,NormalizedCompatibilityStatement}`,
  `Twist.Pullback{Statement,Proof}`,
  `Classification.{ConstituentCompatibility,UnitaryGenericCompatibilityStatement}`;
- `Langlands.Group.GL.{BlockScalarCenter,CentralQuotientTopologyStatement,CentralQuotientTopologyProof}`,
  `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExists{Statement,Proof}` and
  `Langlands.LocalField.SmoothCharacterNorm{Statement,Proof}`.

`Unitary.SquareIntegrable*` proves unitarizability of irreducible
representations with square-integrable coefficients modulo the center. It is
not the excluded square-integrable classification or exhaustion.
`TwoSupercuspidalProductStructureStatement` is a statement module that proves
nothing. Of it, this module uses only the definition `twoBlockFactors`, which
appears in the type of the reducibility proposition.

## Published declarations used

A private compiled probe listed the external constants used directly by this
module's declarations (859 constants, of which the project ones are grouped
below by module). It also attributed every reachable constant from a sensitive
module to the direct constant that reaches it. The probe was compiled with the
module and deleted afterwards. Its output is preparation evidence.

| Module (prefix `Langlands.`) | Declarations used directly |
| --- | --- |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` | `Classification.twoSupercuspidalAdjacentProductReducible` |
| `Representation.Classification.TwoSupercuspidalProductStructureStatement` | `Classification.twoBlockFactors` (definition only) |
| `Representation.Classification.SegmentHeadTopDerivative` | `Classification.segmentHeadTopDerivativeNontrivial` |
| `Representation.Classification.SupercuspidalDerivativesProof` | `Classification.supercuspidalDerivatives` |
| `Representation.Classification.CuspidalProductMirabolicSupportShiftProof` | `Classification.cuspidalProductMirabolicSupportShift` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` | `Classification.cuspidalIntegralTwistFreeness` |
| `Representation.Derivative.OrderedCuspidalProductHeadShift` | `Derivative.OrderedCuspidalProductHeadShift.irreducible_support_of_injective` |
| `Representation.Derivative.OrderedCuspidalProductTwistOne` | `Derivative.OrderedCuspidalProductTwistOne.twist_one_ne_self` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` and `...Statement` | `Derivative.generalLinearDerivativeLeibnizFiltration`, its `filtration` field, `LeibnizIndex`, `leibnizIndices`, `leibnizIndices_rank`, `leibnizIndices_sum`, `leibnizIndices_top`, `mem_leibnizIndices`, `leibnizPiece`, `leibnizSource` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` | `Derivative.generalLinearDerivativeExactness` |
| `Representation.Derivative.RestrictionBridge` | `generalLinearDerivative_succ_obj_eq`, `nontrivial_generalLinearDerivative_iff`, `nontrivial_generalLinearRankCast_iff` |
| `Representation.Derivative.LevelCalculus`, `Homogeneity`, `Iteration` | `IsShortExact` and its fields, `isShortExact_kernelι`, `isShortExact_map`, `level_pos`, `hasNonzeroDerivative_level`; `level`, `level_le`, `HasNonzeroDerivative`, `mirabolicDerivativeOfOrder`; `generalLinearDerivative`, `generalLinearRankCast`, `generalLinearRestriction` |
| `Representation.Filtration.*` | `ObjectRepFiltration` API, `zeroFactorDeletionTheorem`, `objectRepFiltrationSubsingleton`, `LengthCriterionProof.{hasSimpleFactors_iff_covBy, quotientRep, lower, mem_bot_iff, mem_top}`, `LengthTwo.comap`, `FunctorLengthTwo.subtypeMap`, `RepFunctorFiltration` API |
| `Representation.Classification.{Segments,SegmentCuspidalContent,SegmentTruncationObstructionStatement,SupercuspidalSupport,Supercuspidal,SupercuspidalTwist,ConstituentRelations}` | Definitions of segments, members, cuspidal data and their twists, `IsSegmentHead`, `IsSupercuspidalSupport`, `cuspidalProductInduced`, `cuspidalShape`, terminal truncations, supercuspidal representations and real twists, `CuspidalDatum.twist_twist`, `supercuspidalClassRealPowerTwist_add`, `isSupercuspidal_of_equiv` |
| `Representation.Induction.*`, `Representation.Category.*`, `Representation.Tensor.SmoothSubquotients`, `Representation.Exponents.*`, `Weil.Representation.IsomorphismInvarianceProof`, `Group.GL.*`, `Representation.Shahidi.TwoBlocks` | Category of smooth representations, kernels, universe lift, subquotients, binary and block products, single block, rank reindexing, `Shahidi.twoBlocks`, irreducibility under equivalence |

The probe's attribution of reachable constants:

- Whittaker and Gelfand–Kazhdan constants are reached only through
  `supercuspidalDerivatives` (BZ77 4.4, through Gelfand–Kazhdan multiplicity
  one), `segmentHeadTopDerivativeNontrivial`, `cuspidalProductMirabolicSupportShift`
  (Ze80 3.7(b) through the Lemma 4.7(b) closure),
  `generalLinearDerivativeLeibnizFiltration` (only the Iwasawa integration
  helpers) and the authorized reducibility theorem.
- Constants of `SegmentHeadProductFiniteness` and of the individual
  constituent existence proof are reached only through
  `segmentHeadTopDerivativeNontrivial`, which uses
  `IsSegmentHead.isIrreducible` and the published decreasing-socle embedding.
- Constants of the two-supercuspidal family are reached only through
  `twoSupercuspidalAdjacentProductReducible` and the definition `twoBlockFactors`.

## Mathematical dependency audit

1. **BZ77 derivative theory.** The Leibniz filtration, exactness of
   derivatives, the restriction bridge, levels and the cuspidal-derivative
   theorem 4.4 are published general BZ77 results. They are the foundations
   named in bd71b918 and 30144f6f. `supercuspidalDerivatives` is the isolated,
   independently proved cuspidal-derivative part of `8e5b4563`, which those
   rulings permit. Its proof uses Gelfand–Kazhdan multiplicity one. That is the
   reason for the Whittaker Bruhat-cell and multiplicity-one modules in the
   closure.
2. **BZ77 Lemma 4.7(b).** `cuspidalProductMirabolicSupportShift` is used once,
   in `no_shifted_embedding`, for the kernel `K ⊂ A0 × A1`. Its closure, which
   includes the Ze80 3.7(b) comparison `PartialDerivativeJacquetComparisonProof`,
   `CuspidalProductDerivativeQuotientSupport` and the Whittaker prerequisite and
   character-change modules, is admitted by 09565d90 and 0edda612.
3. **The top derivative of the head.** `segmentHeadTopDerivativeNontrivial`
   is the published composition of BZ77 4.11 with the individual decreasing-socle
   embedding. Its published Markdown audits its route and closure under
   0edda612. Its closure carries the individual constituent existence, the
   head-finiteness interface and cuspidal Jacquet multiplicity modules. None of
   them supplies a full, head, socle or exponent Jacquet formula of a segment
   representation. This module uses only the nonvanishing of `D_{2r} π`.
4. **Twist freeness and supports.** `cuspidalIntegralTwistFreeness` and
   `twist_one_ne_self` are central-character arguments.
   `irreducible_support_of_injective` (from the BZ77 4.11 publication `bfc08f82`,
   admitted by 0edda612) gives the support of the rank cast of a supercuspidal.
5. **Reducibility.** `twoSupercuspidalAdjacentProductReducible` is used once,
   in `not_isIrreducible_binary`, to show `K ≠ 0`, as ruling 2b33898b permits.
   The module uses neither `TwoSupercuspidalProductStructureProof` (it is not
   in the closure) nor any length-two, unique-submodule or Jacquet statement of
   Ze80 1.11(b). Ze80 1.11(a) enters only inside the published reducibility proof.
6. **The new arguments.** The vanishing of `K^(k)` for `k ≠ r`, the level
   computation, the two-step filtration, the 4.7(b) exclusion and the lattice
   lemma `twoStep_quotient` are proved in this module from the inputs above.

## Authorized general infrastructure and retained exclusions

The closure contains the nine generic modules of response 0edda612
(`Filtration.ObjectTransport`, `Tensor.FiniteFiltration`,
`Tensor.ExternalFiltration`, `Tensor.ExternalSubrepresentation`,
`Parabolic.InductionSubrepresentation`,
`Parabolic.ProductInductionSubrepresentation`,
`Langlands.Combinatorics.RelationInversions`,
`Derivative.MirabolicMinusNormalization` and
`Classification.SupercuspidalDerivativesStatement`), with unchanged published
bytes. They are reached through the same general routes recorded in the
published `SegmentHeadTopDerivative` audit. `Filtration.CoinvariantVanishingStatement`,
`Induction.*Coinvariant*` and `Tensor.CoinvariantReflection` are general
coinvariant exactness modules from the 4.7(b) and Leibniz closures.
`CompactCoefficient.FixedLevelFiniteness` and
`CuspidalSupport.CompactCoefficientFiniteness{Statement,Reduction,Proof}` are
the general BZ76 4.16 finiteness of compact-coefficient classes. They are reached
through the cuspidal theory behind BZ77 4.4, 4.7(b) and 4.11. The closure
contains no Whittaker coinvariant-finiteness module. The `Essential`,
`Tempered*Statement`, `Relative*Statement` and `CanonicalConstituents` modules
reached through `Exponents.WeylBranchPiecesSubquotient` and
`Tensor.SmoothSubquotients` contain definitions and Prop-valued statements. No
proof of a tempered, essentially square-integrable or relative classification
statement is used.

| Excluded conclusion (target task Independence) | Dependency check |
| --- | --- |
| Parent `GenericSegmentProductUniqueness`, `30341ae4-65f2-4a0e-9283-763db01a409e` | No import or proof use |
| Multisegment exhaustion, `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No import or proof use |
| Ordered strong-head existence, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No import or proof use; the individual-segment constructions inside `SegmentHeadTopDerivative` are a different, permitted result |
| Quotient coverage, `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No import or proof use |
| Ordered conversion, `8252833d-c269-41a9-824c-5879e531b23b` | No import or proof use |
| Tempered uniqueness, `52e97845-36bb-457d-b76f-70753334b88c` | No import or proof use |
| `SquareIntegrableLanglandsClassification`, `1cb45da2-7007-4351-a694-594fb148b8d1` | No import or proof use; `Unitary.SquareIntegrable*` (unitarity from square-integrable coefficients) enters only through the authorized reducibility closure |
| Square-integrable exhaustion, `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No import or proof use |
| Regular exhaustion, `bf433f0a-921a-428c-b0c0-6475438125ac` | No import or proof use |
| Full `SegmentHeadProductIrreducibility`, either direction, host `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Neither its statement module nor any proof of it is imported; the target statement module is not imported either |
| Ze80 3.5 and 9.6, their proofs and successors; segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292` | No import or proof use; only the isolated cuspidal-derivative theorem `supercuspidalDerivatives` is used |
| `SegmentFullJacquetFormula` `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `SegmentHeadJacquetFormula` `55ad1e10-62d8-46b7-a081-909ef0056426`, `SegmentSocleJacquetFormula` `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `SegmentSpecialJacquetExponentNormFormula` `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No statement or proof module of these formulas is in the closure |
| Socle exhaustion `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`, ordered multisegment socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5` | No excluded conclusion imported or used; the generic modules introduced under `f3a69bc8` are those authorized by 0edda612 |
| Segment-socle product irreducibility `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`; unlinked or linked socle structure `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc`, `7ff2a1e9-89dc-439e-a861-a567b3db92bf` | No import or proof use |
| Adjacent and two-segment socle commutation `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab`, `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0`; linked socle gluing `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea`; downstream swaps | No import or proof use; `LeibnizPositiveGluing` and `LeibnizRankZeroGluing` are parts of the general Leibniz filtration proof, not socle gluing; the `LinkedSegment*` modules are not in the closure |
| Analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`; forward special-segment essential square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No import or proof use; `SegmentSpecialEssentialSquareIntegrabilityProof` is not in the closure |
| Two-supercuspidal product irreducibility or structure, including `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | Only `twoSupercuspidalAdjacentProductReducible` and its published closure (which contains the 1.11(a) proof), solely for reducibility, under ruling 2b33898b; `TwoSupercuspidalProductStructureProof` is not in the closure |
| Whittaker coinvariant-finiteness conclusions | No such module is in the closure; the Whittaker modules present are Gelfand–Kazhdan multiplicity one, Iwasawa integration, Bruhat-cell distributions and character-change helpers, on the routes listed above |
| Unproved statements, drafts and pending candidates | None is used as a proof; every theorem applied is a published proof |

## Scope

This module proves the four exported theorems and nothing more. It does not
state or prove the target for segments of length at least three, a derivative
formula, the irreducibility of any derivative, a multiplicity statement or
either direction of the special-head product criterion.

## Appendix: complete project import closure

The root is included. Modules marked `*` are reached only through the
authorized import `Classification.TwoSupercuspidalAdjacentReducibilityProof`.

```text
Langlands.Algebra.CommutingDimensionHelpers
Langlands.Algebra.CommutingDimensionNilpotent
Langlands.Algebra.CommutingDimensionNumerics
Langlands.Algebra.CommutingDimensionPrimary
Langlands.Algebra.CommutingDimensionRecurrence
Langlands.Algebra.SandwichDimensionBoundProof
Langlands.Algebra.SandwichDimensionBoundStatement
Langlands.Algebra.SeparatedMatrixRepresentations
Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasureExistence
Langlands.Analysis.Local.QuotientMeasureExistenceStatement
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.ClassFieldTheory.Local.Completion
Langlands.ClassFieldTheory.Local.FiniteArtin
Langlands.ClassFieldTheory.Local.Galois
Langlands.ClassFieldTheory.Local.Norms
Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
Langlands.ClassFieldTheory.Local.ReciprocityRelations
Langlands.ClassFieldTheory.Local.Transfer
Langlands.ClassFieldTheory.Local.Units
Langlands.ClassFieldTheory.Local.WeilAbelianization
Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
Langlands.Combinatorics.RelationInversions
Langlands.Correspondence.AutomorphicRelations
Langlands.Correspondence.Domains
Langlands.Correspondence.LocalConventions
Langlands.Correspondence.OperationCompatibility
Langlands.Correspondence.SupercuspidalRelations
Langlands.Correspondence.UnramifiedNormalization
Langlands.Galois.FiniteField.Comparison
Langlands.Galois.FiniteField.ComparisonProof
Langlands.Galois.FiniteField.Frobenius
Langlands.Galois.Local.AbsoluteDefinitions
Langlands.Galois.Local.AbsoluteProof
Langlands.Galois.Local.AbsoluteStatement
Langlands.Galois.Local.SpectralDefinitions
Langlands.Galois.Local.SpectralProof
Langlands.Galois.Local.SpectralStatement
Langlands.Group.GL.AdjacentMergeShape
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockContractionProof
Langlands.Group.GL.BlockContractionStatement
Langlands.Group.GL.BlockDeterminant
Langlands.Group.GL.BlockIwahoriBasis
Langlands.Group.GL.BlockIwahoriBasisStatement
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockModulusHaarProof
Langlands.Group.GL.BlockModulusHaarStatement
Langlands.Group.GL.BlockScalarCenter *
Langlands.Group.GL.BlockUnipotent
Langlands.Group.GL.BlockUnipotentCoordinates
Langlands.Group.GL.BlockUnipotentHaarProof
Langlands.Group.GL.BlockUnipotentHaarStatement
Langlands.Group.GL.Blocks
Langlands.Group.GL.CartanProof
Langlands.Group.GL.CartanStatement
Langlands.Group.GL.CentralQuotientTopologyProof *
Langlands.Group.GL.CentralQuotientTopologyStatement *
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.DominantExponentGeneration
Langlands.Group.GL.HeadTailBlocks
Langlands.Group.GL.IntegralSubgroup
Langlands.Group.GL.InverseTransposeIwahoriProof
Langlands.Group.GL.InverseTransposeIwahoriStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitSpecializations
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OneBlockShape
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.ParabolicModularCharacter
Langlands.Group.GL.PrincipalBlockFactorizationProof
Langlands.Group.GL.PrincipalBlockFactorizationStatement
Langlands.Group.GL.PrincipalLevelDominance
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RankReindex
Langlands.Group.GL.RefinementCoordinates
Langlands.Group.GL.ReindexCongr
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.SingletonBlocks
Langlands.Group.GL.Transvection
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperBruhatBoundaryProof
Langlands.Group.GL.UpperBruhatBoundaryStatement
Langlands.Group.GL.UpperBruhatCells
Langlands.Group.GL.UpperBruhatCoordinatesProof
Langlands.Group.GL.UpperBruhatCoordinatesStatement
Langlands.Group.GL.UpperBruhatEmbedding
Langlands.Group.GL.UpperBruhatFiltration
Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement
Langlands.Group.GL.UpperBruhatLocalClosednessProof
Langlands.Group.GL.UpperBruhatLocalClosednessStatement
Langlands.Group.GL.UpperBruhatPivotProof
Langlands.Group.GL.UpperBruhatPivotStatement
Langlands.Group.GL.UpperBruhatProof
Langlands.Group.GL.UpperBruhatRankProof
Langlands.Group.GL.UpperBruhatRankStatement
Langlands.Group.GL.UpperBruhatStatement
Langlands.Group.GL.UpperBruhatTransposeProof
Langlands.Group.GL.UpperBruhatTransposeStatement
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.Group.GL.UpperUnipotentFactorizationProof
Langlands.Group.GL.UpperUnipotentFactorizationStatement
Langlands.Group.HaarModulus
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.Distribution.Basic
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverage
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
Langlands.HarmonicAnalysis.Distribution.GeneralLinear
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement
Langlands.HarmonicAnalysis.Distribution.LocalizationProof
Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement
Langlands.HarmonicAnalysis.Distribution.Subspace
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.SupportedRestriction
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof *
Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement *
Langlands.HarmonicAnalysis.RowFourier
Langlands.HarmonicAnalysis.RowSchwartzAction
Langlands.HarmonicAnalysis.RowTensorDecompositionProof
Langlands.HarmonicAnalysis.RowTensorDecompositionStatement
Langlands.HarmonicAnalysis.RowTestSmoothProof
Langlands.HarmonicAnalysis.RowTestSmoothStatement
Langlands.HarmonicAnalysis.TriangularTranslationProof
Langlands.HarmonicAnalysis.TriangularTranslationStatement
Langlands.LinearAlgebra.CyclicQuotientPairingProof
Langlands.LinearAlgebra.CyclicQuotientPairingStatement
Langlands.LinearAlgebra.FiniteRankTrace
Langlands.LinearAlgebra.FiniteRankTranspose
Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
Langlands.LinearAlgebra.MatrixAEvalConjugacyStatement
Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof
Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement
Langlands.LinearAlgebra.MatrixTransposeConjugateProof
Langlands.LinearAlgebra.MatrixTransposeConjugateStatement
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement
Langlands.LocalFactor.Euler
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalFactor.Harmonic.Statement
Langlands.LocalFactor.RankOne
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.SmoothCharacterNormProof *
Langlands.LocalField.SmoothCharacterNormStatement *
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Abelian
Langlands.Representation.Category.Basic
Langlands.Representation.Category.ClassInvariants
Langlands.Representation.Category.ConstituentDichotomy
Langlands.Representation.Category.ConstituentDichotomyStatement
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.FiniteIndexRestriction
Langlands.Representation.Category.FiniteIndexSemisimplicity
Langlands.Representation.Category.FiniteIndexSemisimplicityStatement
Langlands.Representation.Category.RestrictionSubquotients
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Category.UniverseLift
Langlands.Representation.Character.Basic
Langlands.Representation.Character.SeparationProof
Langlands.Representation.Character.SeparationStatement
Langlands.Representation.Character.TransportProof
Langlands.Representation.Character.TransportStatement
Langlands.Representation.Classification.CanonicalConstituents
Langlands.Representation.Classification.CommonImageMultiplicityOneProof
Langlands.Representation.Classification.CommonImageMultiplicityOneStatement
Langlands.Representation.Classification.ConstituentCompatibility *
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Cosocle
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctors
Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.CuspidalProductContragredient
Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.ExponentFamily *
Langlands.Representation.Classification.HeadQuotientCriterionProof
Langlands.Representation.Classification.HeadQuotientCriterionStatement
Langlands.Representation.Classification.IrreducibleProductEmbedding
Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof *
Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement *
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.MirabolicDerivativeContragredient
Langlands.Representation.Classification.MultiplicityOneConstituentProof
Langlands.Representation.Classification.MultiplicityOneConstituentStatement
Langlands.Representation.Classification.NonadjacentAssembly *
Langlands.Representation.Classification.NonadjacentLeibnizPieces *
Langlands.Representation.Classification.NonadjacentSpecialization *
Langlands.Representation.Classification.NonadjacentTwoBlock *
Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement
Langlands.Representation.Classification.OppositeJacquetReciprocity
Langlands.Representation.Classification.OppositeSupportJacquetAdapter
Langlands.Representation.Classification.RelativeGenericityStatement
Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
Langlands.Representation.Classification.RelativeRegularComparisonStatement
Langlands.Representation.Classification.SegmentConstituentStatement
Langlands.Representation.Classification.SegmentCuspidalContent
Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct
Langlands.Representation.Classification.SegmentHeadDecreasingSocle
Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo
Langlands.Representation.Classification.SegmentHeadProductFiniteness
Langlands.Representation.Classification.SegmentHeadTopDerivative
Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement
Langlands.Representation.Classification.SegmentJacquetMultiplicityProof
Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement
Langlands.Representation.Classification.SegmentJacquetReversal
Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
Langlands.Representation.Classification.SegmentTensorReversalProof
Langlands.Representation.Classification.SegmentTensorReversalStatement
Langlands.Representation.Classification.SegmentTensorStabilizerProof
Langlands.Representation.Classification.SegmentTensorStabilizerStatement
Langlands.Representation.Classification.SegmentTruncationObstructionStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredient
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientProof
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalDerivativeVanishing
Langlands.Representation.Classification.SupercuspidalDerivativesProof
Langlands.Representation.Classification.SupercuspidalDerivativesStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalSupportStatement
Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
Langlands.Representation.Classification.SupercuspidalTopDerivative
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedInductionStatement
Langlands.Representation.Classification.TemperedSupportStatement
Langlands.Representation.Classification.TwistedProductCharacterTwistProof *
Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof *
Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement *
Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof *
Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement *
Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge *
Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge *
Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof *
Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist *
Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement *
Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement *
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CompactCoefficient.AdmissibleComplement
Langlands.Representation.CompactCoefficient.AdmissibleLifting
Langlands.Representation.CompactCoefficient.AdmissibleRetraction
Langlands.Representation.CompactCoefficient.AmbientProjector
Langlands.Representation.CompactCoefficient.Classes
Langlands.Representation.CompactCoefficient.ConditionalProjection
Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
Langlands.Representation.CompactCoefficient.GroupTransport
Langlands.Representation.CompactCoefficient.Isotypic
Langlands.Representation.CompactCoefficient.IsotypicTransport
Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
Langlands.Representation.CompactCoefficient.SelectedAssembly
Langlands.Representation.CompactCoefficient.SelectedBlock
Langlands.Representation.CompactCoefficient.SelectedConjugation
Langlands.Representation.CompactCoefficient.SelectedCoverage
Langlands.Representation.CompactCoefficient.SelectedProjector
Langlands.Representation.CompactCoefficient.SemisimplicityProof
Langlands.Representation.CompactCoefficient.SemisimplicityStatement
Langlands.Representation.CompactCoefficient.TotalCompactness
Langlands.Representation.CompactCoefficient.TotalProjector
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.AssociatedAssembly
Langlands.Representation.CuspidalSupport.AssociatedConditional
Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
Langlands.Representation.CuspidalSupport.AssociatedProof
Langlands.Representation.CuspidalSupport.AssociatedRankZero
Langlands.Representation.CuspidalSupport.AssociationForwardHomProof
Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport
Langlands.Representation.CuspidalSupport.AssociationForwardStatement
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.AssociationReduction
Langlands.Representation.CuspidalSupport.AssociationReverseProof
Langlands.Representation.CuspidalSupport.AssociationReverseStatement
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.BlockWeylTransport
Langlands.Representation.CuspidalSupport.CentralShift
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
Langlands.Representation.CuspidalSupport.ConstituentComplement
Langlands.Representation.CuspidalSupport.ConstituentComplementStatement
Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes
Langlands.Representation.CuspidalSupport.ConstituentInduction
Langlands.Representation.CuspidalSupport.ConstituentInductionStatement
Langlands.Representation.CuspidalSupport.ConstituentProof
Langlands.Representation.CuspidalSupport.ConstituentRankZero
Langlands.Representation.CuspidalSupport.ConstituentSemisimple
Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement
Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
Langlands.Representation.CuspidalSupport.CuspidalTensorProof
Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement
Langlands.Representation.CuspidalSupport.DeterminantUnit
Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement
Langlands.Representation.CuspidalSupport.DualAveraging
Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality
Langlands.Representation.CuspidalSupport.FiniteBlockShapes
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.HarishChandraAssembly
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement
Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement
Langlands.Representation.CuspidalSupport.HarishChandraForwardProof
Langlands.Representation.CuspidalSupport.HarishChandraStatement
Langlands.Representation.CuspidalSupport.InducedJacquetCount
Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.JacquetLengthDetector
Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement
Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviAssociation
Langlands.Representation.CuspidalSupport.LeviCompactPart
Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.LeviGapVanishing
Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
Langlands.Representation.CuspidalSupport.LeviSplitContraction
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof
Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition
Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
Langlands.Representation.CuspidalSupport.ProperInductionMaps
Langlands.Representation.CuspidalSupport.ProperInductionProof
Langlands.Representation.CuspidalSupport.ProperInductionStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.CuspidalSupport.WholeLeviTransport
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
Langlands.Representation.Derivative.LeftMixedProductHigher
Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof
Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate
Langlands.Representation.Derivative.LeftMixedProductVanishing
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.LeibnizIndices
Langlands.Representation.Derivative.LeibnizPieceCompat
Langlands.Representation.Derivative.LeibnizPositiveGluing
Langlands.Representation.Derivative.LeibnizQuotientPiece
Langlands.Representation.Derivative.LeibnizRankZeroBoundary
Langlands.Representation.Derivative.LeibnizRankZeroGluing
Langlands.Representation.Derivative.LeibnizRestrictionCompat
Langlands.Representation.Derivative.LeibnizRestrictionExact
Langlands.Representation.Derivative.LeibnizZeroFirstPiece
Langlands.Representation.Derivative.LevelCalculus
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicMinusNormalization
Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicPlusNormalization
Langlands.Representation.Derivative.MirabolicProductMinusBoundary
Langlands.Representation.Derivative.MirabolicProductMinusCompatibility
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestriction
Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.MirabolicSmoothPhiPlus
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Derivative.MixedProductRankCast
Langlands.Representation.Derivative.OrderRecursion
Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement
Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
Langlands.Representation.Derivative.PartialDerivativeJacquetLHS
Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.ProductVanishing
Langlands.Representation.Derivative.RankCastCompat
Langlands.Representation.Derivative.RestrictedProductLevel
Langlands.Representation.Derivative.RestrictionBridge
Langlands.Representation.Derivative.RightMixedLevel
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Langlands.Representation.Derivative.RightMixedProductDerivativePositive
Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof
Langlands.Representation.Derivative.RightMixedProductZeroRank
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Derivative.TopLine
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.ComplexTwistFamilies
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Exponents.RealTwistFamilies
Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement
Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
Langlands.Representation.Exponents.WeylBranchPiecesStatement
Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
Langlands.Representation.Filtration.CoinvariantVanishingStatement
Langlands.Representation.Filtration.CommonSubquotientStatement
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement
Langlands.Representation.Filtration.FunctorLengthTwoDetection
Langlands.Representation.Filtration.GluedFamily
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.InvariantBilinear
Langlands.Representation.Filtration.InvariantBilinearBounds
Langlands.Representation.Filtration.InvariantBilinearSubquotientBounds *
Langlands.Representation.Filtration.IrreducibleMultiplicityProof
Langlands.Representation.Filtration.IrreducibleMultiplicityStatement
Langlands.Representation.Filtration.IsoTransport
Langlands.Representation.Filtration.JordanHolderComparisonProof
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.MultiplicityAdditivityProof
Langlands.Representation.Filtration.MultiplicityAdditivityStatement
Langlands.Representation.Filtration.MultiplicityIndependenceProof
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.MultiplicityTransportProof
Langlands.Representation.Filtration.MultiplicityTransportStatement
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.OneStep
Langlands.Representation.Filtration.Precomposition
Langlands.Representation.Filtration.QuasicuspidalVanishingProof
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.QuotientTail
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement
Langlands.Representation.Filtration.SimpleSubquotientFactorProof
Langlands.Representation.Filtration.SimpleSubquotientFactorStatement
Langlands.Representation.Filtration.SmoothDualEvaluation *
Langlands.Representation.Filtration.Splicing
Langlands.Representation.Filtration.Splicing.Basic
Langlands.Representation.Filtration.SubquotientAlgebraProof
Langlands.Representation.Filtration.SubquotientAlgebraStatement
Langlands.Representation.Filtration.SubsingletonProof
Langlands.Representation.Filtration.Transport
Langlands.Representation.Filtration.VanishingStatement
Langlands.Representation.Filtration.ZeroFactorDeletionProof
Langlands.Representation.Filtration.ZeroFactorDeletionStatement
Langlands.Representation.Geometric.BlockIntersectionSplitting
Langlands.Representation.Geometric.BlockSixDecomposableProof
Langlands.Representation.Geometric.BlockSixDecomposableStatement
Langlands.Representation.Geometric.BruhatDescent
Langlands.Representation.Geometric.BruhatMatrixExistenceProof
Langlands.Representation.Geometric.BruhatMatrixStatement
Langlands.Representation.Geometric.BruhatWeylReflectionProof
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CoarseLeviReversal
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CompactSmoothComparison
Langlands.Representation.Geometric.ConditionalAssembly
Langlands.Representation.Geometric.CorrectionSubgroupCoordinates
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.CosetOrbitOrdering
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.GeneralCorrectionCharacters
Langlands.Representation.Geometric.GeneralIntersectionNormalizers
Langlands.Representation.Geometric.GeneralIntersections
Langlands.Representation.Geometric.GeometricLemmaProof
Langlands.Representation.Geometric.GeometricLemmaStatement
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement
Langlands.Representation.Geometric.IntersectionLeviModulusBalance
Langlands.Representation.Geometric.IntersectionTransport
Langlands.Representation.Geometric.MonotoneBlocksProof
Langlands.Representation.Geometric.MonotoneBlocksStatement
Langlands.Representation.Geometric.OrbitRepresentatives
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Geometric.PadicCorrectionCancellationProof
Langlands.Representation.Geometric.PadicCorrectionCancellationStatement
Langlands.Representation.Geometric.PadicParabolicBruhatProof
Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison
Langlands.Representation.Geometric.ParabolicOrbitCompactComparison
Langlands.Representation.Geometric.ParabolicOrbitComparisonData
Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
Langlands.Representation.Geometric.ParabolicOrbitHaarRatio
Langlands.Representation.Geometric.ParabolicOrbitHaarTransport
Langlands.Representation.Geometric.ParabolicOrbitInductionTransport
Langlands.Representation.Geometric.ParabolicOrbitJacquet
Langlands.Representation.Geometric.ParabolicOrbitJacquetProof
Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement
Langlands.Representation.Geometric.ParabolicOrbitMeasureData
Langlands.Representation.Geometric.ParabolicOrbitNestedAction
Langlands.Representation.Geometric.ParabolicOrbitNormalization
Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
Langlands.Representation.Geometric.ParabolicOrbitSectionComparison
Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
Langlands.Representation.Geometric.ParabolicSupportFiltration
Langlands.Representation.Geometric.ParabolicSupportGradedProof
Langlands.Representation.Geometric.ParabolicSupportGradedStatement
Langlands.Representation.Geometric.ParabolicSupportJacquetProof
Langlands.Representation.Geometric.ParabolicSupportJacquetStatement
Langlands.Representation.Geometric.ParabolicSupportTransport
Langlands.Representation.Geometric.RefinedPositiveCharacter
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.RefinementUniqueness
Langlands.Representation.Geometric.SmoothSupportFiltration
Langlands.Representation.Geometric.StandardIntersectionsProof
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Hecke.ActionIntegrand
Langlands.Representation.Hecke.ActionLocalUnits
Langlands.Representation.Hecke.ActionProjection
Langlands.Representation.Hecke.AntiPullback
Langlands.Representation.Hecke.CommonInvarianceProof
Langlands.Representation.Hecke.CommonInvarianceStatement
Langlands.Representation.Hecke.Convolution
Langlands.Representation.Hecke.Corner
Langlands.Representation.Hecke.CornerAction
Langlands.Representation.Hecke.CornerDetermination
Langlands.Representation.Hecke.DoubleCoset
Langlands.Representation.Hecke.DoubleCosetSandwich
Langlands.Representation.Hecke.FiniteRankAction
Langlands.Representation.Hecke.IntegratedAction
Langlands.Representation.Hecke.IntegratedConvolution
Langlands.Representation.Hecke.NormalizedIndicator
Langlands.Representation.Hecke.SmoothTranspose
Langlands.Representation.Hecke.TestFunction
Langlands.Representation.Induction.BinaryPositiveCompact
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockCharacterAbsorption
Langlands.Representation.Induction.BlockEquivalence
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactBilinearPairing
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactIntegralForm *
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactPairingDuality
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactScalarProof
Langlands.Representation.Induction.CompactScalarStatement
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.CompactTransitivityProof
Langlands.Representation.Induction.CompactTransitivityStatement
Langlands.Representation.Induction.ConjugateParabolic
Langlands.Representation.Induction.CovariantRescaling *
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.FiniteProductTensor
Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement
Langlands.Representation.Induction.HeterogeneousConstruction
Langlands.Representation.Induction.HeterogeneousPairs
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.NormalizedIntegralForm *
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.OppositeProductReversalProof
Langlands.Representation.Induction.OppositeProductReversalStatement
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.PiScalarIntegral
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.SplitKernelCharacter
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelHaarTrivial
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesCharacterComparison
Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement
Langlands.Representation.Induction.SplitStagesCharacterIntegrand
Langlands.Representation.Induction.SplitStagesComparison
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.BlockCompressionProof
Langlands.Representation.Jacquet.BlockCompressionStatement
Langlands.Representation.Jacquet.BlockPowerKernelProof
Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
Langlands.Representation.Jacquet.CanonicalLiftDefinitions
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.OppositeCanonicalLiftProof
Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.ReciprocityProof
Langlands.Representation.Jacquet.ReciprocityStatement
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.RefinedOppositeCompressionProof
Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement
Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof
Langlands.Representation.Jacquet.RefinedOppositeStableImageProof
Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.Jacquet.StablePairingProof
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.HermitianProduct *
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.MatrixCoefficient.NormRegularityProof *
Langlands.Representation.MatrixCoefficient.NormRegularityStatement *
Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.HeadTailProductInduction
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionSubrepresentation
Langlands.Representation.Parabolic.InverseTransposeProductProof *
Langlands.Representation.Parabolic.InverseTransposeProductStatement *
Langlands.Representation.Parabolic.LeviBridges
Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
Langlands.Representation.Parabolic.NaturalFirstAdjointness
Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
Langlands.Representation.Parabolic.NaturalInductionDualityProof
Langlands.Representation.Parabolic.NaturalInductionDualityStatement
Langlands.Representation.Parabolic.NaturalJacquetDualityProof
Langlands.Representation.Parabolic.NaturalJacquetDualityStatement
Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedCompatibilityStatement *
Langlands.Representation.Parabolic.NormalizedInductionStatement
Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
Langlands.Representation.Parabolic.NormalizedJacquetStatement
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement
Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
Langlands.Representation.Parabolic.OrderedProductRegroupingProof
Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
Langlands.Representation.Parabolic.ProductInductionSubrepresentation
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionAdmissibility
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.RegroupingFactorEquivalences
Langlands.Representation.Parabolic.SecondAdjointnessAssembly
Langlands.Representation.Parabolic.SecondAdjointnessProof
Langlands.Representation.Parabolic.SecondAdjointnessStatement
Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.ThreeBlockCarrierComparison
Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
Langlands.Representation.Parabolic.ThreeBlockUniverseReduction
Langlands.Representation.Parabolic.UnipotentFiniteContainment
Langlands.Representation.RankinSelberg.AnalyticStatement
Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly
Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction
Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement
Langlands.Representation.RankinSelberg.FunctionalEquationStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.HaarSymmetriesProof
Langlands.Representation.RankinSelberg.HaarSymmetriesStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.LocalFactor
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.RationalContinuation
Langlands.Representation.RankinSelberg.RationalZeta
Langlands.Representation.RankinSelberg.TwistInvariance
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
Langlands.Representation.Schur.CountableDimensionProof
Langlands.Representation.Schur.CountableDimensionStatement
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Admissibility.Extension
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement
Langlands.Representation.Smooth.Contragredient.HomDualityProof
Langlands.Representation.Smooth.Contragredient.HomDualityStatement
Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
Langlands.Representation.Smooth.Factorization.TwoFactorStatement
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.Detection
Langlands.Representation.Smooth.FixedVectors.FiniteTypes
Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
Langlands.Representation.Smooth.FixedVectors.GenerationInheritance
Langlands.Representation.Smooth.FixedVectors.GenerationInheritanceStatement
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.GroupEquivalence
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Tensor.CoinvariantReflection
Langlands.Representation.Tensor.ExternalFiltration
Langlands.Representation.Tensor.ExternalSubquotient
Langlands.Representation.Tensor.ExternalSubrepresentation
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.FlattenedGLRefinement
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Tensor.ProductFiltration
Langlands.Representation.Tensor.SmoothDual
Langlands.Representation.Tensor.SmoothDualInjectivityProof
Langlands.Representation.Tensor.SmoothDualInjectivityStatement
Langlands.Representation.Tensor.SmoothDualSurjectivityProof
Langlands.Representation.Tensor.SmoothDualSurjectivityStatement
Langlands.Representation.Tensor.SmoothSubquotients
Langlands.Representation.Tensor.UnitaryProof *
Langlands.Representation.Tensor.UnitaryStatement *
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.DualProof
Langlands.Representation.Twist.DualStatement
Langlands.Representation.Twist.LeviComplexPower
Langlands.Representation.Twist.LeviRealPower
Langlands.Representation.Twist.PullbackProof *
Langlands.Representation.Twist.PullbackStatement *
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothPartDefinitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Unitary.CentralCharacterProof *
Langlands.Representation.Unitary.CentralCharacterStatement *
Langlands.Representation.Unitary.HermitianDual *
Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof *
Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement *
Langlands.Representation.Unitary.SquareIntegrableProof *
Langlands.Representation.Unitary.SquareIntegrableStatement *
Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof *
Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement *
Langlands.Representation.Unitary.Twist *
Langlands.Representation.Unitary.UnitarizabilityContinuationProof *
Langlands.Representation.Unitary.UnitarizabilityContinuationStatement *
Langlands.Representation.Unramified.Eigenvalues
Langlands.Representation.Unramified.HeckeOperators
Langlands.Representation.Unramified.PrincipalSeries
Langlands.Representation.Unramified.SphericalClassificationStatement
Langlands.Representation.Unramified.SphericalConstituentExistenceProof
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.AlgebraicTwist
Langlands.Representation.Whittaker.BruhatCellDistribution
Langlands.Representation.Whittaker.BruhatCellFactorizationProof
Langlands.Representation.Whittaker.BruhatCellFactorizationStatement
Langlands.Representation.Whittaker.BruhatCellInvarianceProof
Langlands.Representation.Whittaker.BruhatCellInvarianceStatement
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingProof
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement
Langlands.Representation.Whittaker.BruhatCellVanishingProof
Langlands.Representation.Whittaker.BruhatCellVanishingStatement
Langlands.Representation.Whittaker.BruhatCompatibleSupportProof
Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement
Langlands.Representation.Whittaker.BruhatFiberAverage
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement
Langlands.Representation.Whittaker.BruhatHaarMeasureProof
Langlands.Representation.Whittaker.BruhatHaarMeasureStatement
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement
Langlands.Representation.Whittaker.BundledDualTransport
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.CoefficientDistribution
Langlands.Representation.Whittaker.CompatibleMonomialFixedProof
Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement
Langlands.Representation.Whittaker.CompatibleTorus
Langlands.Representation.Whittaker.Distribution
Langlands.Representation.Whittaker.DistributionInvarianceProof
Langlands.Representation.Whittaker.DistributionInvarianceStatement
Langlands.Representation.Whittaker.DualTransform
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.GeneralizedCoefficient
Langlands.Representation.Whittaker.GeneralizedCoefficientDescent
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement
Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation
Langlands.Representation.Whittaker.GenericDualTransport
Langlands.Representation.Whittaker.Iwasawa
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.MultiplicityOneProof
Langlands.Representation.Whittaker.MultiplicityOneStatement
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Representation.Whittaker.Twist
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.GroupAction.FiniteOrbitProof
Langlands.Topology.GroupAction.FiniteOrbitStatement
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.VirtualRepresentation.Exact
Langlands.VirtualRepresentation.ExactTwist
Langlands.VirtualRepresentation.Integral
Langlands.Weil.Algebraic
Langlands.Weil.AlgebraicProof
Langlands.Weil.Local.Assembly
Langlands.Weil.Local.DegreeCharacters
Langlands.Weil.Local.Parameters
Langlands.Weil.Local.ResidueCharacters
Langlands.Weil.Pullback
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.CharacterLine
Langlands.Weil.Representation.Continuity
Langlands.Weil.Representation.ContinuityProof
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.DirectSum
Langlands.Weil.Representation.Dual
Langlands.Weil.Representation.DualClasses
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.OperationClosureProof
Langlands.Weil.Representation.Operations
Langlands.Weil.Representation.Predicates
Langlands.Weil.Representation.Twist
Langlands.Weil.Representation.TwistClasses
Langlands.Weil.Representation.TwistProperties
Langlands.Weil.Topology
Langlands.Weil.TopologyProof
Langlands.WeilDeligne.Basic
Langlands.WeilDeligne.DirectSum
Langlands.WeilDeligne.Dual
Langlands.WeilDeligne.ParameterRelations
Langlands.WeilDeligne.Parameters
Langlands.WeilDeligne.Twist
```

## Appendix: external import roots

These are the direct non-project imports in the project closure. Mathlib and
Lean internals are not traversed.

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.Bilinear
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.Algebra.Subalgebra.Lattice
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Group.List.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.DirectSum.Module
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Action.Hom
Mathlib.Algebra.Group.Action.Opposite
Mathlib.Algebra.Group.AddChar
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.CharacterModule
Mathlib.Algebra.Module.LinearMap.FiniteRange
Mathlib.Algebra.Module.Opposite
Mathlib.Algebra.Module.PID
Mathlib.Algebra.Module.Projective
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.FieldDivision
Mathlib.Algebra.Polynomial.Laurent
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Polynomial.Module.AEval
Mathlib.Algebra.Polynomial.Module.FiniteDimensional
Mathlib.Algebra.Polynomial.Roots
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.Fourier.FourierTransform
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.InnerProductSpace.Dual
Mathlib.Analysis.InnerProductSpace.TensorProduct
Mathlib.Analysis.Matrix.Hermitian
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.MeanInequalitiesPow
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Log.Base
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.Continuity
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Sqrt
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.Basic
Mathlib.Data.ENat.BigOperators
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Basic
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Finset.NatAntidiagonal
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Fintype.Sum
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.Interval
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.List.Pairwise
Mathlib.Data.Matrix.Basic
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.Data.PNat.Basic
Mathlib.Data.Set.Card
Mathlib.Data.Set.Finite.Basic
Mathlib.Data.Sym.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.AbsoluteGaloisGroup
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.Finite.Extension
Mathlib.FieldTheory.Galois.Profinite
Mathlib.FieldTheory.PrimitiveElement
Mathlib.FieldTheory.RatFunc.AsPolynomial
Mathlib.GroupTheory.Abelianization.Defs
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.FiniteIndexNormalSubgroup
Mathlib.GroupTheory.GroupAction.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Defs
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.OrderOfElement
Mathlib.GroupTheory.QuotientGroup.Defs
Mathlib.GroupTheory.Subgroup.Center
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.GroupTheory.Transfer
Mathlib.LinearAlgebra.AffineSpace.AffineMap
Mathlib.LinearAlgebra.AnnihilatingPolynomial
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.BilinearForm.Properties
Mathlib.LinearAlgebra.BilinearMap
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dimension.StrongRankCondition
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Defs
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.Eigenspace.Pi
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
Mathlib.LinearAlgebra.Finsupp.LinearCombination
Mathlib.LinearAlgebra.Finsupp.VectorSpace
Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.BilinearForm
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.NonsingularInverse
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.PosDef
Mathlib.LinearAlgebra.Matrix.Rank
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Dual
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.Quotient.Basic
Mathlib.LinearAlgebra.Semisimple
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.Finiteness
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.LinearAlgebra.Trace
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.L2Space
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Function.LpSpace.Indicator
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.MeasurableEquiv
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Prod
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.CompactlyGenerated.Basic
Mathlib.Order.Hom.Set
Mathlib.Order.Interval.Finset.Fin
Mathlib.Order.Interval.Set.Infinite
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Equiv
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Adjoin.Basic
Mathlib.RingTheory.Adjoin.Polynomial.Basic
Mathlib.RingTheory.AdjoinRoot
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.FractionalIdeal.Operations
Mathlib.RingTheory.Ideal.Quotient.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Jacobson.Semiprimary
Mathlib.RingTheory.Length
Mathlib.RingTheory.Localization.Ideal
Mathlib.RingTheory.Nakayama
Mathlib.RingTheory.Nilpotent.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Norm.Transitivity
Mathlib.RingTheory.Polynomial.Basic
Mathlib.RingTheory.Polynomial.UniqueFactorization
Mathlib.RingTheory.PowerBasis
Mathlib.RingTheory.PrincipalIdealDomain
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Extension
Mathlib.RingTheory.Valuation.Integral
Mathlib.RingTheory.Valuation.LocalSubring
Mathlib.RingTheory.Valuation.RamificationGroup
Mathlib.Tactic
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
Mathlib.Tactic.NoncommRing
Mathlib.Tactic.NormNum
Mathlib.Tactic.Ring
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
Mathlib.Topology.Algebra.ClopenNhdofOne
Mathlib.Topology.Algebra.ConstMulAction
Mathlib.Topology.Algebra.Constructions
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Field
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.ClosedSubgroup
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.GroupWithZero
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.MvPolynomial
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Ring.Ideal
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.Lemmas
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.Clopen
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Defs
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.Int
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.MetricSpace.ProperSpace
Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
Mathlib.Topology.Order.Compact
Mathlib.Topology.Separation.Profinite
Mathlib.Topology.Sequences
Mathlib.Topology.UrysohnsLemma
```
