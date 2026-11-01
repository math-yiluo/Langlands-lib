# The induction on the number of segments for Zelevinsky 6.2

Module
`Langlands.Representation.Classification.SegmentSocleProductHomogeneityInduction`,
namespace `Langlands.Classification.SegmentSocleProductHomogeneityInduction`.

Zelevinsky's Theorem 6.2 (`zelevinsky-1980-induced-ii`, printed p.188) says:
let `Δ_1, …, Δ_r` be segments with `Δ_i = [ρ_i, ρ'_i]`, and suppose that
`ρ_j ≠ ν ρ'_i` whenever `i < j`. Then `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is homogeneous. In
the published target `SegmentSocleProductHomogeneity` the condition reads
`(d.segments j).base ≠ ((d.segments i).last).twist 1` for `i < j`, and the
conclusion is `IsGeneralLinearHomogeneous T ψ d.induced`, i.e. the restriction
to the mirabolic subgroup is homogeneous.

The main theorem of this module, `homogeneous_of_caseTwo`, proves this
conclusion by induction on the number of segments. It takes the lower
propositions of the proof as explicit hypotheses, and it also takes Case 2 of
Ze80 §6.3 as an explicit hypothesis `hC2`, phrased with the predicate
`CaseTwoExclusion` defined here. The companion module
`SegmentSocleProductCaseTwo` proves `hC2` from its own lower hypotheses. This
module does not prove Theorem 6.2 by itself.

## Hypotheses of `homogeneous_of_caseTwo`

None of these is proved here. All except `hH` are published Library
propositions. `hH` is written out inline: it is the instance at the fixed `ψ`
of Ze80 Proposition 5.3, whose statement is not yet in the Library (statement
task `49d8eea3-1f52-4505-bfce-d76bf8ed5b8a`).

| Hypothesis | Proposition | Source |
| --- | --- | --- |
| `hE` | `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T` | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) |
| `hD` | `RightMixedProductPhiMinusDetection.{uF, max uF uV} F T` | BZ77 4.13(d) |
| `hS` | `MirabolicProductMinus.RightPhiShortExact.{uF, max uF uV} F T` | BZ77 4.13(c) |
| `hB` | `MirabolicProductMinus.RightPhiBoundary.{uF, max uF uV} F T` | BZ77 4.13(c), `P_1` boundary |
| `hR` | `MirabolicProductRestrictionStatement.{uF, max uF uV} F T` | BZ77 4.13(a) |
| `hLD` | `LeftMixedProductDerivative.{uF, max uF uV} F T` | BZ77 4.14(a) |
| `hH` | inline, see below | Ze80 5.3 |
| `h35` | `SegmentSocleDerivatives.{uF, uV} F T` | Ze80 3.5 |
| `hC2` | inline, see below | Case 2 of Ze80 §6.3 |

The modules are `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`
(`hE`), `…Derivative.MixedProductDerivativeStatement` (`hD`, `hLD`),
`…Derivative.MirabolicProductMinusCompatibilityStatement` (`hS`, `hB`),
`…Derivative.MirabolicProductRestrictionStatement` (`hR`) and
`…Classification.SegmentSocleDerivativesStatement` (`h35`). Only the first
conjunct of `h35` is used: a segment socle `⟨Δ⟩` has no nonzero derivative of
positive order other than `Δ.rank`.

`hH` (Ze80 5.3 at `ψ`, carriers in `Type (max uF uV)`):

```lean
∀ (k r : ℕ) (ρ : SmoothRep ℂ (GeneralLinear k F.Carrier))
  (τ : SmoothRep ℂ (mirabolic r F.Carrier)),
  IsHomogeneous T ψ τ → IsHomogeneous T ψ ((T.leftMixedProductFunctor k r).obj (ρ, τ))
```

In words: the left mixed product of any representation of `GL_k` with a
homogeneous representation of `P_(r+1)` is homogeneous. This is exactly the
body, at `ψ`, of the draft statement `LeftMixedProductHomogeneity` of task
`49d8eea3`. The planned final assembly (not part of this submission) will
pass that statement's instance at `ψ`.

`hC2`: for every datum `d` with `d.length = k + 2`, `d.HasSegmentSocles`, the
endpoint condition, head rank `m + 1`, tail rank `n + 1`, and homogeneous
restriction of the tail product, `CaseTwoExclusion T d h m n ha hb` holds.

## Provenance

Ze80 §6.3 (printed pp.188–189) proves Theorem 6.2 "by arguments similar to
those in [I], 4.15", i.e. BZ77 4.15 (`bernstein-zelevinsky-1977-induced-i`,
printed p.459). It lists the modifications: replace `ρ_1` by `⟨Δ_1⟩` and
BZ77 4.4 by Ze80 3.5; Case 1 uses 5.3; Case 2 uses the reasoning of Ze80 4.5.
The argument is an induction on `r`, with `π = ⟨Δ_1⟩ × π°` and
`π° = ⟨Δ_2⟩ × ⋯ × ⟨Δ_r⟩`.

This module is internal derived material. It formalizes that induction: the
base case `r = 1` (from Ze80 3.5) and the step through
`RestrictedProductLevel.isHomogeneous_restrictedProduct`. That helper carries
out Case 1 and the case split. Ze80 states Case 1 as a contrapositive ("one
concludes now that `⟨Δ_1⁻⟩ × π°|P` is not homogeneous … By 5.3 `π°|P` is not
homogeneous"). The Lean proof is the direct form: the homogeneity of `π°|P`
(induction) gives that of `⟨Δ_1⟩^(Δ_1.rank) × π°|P` by 5.3. The predicate
`CaseTwoExclusion`, the bridge lemmas and the datum lemmas are Lean packaging.

## Adapted code and attribution

The proof of `nonempty_iso_single` is adapted from the definition
`SegmentProductDatum.ofSingleSegmentInducedEquiv` in
`Langlands/Representation/Classification/JuxtaposedUnionDatum.lean`
(lines 120–140 at Library commit `a9fde216`), by Worker 167 and Worker 1032.
Both are coauthors of this submission. The source builds the equivalence for
the datum `ofSingleSegment U π hdegree` from
`T.singleBlockNormalizedProductEquiv`, followed by the identity on `π` and the
identification of the reindexing of `GL_n` with the identity. The adaptation
keeps these steps. It applies them to an arbitrary datum of length one, after
destructuring it and substituting `l = 1` and the degree equation. It
reindexes along `e.shape.singleBlock_size` instead of `rfl`, and it returns
`Nonempty` of an isomorphism of smooth representations (via
`SmoothRep.mkIso`). The code is adapted rather than imported because the
source applies only to data of the form `ofSingleSegment`; it also keeps
`JuxtaposedUnionDatum` out of the import closure audited below.

The rest of this module and `SegmentSocleProductCaseTwo` is by Worker 1070.
The submission also builds on the helper modules of the Derivative and
Classification helper candidates named in the import audit; their
Markdown records their own adapted code and coauthors.

## Conventions

`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}`, `T : F.TopologicalData` and
`ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology` are fixed, with
`T.topology` installed. `d : SegmentProductDatum.{uV, uF} T M` is a published
segment-product datum; its blocks and `d.induced` have carriers in
`Type (max uF uV)`. `tail d h`, `d.shape.headIndex h`, `d.shape.headRank h`
and `d.shape.tailRank h` are as in `SegmentProductSplit` (for
`h : d.length = k + 2`). `generalLinearRankCast T h` transports a
representation of `GL_a` to `GL_b` along `h : a = b`. `restrictedProduct T m n`
and `restrictionQuotient T m n` are the published functors of
`MirabolicProductRestriction` giving `(D × P)|P` and its quotient
`D × (P|P)` (BZ77 4.13(a)), both on `mirabolic (m+n+1)`.

## Declarations

### Bridges (section `Bridges`)

- `single_order_of_iso c h A X e hA`: let `h : a = N + 1`, `A` on `GL_a` and
  `X ≅ (generalLinearRankCast T h).obj A` on `GL_(N+1)`. If every derivative of
  `A` of positive order `k ≠ c` vanishes, then every nonzero derivative order
  `j` of `X|P` (`HasNonzeroDerivative`) equals `c`. Proof:
  `RestrictionBridge.nontrivial_generalLinearDerivative_iff` identifies the
  order-`j` derivative of `X|P` with the one of `X`, which is isomorphic to
  the one of `A`.
- `isGeneralLinearHomogeneous_of_restrictedProduct ha hb e hM A B X i hH`: if
  `X ≅ (generalLinearRankCast T e).obj (A × B)` and the restricted product of
  the rank transports of `A`, `B` is homogeneous, then the rank transport of
  `X` to `GL_(N+1)` is `IsGeneralLinearHomogeneous`
  (`LevelCalculus.isHomogeneous_of_iso`).

### Data (section `Data`)

- `nonempty_iso_single d h hdeg`: for a datum of length 1 with
  `hdeg : (d.segments 0).degree = n`, `d.induced` is isomorphic to the rank
  transport of its single block. Proof: the published
  `singleBlockNormalizedProductEquiv` and the identity reindexing of `GL_n`.
- `tail_endpoint d h hsep`: the endpoint condition passes to `tail d h`.
- `head_endpoint d h hsep`: no segment of `tail d h` begins at
  `ν · e(Δ_1)`, where `Δ_1` is the first segment.
- `ofFn_segments_eq_cons d h`: the segment list of `d` is `Δ_1` followed by
  the segment list of `tail d h`.
- `cuspidalContent_eq d`: `d.multisegment.cuspidalContent` is the sum of the
  cuspidal contents of the segments of `d`, in list form.

### The predicate (section `Induction`)

`CaseTwoExclusion T d h m n ha hb` (definition, the entry declaration), for
`h : d.length = k + 2`, `ha : d.shape.headRank h = m + 1` and
`hb : d.shape.tailRank h = n + 1`. Write `D` and `P` for the rank transports
of the first block `⟨Δ_1⟩` to `GL_(m+1)` and of `(tail d h).induced` to
`GL_(n+1)`. The predicate says: no nontrivial `W` on `mirabolic (m+n+1)`
(carrier in `Type (max uF uV)`) has both an injective intertwiner
`f : W ⟶ (restrictedProduct T m n).obj (D, P)` and an injective intertwiner
`g : W ⟶ (restrictionQuotient T m n).obj (D, P)`.

This is the `hC2` premise of `RestrictedProductLevel.isHomogeneous_restrictedProduct`
for this pair `(D, P)`. In Ze80's notation, no nonzero submodule of `π|P`
embeds into the quotient `⟨Δ_1⟩ × (π°|P)` of BZ77 4.13(a). This is Case 2
of BZ77 4.15, which Ze80 shows to be impossible.

### The induction

`homogeneous_of_caseTwo hC2 ℓ M d N hM hl hd hsep` (hypotheses
`hE hD hS hB hR hLD hH h35` from the section): for every `ℓ`, every datum `d`
of rank `M = N + 1` with `d.length = ℓ + 1`, `d.HasSegmentSocles` and the
endpoint condition,
`IsGeneralLinearHomogeneous T ψ ((generalLinearRankCast T hM).obj d.induced)`.

Proof by induction on `ℓ`, for all `M`, `d` and `N`.

- `ℓ = 0`: `d` has one segment `Δ`, of degree `M` (`d.degree_sum`). By
  `nonempty_iso_single`, `d.induced` is the rank transport of `⟨Δ⟩`. By the
  first conjunct of `h35`, `⟨Δ⟩` has no nonzero derivative of positive order
  other than `Δ.rank`. So `single_order_of_iso` shows that every nonzero
  derivative order of the restriction is `Δ.rank`, and
  `RestrictionBridge.isHomogeneous_of_single_order` (with `hE`) gives
  homogeneity.
- `ℓ + 1`: then `d.length = ℓ + 2`. Write the head and tail ranks as `m + 1`
  and `n + 1` (both positive). `SegmentProductSplit.nonempty_iso_binary`
  identifies `d.induced` with the rank transport of `D × P`, where
  `D = ⟨Δ_1⟩` and `P = (tail d h).induced`. The tail satisfies the hypotheses
  (`tail_hasSegmentSocles`, `tail_endpoint`), so the induction hypothesis
  gives `hP`: `P|P` is homogeneous. Let `s + 1 = Δ_1.rank` and
  `n' = m + 1 - Δ_1.rank`, so `m = n' + s`. Apply
  `RestrictedProductLevel.isHomogeneous_restrictedProduct` with
  `hE hD hS hB hR hLD`, and supply its three premises:
  - `hDj`, every nonzero derivative order of `D|P` is `Δ_1.rank`: from `h35`
    through `single_order_of_iso`;
  - `hY`, the left mixed product of `(D|P)^(Δ_1.rank)` with `P|P` is
    homogeneous: `hH` applied to `hP`;
  - the Case 2 exclusion: `hC2` applied to `d`, with `hP`.

  Finally `isGeneralLinearHomogeneous_of_restrictedProduct` transports the
  homogeneity back to `d.induced`.

## Import audit

This module is submitted together with `SegmentSocleProductCaseTwo`. The two
modules use eight helper modules. Five are published in the Library
(`Derivative.LevelCalculus`, `ProductVanishing`, `RestrictionBridge`,
`RightMixedLevel`, `RestrictedProductLevel`; accepted candidate
`6ded142e-bf04-4d18-8956-a5850e80410b`, published at Library commit
`7114a390`). Three are in the Classification helper candidate
`5440c02b-fc2d-4abe-bbe8-6cd061c6a683`
(`Classification.SegmentProductCuspidalEmbedding`, `SegmentProductSplit`,
`SegmentContentShift`), which replaces the rejected candidate `27aa4ec1` with
the same Lean files. This candidate must be published after `5440c02b`.

On Library base `2d873b3c`, the transitive project import closure of the two
modules has 585 modules: the two modules themselves, the three Classification
helper modules above, and 580 published Library modules (among them the five
Derivative helpers).

The direct project imports of the two modules are five of the helpers
(`RestrictedProductLevel`, `RestrictionBridge`, `SegmentProductSplit`,
`SegmentProductCuspidalEmbedding`, `SegmentContentShift`; the other three
enter transitively) and the following published modules: the target statement
module `SegmentSocleProductHomogeneityStatement` (no proposition of it is
assumed), `SegmentSocleDerivativesStatement` (for `h35` here and `hF` in
`SegmentSocleProductCaseTwo`), `Induction.SingleBlock`,
`Classification.SegmentCuspidalContent` and
`Classification.CuspidalIntegralTwistFreenessProof`. The last is the one
published proof called directly: `cuspidalIntegralTwistFreeness`, in
`SegmentSocleProductCaseTwo`. It imports only its statement module,
`Smooth.Schur.Proof` and `LocalField.Uniformizer`, and it adds no other
module to the closure.

Some classification statement modules enter the closure through the published
Ze80 3.5 statement module. `SegmentSocleDerivativesStatement` imports
`SingletonSegmentSocle`, which imports `SegmentSocleProductData`, which imports
`OrderedMultisegmentHeadReduction`. That module imports four statement
modules: `MultisegmentClassificationStatement`,
`OrderedSegmentSquareIntegrableConversionStatement`,
`TemperedBlockStatement` and `RegularLanglandsStatement`. These four only
define propositions, and `OrderedMultisegmentHeadReduction` only proves
implications that take such propositions as hypotheses. No declaration of
these five modules is used here, and none of their propositions is assumed
or proved.

The closure contains no proof module for the conclusions excluded by task
`b711af72` (ordered-socle existence, socle exhaustion, segment-socle product
irreducibility, swaps or commutation, special-head results, quotient
coverage, tempered-block uniqueness, square-integrable or regular
exhaustion, Langlands classification, ordered special-segment conversion,
special square-integrability, generic uniqueness, the segment Jacquet
formulas). It contains no two-supercuspidal product module. The Ze80 3.5
statement `SegmentSocleDerivatives` and highest-derivative statement
`SegmentSocleProductHighestDerivative` are used only as hypotheses; the task
objective names Ze80 3.5 as an input of 6.3.
