# BZ77 Theorem 4.11 for ordered cuspidal products (proof)

Authors: Worker 818 (this pair); Worker 1166 (the helper pair
`OrderedCuspidalProductHeadShift`); Worker 1168 (the proof in the helper pair
`OrderedCuspidalProductTwistOne`).

This module proves the theorem
`Langlands.Derivative.orderedCuspidalProductNoDegenerateSubmodules` (line 692). Its
type is exactly the published proposition
`Langlands.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF,uV} F T` of
module `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement`
(statement artifact `bcda0d7d-48a7-4a3a-8b0e-ad48b26c9c68`, task
`12eb3790-50bc-4727-acc4-14ced067d333`):

```lean
theorem orderedCuspidalProductNoDegenerateSubmodules {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    OrderedCuspidalProductNoDegenerateSubmodules.{uF, uV} F T
```

This is Bernstein–Zelevinsky 1977, Theorem 4.11, sufficient direction (printed
p. 456, one-based PDF p. 17). The target pair and every pair it imports are
unchanged. The module adds no axioms and has no `sorry` or `admit`. The theorem
has no premise beyond the target's own telescope. Its universe parameters are
exactly `uF uV`. A Lake build of the workspace has 0 errors and 0 warnings, and
`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. All
auxiliary declarations are in the namespace
`Langlands.Derivative.OrderedCuspidalProductNondegeneracy`. The auxiliary lemmas
are stated for an arbitrary carrier universe `uW` and are applied at the
universes given below.

The file sets `set_option backward.isDefEq.respectTransparency.types false`
(line 24). This elaborator option controls how definitions are unfolded during
unification. It is set in the same way in 1129 Library modules at the audit base,
among them `Derivative.LevelCalculus` and `Derivative.RestrictedProductLevel`. It
adds no axiom, and the kernel checks the resulting terms as usual.

## The statement proved

Fix a prime `p`, `F : PadicField.{uF} p` and topological data `T`. All topology
is `T.topology`. The proposition quantifies over:

- every nontrivial continuous unitary additive character `ψ` (no existence of a
  character is assumed);
- every `N : ℕ`, including `N = 0`, that is `GL_1` and its mirabolic `P_1`;
- every block shape `B : GeneralLinear.BlockShape (N + 1)`;
- every family `A i : SupercuspidalRep.{uF,uV} (n := B.size i)` of actual
  irreducible supercuspidal representations, with carriers in universe `uV`.

The only hypothesis on `A` is the order condition: for `i < j`, the rank-indexed
class `⟨B.size j, (A j).isoClass⟩` differs from
`⟨B.size i, T.supercuspidalClassRealPowerTwist (B.size i) 1 (A i).isoClass⟩`, that
is, `A j ≇ ν A i` with `ν = |det|^1`. Equal classes may repeat, block ranks are
arbitrary, and `A i ≅ ν A j` with `i < j` is allowed. Let
`Π = (T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)` and
`R = (Derivative.generalLinearRestriction T N).obj Π`, the restriction to
`P_(N+1)`. The conclusion holds for every subrepresentation `U` of `R` with
`U ≠ ⊥`, without any irreducibility, finite generation, admissibility or
finite-length premise: the derivative
`(Derivative.mirabolicDerivativeOfOrder T ψ N (N + 1) _).obj (SmoothRep.subrepresentation R U)`
of top order `N + 1` is `Nontrivial`.

## Normalizations and universes

The product is the Library's normalized block induction
`T.normalizedProductInductionFunctor B`. It is upper-block induction normalized by
the positive half-modulus `T.leviModulus B`. The binary product
`T.binaryNormalizedProductFunctor a b` and its identification with the two-block
product (`binaryNormalizedProductPositiveIso`) are the Library's, and so is the
head/tail regrouping `headTailProductInductionIso`. The derivatives are the
Library's `mirabolicDerivativeOfOrder` (iterates of the determinant
inverse-half normalized `Ψ⁻`/`Φ⁻`) and `generalLinearDerivative`. The published
bridge `RestrictionBridge.generalLinearDerivative_succ_obj_eq` identifies the
`GL` derivative of positive order with the mirabolic derivative of the
restriction. The twist `ν` is the residue-normalized `|det|^1`, both in the order
condition and in `CuspidalDatum.twist 1`, which the published Lemma 4.7(b) uses.

Every published input below (BZ77 §4.4, 4.5/4.6, 4.13, 4.14, Lemma 4.7(b),
derivative detection and exactness, and Zelevinsky 1980 Proposition 5.3) is stated
for these same functors, so no source normalization is re-derived. The argument
uses only vanishing, nonvanishing, dimensions and injectivity of derivatives.
None of these depends on a normalizing character. So the Haar comparisons
`glBlockModulusHaar`, `psiMinusHaarInverseHalf_eq` and `phiMinusHaarInverseHalf_eq`,
which the target Markdown cites, are not needed and are not imported.

The universes `uF` (field) and `uV` (block carriers) are independent. `Π`, `R`,
`U` and all derivatives have carriers in `max uF uV`. When the product is split,
the head block enters as `SmoothRep.universeLift.{uF} (A i₀).obj`, with carrier
in `max uF uV`, and the product of the other blocks has carrier `max uF uV`.
Published inputs are used at the universes `.{uF, max uF uV}`. These are
`Mirabolic.minusExactness`, `leftMixedProductDerivative`,
`leftMixedProductHomogeneity`, `rightMixedProductPhiMinusDetection`,
`mirabolicProductMinusCompatibility`, `mirabolicProductRestriction` and
`Classification.supercuspidalDerivatives` in the binary step. In the auxiliary
lemmas, `supercuspidalDerivatives` and `generalLinearDerivativeLeibnizFiltration`
are used at `.{uF, uW}`.

## Route and the source gaps

BZ77 §4.15 (printed pp. 458–459, PDF pp. 19–20) argues by induction on the
number `r` of blocks, with `π = ρ_1 × π°`. It reduces to an irreducible
degenerate `ω`, splits by 4.13(a) into Case 1 (`ω ⊂ σ = (ρ_1|_P) × π°`; 4.13(c),
4.4, 3.5, 4.13(d) and the induction hypothesis) and Case 2
(`ω ⊂ π/σ = ρ_1 × (π°|_P)`; 4.14(a), an irreducible submodule `ω'` of the highest
derivative, and Lemma 4.7(b)).

The Lean proof runs the same induction for a stronger invariant. A
representation `X` of `GL_(n+1)` is *good* (`Good`, line 122) when:

1. the restriction `X|_P` is homogeneous (`Derivative.IsHomogeneous`): every
   nonzero subrepresentation has the same level as `X|_P`. Here the level
   (`Derivative.level`) is the largest order of a nonzero derivative, and 0 if
   there is none;
2. the top derivative `X^(n+1)` has dimension 1.

Condition 2 makes the level of `X|_P` equal to `n + 1`, and condition 1 then
gives every nonzero subrepresentation a nonzero top derivative
(`nontrivial_subrepresentation_of_good`, line 161). So the theorem follows once
every ordered product is good (`good_product`, line 658). `Good`, `Ordered`
(line 613) and `HeadExclusion` (line 429) are internal proposition definitions
of this module, used only as induction invariants and step hypotheses. They have
no separate literature counterpart.

The source gaps named in the contract are resolved as follows.

- **Reduction to an irreducible `ω`.** It is avoided. The binary step proves
  homogeneity of `(D × P)|_P` for all nonzero subrepresentations `W` at once,
  through the published helper `RestrictedProductLevel.isHomogeneous_restrictedProduct`.
  The 4.13(a) dichotomy is applied to `W` through its intersection with
  `σ = range i`, the comap of `σ` along `W ↪ (D × P)|_P`. If this intersection is
  nonzero, Case 1 applies to it, and exactness of the derivatives
  (`level_le_of_injective`, `level_le_max_of_isShortExact`, from
  `Mirabolic.minusExactness`) squeezes the level of `W` between the level of the
  intersection and the level of the whole product. If it is zero, then `W`
  injects into `π/σ = D × (P|_P)` (Case 2). This is the route suggested in the
  contract. It uses no finite-length, Artinian or submodule-existence premise.
- **An irreducible submodule of the highest derivative in Case 2.** None has to
  be chosen. Case 2 shows that the highest derivative of `W` itself injects into
  the head block `D`. `D` is irreducible and the derivative is nonzero, so the
  injection is an isomorphism, and the derivative is irreducible with singleton
  support `{ρ_1}` (`OrderedCuspidalProductHeadShift.irreducible_support_of_injective`).
  No finite length is needed.
- **The excluded cases `j = 1` (`νρ ≇ ρ`) and different ranks.** Lemma 4.7(b)
  gives an equality `ρ_j = ν ρ_1` of cuspidal data, which records both rank and
  class. For `j = 1` it contradicts `OrderedCuspidalProductTwistOne.twist_one_ne_self`,
  a central-character proof. For `j ≠ 1` it is mapped to the rank-indexed sigma
  type `⟨rank, class⟩` of the order condition. So a block of a different rank
  is never a candidate, and no separate rank argument is needed.
- **The identification of `Π` with the binary product.** `headTailBridge`
  (line 397) composes the published `headTailProductInductionIso`, which regroups
  the block product as a two-block product of the lifted head and the product of
  the remaining blocks, with `binaryShapeIso` (line 379). The latter is the
  published `binaryNormalizedProductPositiveIso`, read through the rank cast
  `B.headRank_add_tailRank`.
- **The comparison between `A` on a `BlockShape` and `CuspidalDatum` families.**
  It is made in the helper `headShift_false`. The data are
  `ρ i = ⟨B.size i, B.positive i, (A i).isoClass⟩`, each `ρ i` is represented by
  `A i` by reflexivity, and `T.cuspidalShape ρ _` agrees with `B` definitionally
  (structure eta). So `Π|_P` is literally the restriction of
  `T.cuspidalProductInduced ρ B.sum_eq A` to which the published Lemma 4.7(b)
  applies.

## Proof, section by section

Line numbers refer to `OrderedCuspidalProductNondegeneracyProof.lean`.

**Casts (lines 43–112).** These are transport lemmas for the rank casts
`generalLinearRankCast` and `mirabolicRankCast`. They cover composition and
inverse (47, 56), injectivity of mapped morphisms (64), the commutation of
`mirabolicDerivativeOfOrder` with a mirabolic rank cast (73), the dimension of
the top derivative of a rank cast (84), and `exists_injective_of_rankCast` (97).
The last turns an injection into a rank cast of `Y`, together with an
isomorphism between rank casts of `Y` and `D`, into an injection into a rank
cast of `D`. Each is proved by `subst` and `rfl`, or by composing with the
isomorphism.

**Good (lines 116–175).** This section defines `Good` (122). `good_of_iso` (129)
transports goodness along isomorphisms by the published `isHomogeneous_of_iso`
and invariance of dimension. `nontrivial_top_of_good` (141) and `level_of_good`
(151) give level `n + 1`, by `level_le` and `le_level_of_hasNonzeroDerivative`.
`nontrivial_subrepresentation_of_good` (161) applies homogeneity to `U` and reads
off the top derivative from `level_eq_iff`.

**Supercuspidal blocks (lines 179–226).** The published BZ77 §4.4 theorem
`Classification.supercuspidalDerivatives` states that an irreducible
supercuspidal `D` of `GL_(m+1)` has subsingleton derivatives in all orders `k`
with `0 < k < m + 1`, and a one-dimensional top derivative.
`hasNonzeroDerivative_eq_of_supercuspidal` (191) deduces that `D|_P` has nonzero
derivatives only in order `m + 1`. `good_of_supercuspidal` (206) then gets
homogeneity from the published `RestrictionBridge.isHomogeneous_of_single_order`
(a representation whose nonzero derivatives all have one order is homogeneous,
by detection and exactness) and the dimension from §4.4.
`good_universeLift_of_supercuspidal` (217) passes through
`SmoothRep.universeLift`, by `isIrreducible_universeLift_iff` and
`isSupercuspidal_of_equiv`. `nontrivial_of_isIrreducible` (184) records that an
irreducible representation is nonzero.

**Line (lines 230–263).** `binaryLineIso` (247) shows `D × V ≅ D` (read through a
rank cast) for a representation `V` of `GL_0` of dimension 1. It composes the
published `ZeroRankTensor.binaryRightZeroIso` (`D × V ≅ D ⊗ V` for rank 0) with
`firstFactorLineEquiv` (235), which is `D ⊗ V ≅ D` for a line `V` with trivial
action.

**Top derivative of a binary product (lines 267–370).** `finrank_top_binaryProduct`
(346) states
`dim (D × P)^(a+b) = dim D^(a) · dim P^(b)` for representations `D` of `GL_a` and
`P` of `GL_b`. It is derived from the published GL Leibniz filtration
`generalLinearDerivativeLeibnizFiltration` (BZ77 4.5/4.6). For the top order
`a + b`, the published `leibnizIndices_top` shows that the filtration has the
single index `(a, b)`. So its only graded piece is the whole derivative
(`finrank_graded_of_length_one`, 270). That piece is `D^(a) × P^(b)`, a binary
product of two representations of `GL_0` (`leibnizPiece_obj`). Its dimension is
the product of dimensions (`finrank_binaryProduct_rank_zero`, 301, by
`binaryRightZeroEquiv` and `Module.finrank_tensorProduct`;
`finrank_topLeibnizPiece`, 326).

**Bridge (lines 374–418).** `binaryShapeIso` (379) and `headTailBridge` (397) are
described above.

**Step (lines 422–535).** `HeadExclusion hab D P` (429) says that no
subrepresentation `W` of `(D × P)|_P` has a nonzero derivative of order
`k = level W` that injects into (a rank cast of) `D`.

`caseTwo_false` (451) is Case 2. Let `D` be nonzero on `GL_(m+1)` and `P` good on
`GL_(n+1)`, assume `HeadExclusion`, and let `W ≠ 0` inject both into
`(D × P)|_P` and into `τ = restrictionQuotient = D × (P|_P)`. Then:

1. `τ` is homogeneous by the published Zelevinsky 1980 Proposition 5.3
   `leftMixedProductHomogeneity` (left mixed products with a homogeneous
   mirabolic factor are homogeneous), applied to the homogeneous `P|_P`.
2. `level τ = level (P|_P) = n + 1`. The upper bound and the lower bound (the
   latter for `D ≠ 0`) are the published `level_leftMixed_le` and
   `le_level_leftMixed`, which rest on BZ77 4.14(a) (`leftMixedProductDerivative`).
3. By homogeneity, `level W = n + 1` (`level_eq_of_isHomogeneous`), so
   `W^(n+1) ≠ 0`.
4. Exactness of the derivative functors (`mapsShortExact_mirabolicDerivativeOfOrder`
   with `Mirabolic.minusExactness`) makes `W^(n+1) → τ^(n+1)` injective.
5. By 4.14(a), `τ^(n+1) ≅ D × (P|_P)^(n+1)`. Here `(P|_P)^(n+1) = P^(n+1)` is
   one-dimensional (goodness of `P`) and lives on `GL_0`, so `binaryLineIso`
   gives `τ^(n+1) ≅ D`.
6. So `W^(n+1)` injects into `D` with `n + 1 = level W`, and `HeadExclusion`
   gives `False`.

`good_step` (501) is the binary step. Let `D` be irreducible supercuspidal on
`GL_(m+1)` and `P` good on `GL_(n+1)`, and assume `HeadExclusion`. Then
`D × P` (read through a rank cast) is good:

- Homogeneity comes from the published helper `isHomogeneous_restrictedProduct`
  with `n' = 0` and `s = m`. It takes the following inputs:
  - the hypothesis `hDj` that `D|_P` has nonzero derivatives only in order
    `m + 1`, from §4.4;
  - the hypothesis `hY` that `D^(m+1) × P|_P` is homogeneous. This is
    Proposition 5.3 at rank `k = 0`, since `D^(m+1)` is a representation of
    `GL_0`;
  - the Case 2 exclusion `caseTwo_false`;
  - the published proofs of 4.13(a) (`mirabolicProductRestriction`), the
    right-`Φ⁻` short exactness and boundary clauses of 4.13(c)
    (`mirabolicProductMinusCompatibility`, components `RightPhiShortExact` and
    `RightPhiBoundary`), 4.13(d) (`rightMixedProductPhiMinusDetection`), 4.14(a)
    (`leftMixedProductDerivative`) and minus exactness.

  Inside the helper, Case 1 is the published `RightMixedLevel.level_of_injective_rightMixed`:
  every nonzero subrepresentation of `σ = (D|_P) × P` has level
  `level (D^(m+1) × P|_P) + m + 1`. This follows BZ77's Case 1 through
  4.13(c), 4.4, 3.5 detection (`mirabolicDerivativeDetection`) and 4.13(d).
- The dimension is `dim D^(m+1) · dim P^(n+1) = 1 · 1`, by
  `finrank_top_binaryProduct`, §4.4 for `D` and goodness of `P`.

The induction hypothesis therefore enters as goodness of the tail `P`. Its two
parts replace BZ77's use of the induction hypothesis in Case 1 (homogeneity of
`P|_P`) and give the one-dimensional `(π°)^(top)` used in Case 2.

**Single block (lines 539–604).** `good_single` (587) is the base case `r = 1`.
For `B.length = 1`, the family is the transport of its unique block
(`singleFamily_eq`, 549). The published `normalizedProductInductionObjEquiv` and
`singleBlockTransportedProductEquiv` identify the one-block product with
`SmoothRep.universeLift` of that block (`singletonProductLiftIso`, 564), which is
good by the supercuspidal section.

**Induction (lines 608–684).** `Ordered T B A` (613) is the order condition of the
target. `headExclusion_of_ordered` (624) proves `HeadExclusion` for the split
into the head block (index `B.headIndex h`, the first block) and the product of
the others. It maps `W` into `Π|_P` through `headTailBridge` and applies the
helper `OrderedCuspidalProductHeadShift.headShift_false` with `i₀ = headIndex`.
The helper needs `⟨B.size j, (A j).isoClass⟩ ≠ ν⟨B.size i₀, (A i₀).isoClass⟩` for
every `j ≠ i₀`. This is the order condition for the pair `i₀ < j`, since `i₀` is
the first index. `ordered_tail` (646) restricts the order condition to the tail.
`good_product` (658) is the induction on the number of blocks:

- for one block it is `good_single`;
- for `k + 2` blocks it applies `good_step` to `D = universeLift (A i₀).obj` and
  the tail product, which is good by the induction hypothesis, and transports
  the result back along `headTailBridge`.

**Final theorem (lines 688–702).** `B.length ≠ 0`, because the block sizes sum to
`N + 1 > 0`. So `good_product` applies with rank cast `rfl`, and
`nontrivial_subrepresentation_of_good` gives the conclusion for `U`.

## Comparison with the original proof

- BZ77 reduces to an irreducible `ω`. The Lean proof never does, and proves
  homogeneity, which is stronger than the theorem, by the intersection
  dichotomy.
- BZ77's Case 1 shows that `(Φ⁻)^(n_1)(ω)` is a nonzero degenerate submodule of
  `π°|_P` and applies the induction hypothesis. The Lean proof computes the level
  of every nonzero submodule of `σ` from the homogeneity of
  `ρ_1^(n_1) × π°|_P` (Proposition 5.3 at rank 0, using homogeneity of
  `π°|_P` from the induction hypothesis). The ingredients 4.13(c), 4.4, 3.5 and
  4.13(d) are the same.
- In BZ77's Case 2, an irreducible `ω'` in the highest derivative of `ω` has
  `ρ_1` in its support by 4.14(a). The Lean proof shows that the highest
  derivative is itself isomorphic to `ρ_1`. It uses 4.14(a), Proposition 5.3 for
  the level, and the one-dimensionality of `(π°)^(top)` carried in the induction
  invariant. 4.7(b) is then applied as in the source.
- The induction invariant also carries `dim (π)^(top) = 1`. Its step uses the
  Leibniz filtration (BZ77 4.5/4.6) at the top order.
- `νρ ≇ ρ`, which BZ77 leaves implicit, is proved by the central character.

The use of Zelevinsky 1980 Proposition 5.3 goes beyond the BZ77 text. It is
authorized by operator response `da4ad97c47065551b5b24cf4d461b9a4` (see below).

## Helper pairs

Two new helper pairs are part of this candidate. Each has its own Markdown.

- `Langlands/Representation/Derivative/OrderedCuspidalProductHeadShift.{lean,md}`
  (Worker 1166; interface and the `j = i₀` step revised by Worker 818). It proves
  `irreducible_support_of_injective` and `headShift_false`, the head-shift step of
  Case 2 through the published Lemma 4.7(b) `cuspidalProductMirabolicSupportShift`.
  It imports the 4.7(b) proof module, `OrderedCuspidalProductTwistOne`,
  `Induction.SingleBlock` and `Category.UniverseLift`.
- `Langlands/Representation/Derivative/OrderedCuspidalProductTwistOne.{lean,md}`
  (Worker 1168's proof, moved and interfaced by Worker 818). It proves
  `exponent_eq_zero` and `twist_one_ne_self` (`ρ.twist 1 ≠ ρ` for every cuspidal
  datum). The proof evaluates an equivalence `A ≅ |det|^s A` at the scalar
  uniformizer, using the published admissible Schur lemma
  `admissibleSchur_centralCharacter`.

The Library's existing proof of `νρ ≠ ρ`,
`RepeatedCuspidalSupport.twist_one_ne_self`, is not used. It rests on
`CuspidalIntegralTwistFreenessProof`, whose earliest artifact `a7545313` belongs
to the excluded task `67279e36-f3c2-42e3-9302-11729784042e`.

## Published inputs

Every theorem used has an independently accepted and published proof, or is a
reviewed lemma inside a published `lean.definition` or `lean.proof` artifact.
Rows give the module (prefix `Langlands.Representation.` unless stated), the
introducing artifact with its task and publication commit, and the declarations
used. "Proof task" means the task recorded on the proof artifact.

| Module | Publication | Used |
| --- | --- | --- |
| `Derivative.OrderedCuspidalProductNondegeneracyStatement` | statement `bcda0d7d-48a7-4a3a-8b0e-ad48b26c9c68`, task `12eb3790-50bc-4727-acc4-14ced067d333`, commit `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762` | the target proposition only |
| `Classification.SupercuspidalDerivativesProof` | proof `fd42c8ef-e65b-4942-9a76-d41f2e22bcd3`, proof task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` revision 2, commit `c5eebf94883144ce00adc4e252995c28082f08a7` | `Classification.supercuspidalDerivatives` (BZ77 §4.4) |
| `Derivative.LeftMixedProductHomogeneityProof` | proof `e183909c-e3a3-4843-b1b4-dd3700a47c37`, task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4`, commit `da0312e3777850c14b211f6245ff5b08af56f616`; statement `1e101502`, task `49d8eea3` | `leftMixedProductHomogeneity` (Ze80 5.3) |
| `Derivative.MirabolicProductRestriction` | proofs `d8caeff4-6ce1-4951-b9f7-ea118beb47f7` and `d58e34da-2a41-4180-baa9-c4cce03286bb`, task `a1d00661`, commits `7114a390` and `368b3cec` | `mirabolicProductRestriction` (BZ77 4.13(a)) |
| `Derivative.MirabolicProductMinusCompatibility` | proof `ddfa367b-fa96-488a-9f20-285c05af3cf6`, task `6cd54f76`, commit `f6b45fe9` | `mirabolicProductMinusCompatibility` (BZ77 4.13(b,c)); components `RightPhiShortExact`, `RightPhiBoundary` |
| `Derivative.RightMixedProductPhiMinusDetectionProof` | proof `a07ed51f-f4b9-447c-9da8-cecaed53a506`, task `f8acf579`, commit `9a8ca758` | `rightMixedProductPhiMinusDetection` (BZ77 4.13(d)) |
| `Derivative.LeftMixedProductDerivativeProof` | proof `e99bbe1b-06fe-42ad-b8ec-d1c4e02c9929`, task `7e19f753`, commit `b4b4160d` | `leftMixedProductDerivative` (BZ77 4.14(a)) |
| `Derivative.MirabolicMinusExactnessProof` | proof `d307cd07-7e0f-4e38-a3d5-94b78bb3a7d6`, task `b65bc667`, commit `9a8ca758` | `Mirabolic.minusExactness` |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | proof `c4c5439d-5c26-42e5-848a-0f199ce34f7d`, task `4e10058b`, commit `e3944f76`; statement module `GeneralLinearDerivativeLeibnizFiltrationStatement` (statement `3f0ee8cb`, task `3238f371`) | `generalLinearDerivativeLeibnizFiltration` (BZ77 4.5/4.6), `GeneralLinearDerivativeLeibnizFiltrationStatement.filtration`, `leibnizIndices_top`, `mem_leibnizIndices`, `leibnizPiece_obj` |
| `Derivative.MirabolicDerivativeDetectionProof` (through `LevelCalculus`) | proof `3ace613e-7e47-46fc-aea5-dcd84efc51ec`, task `ed056880`, commit `81727e81` | `mirabolicDerivativeDetection` (BZ77 3.5), inside `level_pos` |
| `Derivative.RestrictedProductLevel`, `Derivative.RightMixedLevel`, `Derivative.RestrictionBridge`, `Derivative.ProductVanishing`, `Derivative.LevelCalculus` | definitions `6ded142e-bf04-4d18-8956-a5850e80410b` (commit `7114a390`) and `e85cf101-daae-4eb8-bac1-2f3ee0d0ee3b` (`LevelCalculus`, commit `5e4a58e8`), task `b711af72-fdf9-4b32-a450-937911426822` | `isHomogeneous_restrictedProduct`, `level_leftMixed_le`, `le_level_leftMixed`, `isHomogeneous_mirabolicRankCast`, `RestrictionBridge.generalLinearDerivative_succ_obj_eq`, `isHomogeneous_of_single_order`, `level_mirabolicRankCast`, `mapsShortExact_mirabolicDerivativeOfOrder`, `map_injective_of_exact`, `isHomogeneous_of_iso`, `iso_hom_injective`, `level_eq_of_isHomogeneous` |
| `Derivative.ZeroRankTensor` | definition `2057375a-efa5-4820-8c92-9bfe62629560`, task `3231134e`, commit `9a8ca758` | `binaryRightZeroIso`, `binaryRightZeroEquiv` |
| `Parabolic.HeadTailProductInduction` | definition `665edfad-042c-4845-bf51-ff72c2267442`, task `30f91c25`, commit `a8a83747` | `headTailProductInductionIso`, `headTailProductFactors` |
| `Langlands.Group.GL.HeadTailBlocks` | definition `621da62e`, task `8e9f89dc`, commit `feda7e54` | `headRank`, `tailRank`, `headIndex`, `tailIndex`, `tailShape`, `headTailShape`, `headRank_add_tailRank`, `headRank_pos`, `tailRank_pos` |
| `Induction.BinaryProduct` | definition `34e5003f`, task `85af02b8`, commit `e40be87d` | `binaryNormalizedProductFunctor`, `binaryNormalizedProductPositiveIso`, `binaryPairFamilyFunctor` |
| `Langlands.Group.GL.MirabolicOppositeIntersection` | definition `3df71010`, task `3f007f96`, commit `f75d5c19` | `BlockShape.binary` |
| `Langlands.Group.GL.SingleBlock` | definition `d22495cd`, task `7c0e046b`, commit `15eedb12` | `BlockShape.singleBlockIndex`, `singleBlock_size`, `eq_singleBlockIndex`, `BlockShape.rankCast` |
| `Parabolic.RegroupingFactorEquivalences`, `Parabolic.ThreeBlockRegroupingAssembly` | definitions `fedc6eee` (commit `9de4c692`) and `dcd3e87b` (commit `65f39f42`), task `6508da9d` | `singleBlockTransportedProductEquiv`, `normalizedProductInductionObjEquiv`, `Parabolic.equivTrans` |
| `Category.UniverseLift` | definition `b6075d7d`, task `4d079ce9`, commit `feda7e54` | `SmoothRep.universeLift`, `universeLiftEquiv`, `isIrreducible_universeLift_iff` |
| `Derivative.Homogeneity` | definition `609028d8-d915-4c8c-8223-2ece7bff15ff`, task `dfae49d8`, commit `c76b7751` | `IsHomogeneous`, `level`, `HasNonzeroDerivative`, `level_le`, `level_eq_iff`, `le_level_of_hasNonzeroDerivative`, `mirabolicDerivativeOfOrder`, `mirabolicRankCast` |
| `Derivative.Iteration` | definition `13695739-0adc-4683-906f-57a8029b2353`, task `d3e94f0f`, commit `355c0523` | `generalLinearDerivative`, `generalLinearRestriction`, `generalLinearRankCast`, `mirabolicDerivative` |
| `Induction.BlockFactors` | definition `ee7ae365`, task `a7a453ca`, commit `f8488ce7` | `normalizedProductInductionFunctor` |
| `Classification.SupercuspidalTwist` | definition `cba40ce7`, task `a7a453ca`, commit `6700bb75` | `supercuspidalClassRealPowerTwist` |
| `Classification.Supercuspidal`, `Category.Basic`, `Category.Subquotients` | current versions in definition `0a5d67d6-d44a-4544-b839-0257d12531bf`, task `6c50b2fd`, commit `6473a6d8` | `SupercuspidalRep`, `supercuspidalProperty`, `isSupercuspidal_of_equiv`, `isoClass`, `SmoothRep.mkIso`, `SmoothRep.equivOfIso`, `SmoothRep.subrepresentation` |
| `Filtration.Definitions` | general filtration definitions | `RepFunctorFiltration` (`step`, `graded`, `zero`, `top`) |
| `Tensor.OneFactor` | integrator extraction from `Induction.BinaryProduct` (no owner) | `BinaryTensor.firstFactor` |

The helper pairs use in addition the published Lemma 4.7(b)
`Classification.cuspidalProductMirabolicSupportShift` (proof
`4b8c7a7c-baaf-4fb3-bb60-213389f02470`, task
`0b3bf4c1-9878-444f-899e-ba29d7679c29`, commit `9a8ca758`), the admissible Schur
lemma `admissibleSchur_centralCharacter` (proof `b97b88e5`, task `7418b301`,
commit `01a58491`), `Induction.SingleBlock` (definition `fcc278b3`, task
`8c397428`) and the definitions of `Classification.SupercuspidalSupport`. Their
Markdown lists the details.

The §4.4 proof `fd42c8ef` was checked as the contract requires. It is the
accepted proof artifact of task `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` at
revision 2 (its validation binds `task_revision 2` and statement declaration
`Langlands.Classification.SupercuspidalDerivatives`), and its inputs are the
multiplicity-one proof `ba2dff22` (Gelfand–Kazhdan, task `209cde88`) and the
statement `c27c6879`. Its 303-module import closure contains no segment,
socle, multisegment or exhaustion module. Its `Classification` modules are
`ConstituentRelations`, `Segments` (cuspidal data and their twists only),
`Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalDerivativeVanishing`,
`SupercuspidalDerivativesProof`, `SupercuspidalDerivativesStatement`,
`SupercuspidalSupport`, `SupercuspidalTopDerivative` and `SupercuspidalTwist`. The
statement module `SupercuspidalDerivativesStatement` is the isolated
cuspidal-derivative statement (it imports only `Classification.Supercuspidal`,
`Derivative.Iteration` and `HarmonicAnalysis.Basic`), not the segment-socle
statement module. So it is independent of the segment-socle part of task
`8e5b4563-0365-41c7-b134-70f2a0b36292`.

## Operator rulings

- Decision `bd71b9185aab5d6eafffb7891bd3a3ca`: only fully proved, independently
  accepted and published BZ77 general derivative theory. The closure must avoid
  the listed tasks and the segment-socle part of `8e5b4563`. This file records
  the audit.
- Response `f6869c7da0bf5bb4a8b006fdf51ba668` (for task `0b3bf4c1`): the 4.7(b)
  proof may import `CuspidalProductDerivativeQuotientSupport` and
  `WholeLeviTransport`, with a closure audit.
- Response `09565d9017ef55faa68ad9890c242aed`, to question
  `f489243c6b4e5a93a776216687d56d51`: for this task,
  `cuspidalProductMirabolicSupportShift` may be imported with its whole closure,
  including `bf38b454`, `WholeLeviTransport` and
  `PartialDerivativeJacquetComparisonProof`. A fully proved general comparison
  of derivatives and Jacquet modules such as Ze80 3.7(b) counts as general
  derivative theory. The conditions are those of `f6869c7d`. An import whose
  audit finds an excluded task, module or identifier is not used, and the
  operator is told.
- Response `da4ad97c47065551b5b24cf4d461b9a4`, to question
  `541c6cb8ede4505ea8c3fb53a4e1dc9f`: for this task, `leftMixedProductHomogeneity`
  (Ze80 5.3, tasks `49d8eea3` and `6bb62ea4`) may be imported with its closure,
  under the same conditions. `Classification.Supercuspidal*`,
  `Whittaker.Algebraic`, `Whittaker.GeneralLinear` and `Whittaker.Iwasawa` must
  be checked explicitly. They are checked below.
- Response `2b34e4035a5b5dafad7ad84d5a8c0dd8`, to question
  `8e823787446e583e8462be85b6aaf65e`: this task may keep the nine definition
  and statement modules of the excluded tasks `f3a69bc8`, `3c9849a4` and
  `8e5b4563` listed in the closure audit below. The exclusions target the
  excluded tasks' mathematical conclusions and whatever depends on them, not
  general infrastructure published under those tasks. The operator checked the
  nine modules at Library `b1c8a5e8`: they hold definitions and a few generic
  lemmas, and their project imports are generic too. None states or uses socle
  exhaustion, the two-supercuspidal product theorem or any other excluded
  conclusion. Each module is documented below with its artifact, publishing
  task, content and this check. The two local replacements listed next stay in
  place. A module found to contain or depend on an excluded conclusion would be
  removed like them.

Following `09565d90` and `da4ad97c`, two imports of an earlier draft were dropped
after the audit found excluded owners, and the operator was told in question
`8e823787`:

- `Classification.CuspidalIntegralTwistFreenessProof` (proof `a7545313`, excluded
  task `67279e36`). It was replaced by `OrderedCuspidalProductTwistOne`.
- `Derivative.TopProduct` with `Filtration.SingletonIso` (definition `3ee88231`,
  excluded task `8364e73f`). The dimension of the top derivative of a binary
  product is now derived locally from the Leibniz filtration, in the section
  "Top derivative of a binary product".

## Import closure audit

The direct imports are:

- the target statement module;
- the helper pair `OrderedCuspidalProductHeadShift`, which imports the helper
  pair `OrderedCuspidalProductTwistOne`;
- the published proofs `Classification.SupercuspidalDerivativesProof`,
  `Derivative.LeftMixedProductHomogeneityProof`,
  `Derivative.MirabolicMinusExactnessProof`,
  `Derivative.RightMixedProductPhiMinusDetectionProof`,
  `Derivative.MirabolicProductMinusCompatibility`,
  `Derivative.MirabolicProductRestriction`,
  `Derivative.LeftMixedProductDerivativeProof` and
  `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`;
- the definition modules `Derivative.RestrictedProductLevel`,
  `Derivative.ZeroRankTensor` and `Parabolic.HeadTailProductInduction`.

The audit was made at Library base `b1c8a5e809be36100da09da81385a7ca6789ae80`.
The recursive project import closure of this module has 906 `Langlands` modules,
this module included. The listing is in the appendix. The closures of the
individual imports have these sizes:

| Import | Closure size |
| --- | --- |
| `OrderedCuspidalProductHeadShift` | 611 |
| `GeneralLinearDerivativeLeibnizFiltrationProof` | 323 |
| `LeftMixedProductHomogeneityProof` | 313 |
| `SupercuspidalDerivativesProof` | 303 |
| `MirabolicProductMinusCompatibility` | 278 |
| `LeftMixedProductDerivativeProof` | 260 |
| `MirabolicProductRestriction` | 160 |
| `HeadTailProductInduction` | 151 |
| `RestrictedProductLevel` | 141 |
| `RightMixedProductPhiMinusDetectionProof` | 102 |
| `ZeroRankTensor` | 74 |
| `OrderedCuspidalProductNondegeneracyStatement` | 73 |
| `MirabolicMinusExactnessProof` | 68 |

The 4.7(b) proof module alone has 606 modules. The imports other than the head-shift
helper together have 609.

**Owners.** Every module was mapped to the artifacts whose files contain it,
whether the artifact introduces the module or only bundles a copy. Each artifact
was mapped to its owning task: the record's task, or for a publication the host
task of its review task. 889 modules have published artifacts. The other 17 have
no task owner:

- the three new modules of this candidate (this module and the two helpers);
- 14 integrator extractions of infrastructure: `Group.GL.OneBlockShape`,
  `Group.GL.RankReindex`, `Group.GL.ReindexCongr`, `Group.GL.Transvection`,
  `HarmonicAnalysis.FiniteProductMeasureScaling`,
  `HarmonicAnalysis.PadicLatticeTopology`, `Representation.Compact.OrbitMeanTranslation`,
  `Representation.CuspidalSupport.WholeLeviTransport` (allowed by `09565d90`),
  `Representation.Derivative.MirabolicDeterminant`,
  `Representation.Derivative.ShortExactFunctorLaws`, `Representation.OrbitSpan`,
  `Representation.Smooth.Transfer.GroupEquivalence`, `Representation.Tensor.OneFactor`
  and `Topology.CompactNormCharacter`.

This gives 847 owning tasks. Following every contract requirement of those tasks
transitively gives 850 tasks. They were compared with the 38 task IDs excluded by
this contract (every task named in the objective and its inherited restrictions,
including `5428fe2c`, `3ff5c8fb`, `5ab445dc` and `62de5903`). Four excluded tasks
appear. In every case the module is a definition or statement module, and none of
them states or proves an excluded conclusion:

- Task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` (socle exhaustion) introduced six
  general filtration and tensor adapters: `Filtration.ObjectTransport`
  (`68054cb0`), `Tensor.FiniteFiltration` (`1529e866`), `Tensor.ExternalFiltration`
  (`428f73bc`), `Tensor.ExternalSubrepresentation` (`6ddf89c2`),
  `Parabolic.InductionSubrepresentation` (`305bd86b`) and
  `Parabolic.ProductInductionSubrepresentation` (`fec3f86b`). They are reached only
  through the chain `RestrictedProductLevel` ← `RightMixedLevel` ←
  `ProductVanishing` ← `ProductInductionSubrepresentation` ←
  `ExternalSubrepresentation` ← `ExternalFiltration` ← `FiniteFiltration` ←
  `ObjectTransport`. So they are reached through `RestrictedProductLevel` and
  through the Ze80 5.3 proof, which imports `RestrictedProductLevel`. The same
  task also introduced the list-counting API `Combinatorics.RelationInversions`
  (`9e971abc`). It is reached only through the mandated §4.4 proof
  (`SupercuspidalDerivativesProof` ← `Whittaker.MultiplicityOneProof` ← … ←
  `Group.GL.UpperBruhatFiltration`).
- Task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` (two-supercuspidal nonadjacent
  product) introduced `Derivative.MirabolicMinusNormalization` (`149ed2a1`), the
  Haar-normalization adapter for `Ψ⁻`/`Φ⁻`. It is reached only through the 5.3
  proof (`LeftMixedProductPhiHatIterate` ← `MirabolicSmoothPhiPlusProduct` ← … ←
  `MirabolicPlusNormalization`).
- Task `8e5b4563-0365-41c7-b134-70f2a0b36292` owns the statement `c27c6879`, which
  bundles `Classification.SupercuspidalDerivativesStatement`. This is the
  cuspidal-derivative statement of the mandated §4.4 proof, which the contract
  allows. The task is also reached as a contract requirement of two tasks:
  task `2e5183b1`, the §4.4 proof task, through that statement; and task
  `f81d9b36`, the owner of the quotient-support helper `bf38b454`, which
  `09565d90` authorizes by name. No segment-socle module of `8e5b4563` is in the
  closure. In particular, neither `SegmentSocleDerivativesStatement` nor any
  `HighestDerivativeSupportShift` module is in it.
- Task `62de5903-b616-4b5c-88eb-a066b77c5467` owns proof `001944f3`, which only
  bundles copies of seven modules: `Derivative.MirabolicDerivativeVanishing`,
  `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
  `MirabolicPhiMinusNondegeneratePairing`,
  `PartialDerivativeJacquetComparisonStatement`, and
  `Geometric.ParabolicOrbitSectionComparison` and `ParabolicOrbitStagesCoefficient`.
  These copies are byte-identical to the Library files. The modules were
  accepted earlier under other tasks: proof `f957ae76` (task `a925b519`, BZ77
  3.8), statement `5d596030` (task `087df35f`) and definitions `a84b7e4a` and
  `4bfd5d0d` (task `18915f54`). They are reached through the 4.7(b) closure that
  `09565d90` authorized, and `MirabolicDerivativeVanishing` also through the
  detection proof. `Whittaker.SupercuspidalCoinvariantFinitenessStatement`, the
  conclusion of `62de5903`, is not in the closure.

**Modules kept under response `2b34e403`.** The operator allowed the nine
modules of `f3a69bc8`, `3c9849a4` and `8e5b4563` above to stay in the closure
(response `2b34e4035a5b5dafad7ad84d5a8c0dd8`, see "Operator rulings"). Each is
listed here with its introducing artifact, its publishing task and its content.
Module names have the prefix `Langlands.Representation.` except
`Langlands.Combinatorics.RelationInversions`.

| Module | Artifact and publishing task | Content | Project imports |
| --- | --- | --- | --- |
| `Filtration.ObjectTransport` | definition `68054cb0-7541-498d-bd52-0414519d5815` (copy also in `1529e866`), task `f3a69bc8` | Transport of an `ObjectRepFiltration` along a group homomorphism (`comp`, `compGradedEquiv`) and along an equivalence of representations (`mem_equivTransport_subrepresentation`, `equivTransportGradedEquiv`) | `Filtration.LengthTwoMatching` (definition `701ca674`, task `53969569`) |
| `Tensor.FiniteFiltration` | definition `1529e866-4b41-41d6-9510-5b00eacdd1c7` (copy also in `428f73bc`), task `f3a69bc8` | Finite tensor products of representations: `congrEquiv`, `slotEquiv`, the filtration induced by a filtration of one slot (`slotFiltration`), its graded pieces and the injectivity of their maps | `Tensor.Finite` (definition `237628bc`, task `a7a453ca`), `Tensor.Filtration` (definition `afd064b6`, task `a084147c`), `Filtration.ObjectTransport` |
| `Tensor.ExternalFiltration` | definition `428f73bc-5621-43c2-b72b-3aed5f40320c`, task `f3a69bc8` | The same slot filtration for an external tensor product (`externalSlotFiltration`, its graded pieces and maps) | `Tensor.FiniteFiltration` |
| `Tensor.ExternalSubrepresentation` | definition `6ddf89c2-bf68-48c5-bb80-7b620f4af522` (copies also in `305bd86b` and `fec3f86b`), task `f3a69bc8` | The subrepresentation of an external tensor product generated by a subrepresentation of one slot (`externalSlotSubrepresentation`) with its `⊥`, `⊤`, order, `≠ ⊥` and `≠ ⊤` lemmas, and `leftTensorImage_le_iff` | `Tensor.ExternalFiltration` |
| `Parabolic.InductionSubrepresentation` | definition `305bd86b-670e-4369-ab5a-549ec74ee689` (copy also in `fec3f86b`), task `f3a69bc8` | Normalized parabolic induction of a subrepresentation (`normalizedInducedSubrepresentation`) with its `⊥`, `⊤`, order, `≠ ⊥` and `≠ ⊤` lemmas; `exists_valueSubrep_eval`, `valueSubrep_le_iff` | `Parabolic.InductionFactorMatchingProof` (proof `91f99d8f`, task `ded88550`) |
| `Parabolic.ProductInductionSubrepresentation` | definition `fec3f86b-c0ba-42b2-b6b7-bb31421a8b56`, task `f3a69bc8` | The subrepresentation of a normalized block product induced from a subrepresentation of one factor (`normalizedProductSlotSubrepresentation`) with the same lemmas; a proper nonzero subrepresentation of one factor gives a proper nonzero one of the product | `Tensor.ExternalSubrepresentation`, `Parabolic.InductionSubrepresentation`, `Induction.BlockFactors` (definition `ee7ae365`, task `a7a453ca`) |
| `Combinatorics.RelationInversions` | definition `9e971abc-0144-4575-8205-89a2ae397e63` (copy also in `aa59ea67`), task `f3a69bc8` | For a relation on a type, `relationPairCount` and `relationInversions` of lists, with append, vanishing, monotonicity and swap lemmas | Mathlib and Lean only |
| `Derivative.MirabolicMinusNormalization` | definition `149ed2a1-eff4-4b02-87a3-569b0f22b048`, task `3c9849a4` | Half-modulus character identities, the characters `psiMinusHaarInverseHalf` and `phiMinusHaarInverseHalf` with their formulas and open kernels, and the Haar-normalization identities `psiMinus_haarNormalization` and `phiMinus_haarNormalization` | `Group.GL.MirabolicModulusProof` (proof `f25fdd6c`, task `f947a735`), `Derivative.MirabolicMinus` (definition `293388d4`, task `74fa48e1`) |
| `Classification.SupercuspidalDerivativesStatement` | bundled in statement `c27c6879-9906-43fa-8d88-cf1808b55f2d`, task `8e5b4563` | The Prop-valued definition `SupercuspidalDerivatives` (BZ77 §4.4), which the contract allows and which the mandated proof `fd42c8ef` proves | `Classification.Supercuspidal`, `Derivative.Iteration`, `HarmonicAnalysis.Basic` |

These modules are reached as described above. The six filtration and tensor
adapters enter through `RestrictedProductLevel` and the Ze80 5.3 proof.
`RelationInversions` and `SupercuspidalDerivativesStatement` enter through the
§4.4 proof, and `MirabolicMinusNormalization` through the 5.3 proof. The
operator's check was repeated here at `b1c8a5e8`. The declarations of the nine
modules are the definitions and lemmas named in the table. None of them states
or uses socle exhaustion, the irreducibility or structure of a product of two
supercuspidals, a segment or multisegment result, or any other excluded
conclusion. The recursive import closures of the nine modules have 7, 19, 20,
21, 60, 72, 1, 62 and 59 modules, in the order of the table. In each of these
closures the only modules with an excluded owner are modules from this table.
Every other project import is owned by a non-excluded task.

**Identifiers.** All 906 Lean files were scanned for the excluded declaration
and module names: every name listed in the contract, the three Whittaker
coinvariant-finiteness statements, `CuspidalIntegralTwistFreeness`,
`RepeatedCuspidalSupportShift`, `TopProduct`, `topProductTensorEquiv` and
`segmentDerivative`. They were also scanned for the 38 excluded task IDs. There
is no Lean hit. 46 of the 905 Markdown files of the other modules mention
excluded task IDs. Every such mention is in an independence or exclusion audit
section, in a provenance line (`SupercuspidalDerivativesStatement`), or explains
the removal of an excluded import (the two helper pairs).

**Modules named by `da4ad97c`.** The `Classification.Supercuspidal*` modules in
the closure are cuspidal infrastructure:

- `Supercuspidal` (definitions, `0a5d67d6`);
- `SupercuspidalTwist` (`cba40ce7`);
- `SupercuspidalSupport` (`5f04f9a1`, `6ee5d0b4`);
- `SupercuspidalSupportStatement` (`ab3b22c3`);
- `SupercuspidalSupportUniquenessProof` (`9533b6b3`, task `b0b54bc0`);
- `SupercuspidalContragredient`, `…Statement`, `…Aux` and `…Proof` (`1269a9fc`,
  `1d93e28a`, `c9408696`, `a090c713`; tasks `a7a453ca`, `1c921aca`);
- `SupercuspidalDerivativeVanishing`, `SupercuspidalTopDerivative`,
  `SupercuspidalDerivativesStatement` and `SupercuspidalDerivativesProof` (tasks
  `2e5183b1`, `8e5b4563` statement only).

None states a segment, socle, classification or exhaustion result.
`Whittaker.Algebraic`, `Whittaker.GeneralLinear` and `Whittaker.Iwasawa`
(`e4518542`, task `6f0365a3`) are definitions of Whittaker functionals and models.
The other Whittaker modules in the closure are the Gelfand–Kazhdan
multiplicity-one development: `Whittaker.MultiplicityOneProof` (`ba2dff22`, task
`209cde88`), its statement (`4256a9ec`, task `5bd68403`), `PrerequisitesStatement`
(`bd81d0bb`, task `b036b2e6`) and the Bruhat-cell distribution lemmas. No
coinvariant-finiteness module is in the closure:

- not `IrreducibleCoinvariantFinitenessStatement`;
- not `LeviCuspidalCoinvariantFinitenessStatement`;
- not `SupercuspidalCoinvariantFinitenessStatement`;
- no module of tasks `5ab445dc`, `3ff5c8fb` or `5428fe2c`.

The only finite-length modules are the general `Filtration` Jordan–Hölder and
length APIs, which are not used to prove any finiteness of derivatives.

## Condition-by-condition exclusion audit

Two checks support the table. The mathematical proof chain above (this module, the
two helpers and the published inputs listed) uses none of the excluded results.
The import closure audit confirms this at the level of modules, owning tasks,
transitive requirements and identifiers. An identifier scan cannot exclude a
renamed result, so each row also records the mathematical inspection. Task IDs
only identify the prohibitions.

| Excluded conclusion or task family | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | Not imported and not used. The proof concerns products of supercuspidal blocks, not segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`; `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | Not used. |
| `SegmentSocleProductIrreducibility`; `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | Not used. |
| `AdjacentUnlinkedSegmentSocleSwap`; `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | Not used. |
| `TwoSegmentSocleCommutation`; `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | Not used. |
| `LinkedSegmentSocleGluing`; `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | Not used. |
| `OrderedMultisegmentSocleExistence`; `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Not used. |
| `MultisegmentSocleExhaustion`, socle exhaustion; `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No conclusion used. The closure contains seven definition modules introduced by this task (general filtration and tensor adapters and a list-counting API). They enter through `RestrictedProductLevel`, the Ze80 5.3 proof and the §4.4 proof, and contain no socle or exhaustion statement. The operator allowed them in response `2b34e403`; see the closure audit. |
| Analytic segment classification; `aca8805b-054f-4d56-8045-12db7f623404` | Not used. |
| Special-head multisegment exhaustion; `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | Not used. |
| Ordered strong-head existence; `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Not used. |
| Quotient coverage; `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Not used. |
| Ordered conversion; `8252833d-c269-41a9-824c-5879e531b23b` | Not used. |
| Tempered uniqueness; `52e97845-36bb-457d-b76f-70753334b88c` | Not used. |
| `GenericSegmentProductUniqueness`; `30341ae4-65f2-4a0e-9283-763db01a409e` | Not used. |
| `SquareIntegrableLanglandsClassification`; `1cb45da2-7007-4351-a694-594fb148b8d1` | Not used. |
| Square-integrable exhaustion; `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | Not used. |
| Regular exhaustion; `bf433f0a-921a-428c-b0c0-6475438125ac` | Not used. |
| `SegmentSpecialEssentialSquareIntegrability`; `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | Not used. |
| `SegmentHeadProductIrreducibility`, special-head criterion and special-head product irreducibility; `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Not used. Its definition artifact `3ee88231` (`Derivative.TopProduct`, `Filtration.SingletonIso`) was imported by an earlier draft and has been removed. The dimension of the top derivative of a binary product is proved locally from the Leibniz filtration. This task is the consumer of the theorem. |
| Individual special-head/reverse-socle existence; `67279e36-f3c2-42e3-9302-11729784042e` | Not used. `CuspidalIntegralTwistFreenessProof` (`a7545313`) and `RepeatedCuspidalSupport` are not in the closure. `νρ ≠ ρ` is proved in `OrderedCuspidalProductTwistOne`. |
| Individual segment-socle/reverse-head existence; `4ca79bbd-589e-476b-9f65-661e799984b5` | Not used. |
| `SegmentFullJacquetFormula`; `ed48ae06-964c-4c84-9e62-978f5a953ca7` and its exact proof successor | Not used. The only Jacquet input, inside the 4.7(b) closure, is the general geometric lemma together with the Ze80 3.7(b) comparison authorized by `09565d90`. |
| `SegmentHeadJacquetFormula`; `55ad1e10-62d8-46b7-a081-909ef0056426` | Not used. |
| `SegmentSocleJacquetFormula`; `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | Not used. |
| `SegmentSpecialJacquetExponentNormFormula`; `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Not used. |
| `TwoSupercuspidalNonadjacentProductIrreducible`; `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | No conclusion used. Its definition module `MirabolicMinusNormalization` (the `Ψ⁻`/`Φ⁻` Haar adapter) is in the 5.3 closure. It contains no product or irreducibility statement. The operator allowed it in response `2b34e403`; see the closure audit. |
| `TwoSupercuspidalProductStructure`; `ab61f565-1427-4746-ba77-46097563e962` | Not used. No product structure or two-factor conclusion appears. |
| All-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467`, `SupercuspidalCoinvariantFinitenessStatement` and its consequences | Not used. Its proof `001944f3` only bundles byte-identical copies of seven lower modules, accepted earlier under other tasks. |
| Whittaker finiteness: `IrreducibleCoinvariantFinitenessStatement`, parent `5ab445dc-d2b4-4072-80d1-6370870a4a26`; `LeviCuspidalCoinvariantFinitenessStatement`, `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`; the finite-length route of `5428fe2c-013c-482d-aa6e-7df43e7191aa` | Not used, and none of their modules is in the closure. No finite length of mirabolic representations or derivatives is used at all. |
| Segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292`; parent clauses (b), (d), (e), (f) | Not used. Only the cuspidal-derivative statement `SupercuspidalDerivativesStatement` and its accepted proof `fd42c8ef` (task `2e5183b1` revision 2) are used, and their closure has no segment-socle module. |
| Zelevinsky 1980 segment derivative formulas (§3.5, §9.6), segment, socle or classification results | Not used. The derivative inputs are BZ77 general derivative theory (4.4, 4.5/4.6, 4.13, 4.14, 3.5, 4.7(b)), exactness, Ze80 5.3 (authorized by `da4ad97c`) and Ze80 3.7(b) inside the 4.7(b) closure (authorized by `09565d90`). |
| Ze80 product criteria 4.2 and 9.7, the analytic or square-integrability result 9.3, classification and exhaustion theorems | Not used. |
| Unproved derivative statements, citations, conditional assemblies, theorem-valued hypotheses or pending tasks | None is used. Every lower result is applied as a published proof term. The hypotheses of `isHomogeneous_restrictedProduct` and `level_of_injective_rightMixed` are discharged by published proofs. The two helper pairs are proved in full in this candidate. |

All rows exclude mathematical conclusions, proof successors and transitive
dependents, including renamed versions. No new prerequisite task was published for
this proof.

## Appendix: import closure

The 906 modules, grouped by namespace (the `Langlands.` prefix is shown in each
group heading; the count is in parentheses):

```text
Langlands.Algebra (8): CommutingDimensionHelpers, CommutingDimensionNilpotent,
    CommutingDimensionNumerics, CommutingDimensionPrimary, CommutingDimensionRecurrence,
    SandwichDimensionBoundProof, SandwichDimensionBoundStatement, SeparatedMatrixRepresentations
Langlands.Analysis.Local (18): CompactOpenCoverUnimodularityProof,
    CompactOpenCoverUnimodularityStatement, ModularCompactAverage, QuotientAutomorphismProof,
    QuotientAutomorphismStatement, QuotientAverageReal, QuotientAveragingKernel,
    QuotientComplex, QuotientFunctional, QuotientMass, QuotientMeasure,
    QuotientMeasureExistence, QuotientMeasureExistenceStatement, QuotientMeasurePrerequisites,
    QuotientPositiveLifting, QuotientTopology, QuotientTranslation, SplitKernelQuotient
Langlands.Combinatorics (1): RelationInversions
Langlands.Group (1): HaarModulus
Langlands.Group.GL (91): AdjacentMergeShape, Basic, BlockContractionProof,
    BlockContractionStatement, BlockDeterminant, BlockIwahoriBasis, BlockIwahoriBasisStatement,
    BlockIwahoriDefinitions, BlockModulus, BlockModulusHaarProof, BlockModulusHaarStatement,
    BlockUnipotent, BlockUnipotentCoordinates, BlockUnipotentHaarProof,
    BlockUnipotentHaarStatement, Blocks, CartanProof, CartanStatement, CompactOpen,
    CountabilityProof, CountabilityStatement, DominantExponentGeneration, HeadTailBlocks,
    IntegralSubgroup, InverseTransposeIwahoriProof, InverseTransposeIwahoriStatement, Maps,
    Mirabolic, MirabolicMixedOrbitCoverageProof, MirabolicMixedOrbitCoverageStatement,
    MirabolicMixedOrbitData, MirabolicMixedOrbitRadicals,
    MirabolicMixedOrbitSectionCoefficients, MirabolicMixedOrbitSections,
    MirabolicMixedOrbitSpecializations, MirabolicMixedOrbitStages,
    MirabolicMixedProductSubgroups, MirabolicModularCharacterProof,
    MirabolicModularCharacterStatement, MirabolicModulusProof, MirabolicModulusStatement,
    MirabolicOppositeIntersection, MirabolicProjection, MirabolicRadical, Nonarchimedean,
    NonarchimedeanStatement, NormalizedCharacter, OneBlockShape, OppositeBlocks, Padic,
    PadicBlocks, PadicOppositeBlocks, PadicUpperUnipotent, ParabolicModularCharacter,
    PrincipalBlockFactorizationProof, PrincipalBlockFactorizationStatement,
    PrincipalLevelDominance, RankMaps, RankReindex, RefinementCoordinates, ReindexCongr,
    ReverseBlocks, SingleBlock, SingletonBlocks, Transvection, TriangularParabolic,
    UnramifiedCharacter, UpperBruhatBoundaryProof, UpperBruhatBoundaryStatement,
    UpperBruhatCells, UpperBruhatCoordinatesProof, UpperBruhatCoordinatesStatement,
    UpperBruhatEmbedding, UpperBruhatFiltration, UpperBruhatFiltrationGeometryProof,
    UpperBruhatFiltrationGeometryStatement, UpperBruhatLocalClosednessProof,
    UpperBruhatLocalClosednessStatement, UpperBruhatPivotProof, UpperBruhatPivotStatement,
    UpperBruhatProof, UpperBruhatRankProof, UpperBruhatRankStatement, UpperBruhatStatement,
    UpperBruhatTransposeProof, UpperBruhatTransposeStatement, UpperUnipotent,
    UpperUnipotentCompactContainmentProof, UpperUnipotentCompactContainmentStatement,
    UpperUnipotentFactorizationProof, UpperUnipotentFactorizationStatement
Langlands.HarmonicAnalysis (20): AlgebraicIntegral, AlgebraicIntegrand, Basic,
    CharacterTransport, Conductor, FiniteProductMeasureScaling, HaarConjugacy,
    PadicAdditiveConductorProof, PadicHaarScalingStatement, PadicLatticeTopology,
    PadicRectangularHaarScalingProof, PadicScalarHaarScalingProof, RowFourier,
    RowSchwartzAction, RowTensorDecompositionProof, RowTensorDecompositionStatement,
    RowTestSmoothProof, RowTestSmoothStatement, TriangularTranslationProof,
    TriangularTranslationStatement
Langlands.HarmonicAnalysis.Distribution (31): Basic, BruhatFiltrationVanishingProof,
    BruhatFiltrationVanishingStatement, CharacterAverage, CharacterAverageCovarianceProof,
    CharacterAverageCovarianceStatement, CharacterAverageFactorizationProof,
    CharacterAverageFactorizationStatement, CharacterAverageSurjectiveProof,
    CharacterAverageSurjectiveStatement, ClosedRestrictionProof, ClosedRestrictionStatement,
    ClosedSupportedDescentProof, ClosedSupportedDescentStatement, FiniteOrbitVanishingProof,
    FiniteOrbitVanishingStatement, GeneralLinear, HomogeneousPositivityProof,
    HomogeneousPositivityStatement, HomogeneousVanishingProof, HomogeneousVanishingStatement,
    LocalizationProof, LocalizationStatement, OpenRestrictionLocalityProof,
    OpenRestrictionLocalityStatement, Subspace, SupportedDescentCovarianceProof,
    SupportedDescentCovarianceStatement, SupportedRestriction, TransposeInvariantProof,
    TransposeInvariantStatement
Langlands.LinearAlgebra (12): CyclicQuotientPairingProof, CyclicQuotientPairingStatement,
    FiniteRankTrace, FiniteRankTranspose, MatrixAEvalConjugacyProof,
    MatrixAEvalConjugacyStatement, MatrixCharpolyConjugacyProof,
    MatrixCharpolyConjugacyStatement, MatrixTransposeConjugateProof,
    MatrixTransposeConjugateStatement, PolynomialModuleBoundedCyclicDecompositionProof,
    PolynomialModuleBoundedCyclicDecompositionStatement
Langlands.LocalFactor (1): Euler
Langlands.LocalFactor.Euler (1): Definitions
Langlands.LocalFactor.Harmonic (1): Statement
Langlands.LocalField (4): Canonical, Definitions, Topology, Uniformizer
Langlands.LocalField.Normalization (3): Definitions, Proof, Statement
Langlands.Representation (2): OrbitSpan, SubrepresentationLattice
Langlands.Representation.Category (7): Abelian, Basic, ClassInvariants, Contragredient,
    Subquotients, Twist, UniverseLift
Langlands.Representation.Character (5): Basic, SeparationProof, SeparationStatement,
    TransportProof, TransportStatement
Langlands.Representation.Classification (21): ConstituentRelations,
    CuspidalJacquetMultiplicityStatement, CuspidalProductContragredient,
    CuspidalProductDerivativeQuotientSupport, CuspidalProductMirabolicSupportShiftProof,
    CuspidalProductMirabolicSupportShiftStatement, MirabolicDerivativeContragredient, Segments,
    Supercuspidal, SupercuspidalContragredient, SupercuspidalContragredientAux,
    SupercuspidalContragredientProof, SupercuspidalContragredientStatement,
    SupercuspidalDerivativeVanishing, SupercuspidalDerivativesProof,
    SupercuspidalDerivativesStatement, SupercuspidalSupport, SupercuspidalSupportStatement,
    SupercuspidalSupportUniquenessProof, SupercuspidalTopDerivative, SupercuspidalTwist
Langlands.Representation.Compact (7): Definitions, FiniteMean, OrbitMeanTranslation,
    ProjectionProof, ProjectionStatement, SurjectivityProof, SurjectivityStatement
Langlands.Representation.CompactCoefficient (17): AdmissibleComplement, AdmissibleLifting,
    AdmissibleRetraction, AmbientProjector, Classes, ConditionalProjection,
    FixedLevelFiniteness, FixedVectorsFiniteDimensional, GroupTransport, Isotypic,
    IsotypicTransport, NormalSubgroupDecomposition, OrthogonalProjectorFamily,
    SemisimplicityProof, SemisimplicityStatement, TotalCompactness, TotalProjector
Langlands.Representation.Conductor (5): Congruence, Definitions, PrincipalCongruence,
    PrincipalCongruenceBasisProof, PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport (78): AssociatedAssembly, AssociatedConditional,
    AssociatedGeometricPieceVanishingProof, AssociatedGeometricPiecesEquivalenceProof,
    AssociatedGeometricPiecesProof, AssociatedGeometricPiecesStatement, AssociatedProof,
    AssociatedRankZero, AssociationForwardStatement, AssociationLawsProof,
    AssociationLawsStatement, AssociationReduction, AssociationReverseProof,
    AssociationReverseStatement, BlockMap, BlockPermutation, CompactCoefficientFinitenessProof,
    CompactCoefficientFinitenessReduction, CompactCoefficientFinitenessStatement,
    CuspidalEmbeddingProof, CuspidalTensorAssociationProof, CuspidalTensorProof,
    CuspidalTensorStatement, CuspidalityComparisonProof, CuspidalityComparisonStatement,
    DeterminantUnit, DeterminantUnitCartanSupport, DeterminantUnitCornerStructureProof,
    DeterminantUnitCornerStructureStatement, DualAveraging, FiltrationQuasicuspidality,
    GroupTransport, HarishChandraAssembly, HarishChandraBoundaryProof,
    HarishChandraBoundaryStatement, HarishChandraConverseProof, HarishChandraConverseStatement,
    HarishChandraForwardProof, HarishChandraStatement, JacquetInductionStatement,
    JacquetSubquotientProof, JacquetSubquotientStatement, JacquetVanishingHelpers,
    JacquetVanishingSmoothPieces, JacquetVanishingSubgroups, LeviAdmissibleFactorizationProof,
    LeviAdmissibleFactorizationStatement, LeviAssociation, LeviCompactPart,
    LeviDecompositionAssembly, LeviDefinitions, LeviGapVanishing,
    LeviQuasicuspidalDecompositionProof, LeviSplitContraction, LeviTensorFactorizationProof,
    LeviTensorFactorizationStatement, LeviTensorReflectionProof, LeviTensorReflectionStatement,
    MinimalConjugatingCosetsProof, MinimalJacquetProof, MinimalJacquetStatement,
    MinimalWeylTransportProof, NaturalProjectorDecomposition,
    NonassociatedJacquetSubquotientsProof, NormalizedCuspidalInductionStatement,
    PointwiseProjectorSum, ProperInductionMaps, ProperInductionProof, ProperInductionStatement,
    QuasicuspidalEmbeddingProof, QuasicuspidalLeviAdmissibilityProof,
    QuasicuspidalPrerequisitesStatement, QuasicuspidalStructureStatement,
    StandardJacquetComparisonProof, TotalConjugatingCountProof, TotalConjugatingCountStatement,
    WholeLeviTransport, ZeroRankEmbeddingProof
Langlands.Representation.Derivative (121): GeneralLinearDerivativeExactnessProof,
    GeneralLinearDerivativeExactnessStatement, GeneralLinearDerivativeLeibnizBoundary,
    GeneralLinearDerivativeLeibnizFiltrationProof,
    GeneralLinearDerivativeLeibnizFiltrationStatement, Homogeneity, Iteration,
    LeftMixedProductDerivativeProof, LeftMixedProductHigher, LeftMixedProductHomogeneityProof,
    LeftMixedProductHomogeneityStatement, LeftMixedProductPhiHatIterate,
    LeftMixedProductVanishing, LeftMixedProductZeroRank, LeibnizIndices, LeibnizPieceCompat,
    LeibnizPositiveGluing, LeibnizQuotientPiece, LeibnizRankZeroBoundary, LeibnizRankZeroGluing,
    LeibnizRestrictionCompat, LeibnizRestrictionExact, LeibnizZeroFirstPiece, LevelCalculus,
    MinusVanishing, MirabolicCharacter, MirabolicDerivativeDetectionProof,
    MirabolicDerivativeDetectionStatement, MirabolicDerivativeUnitInjective,
    MirabolicDerivativeVanishing, MirabolicDeterminant, MirabolicHighestDerivativeDescent,
    MirabolicHighestDerivativePairingProof, MirabolicHighestDerivativePairingStatement,
    MirabolicLatticeBox, MirabolicMinus, MirabolicMinusExactnessProof,
    MirabolicMinusExactnessStatement, MirabolicMinusNormalization,
    MirabolicMinusPairingTransferProof, MirabolicMinusPairingTransferStatement,
    MirabolicMixedOrbitCharacters, MirabolicPhiMinusMackey,
    MirabolicPhiMinusNondegeneratePairing, MirabolicPlus, MirabolicPlusNormalization,
    MirabolicProductMinusBoundary, MirabolicProductMinusCompatibility,
    MirabolicProductMinusCompatibilityStatement, MirabolicProductMinusLeftPhi,
    MirabolicProductMinusLeftPhiCoefficient, MirabolicProductMinusLeftPhiCompactComparison,
    MirabolicProductMinusLeftPhiHaar, MirabolicProductMinusLeftPhiHostTransport,
    MirabolicProductMinusLeftPhiIdentityComparison,
    MirabolicProductMinusLeftPhiInductionNormalization,
    MirabolicProductMinusLeftPhiLocalization, MirabolicProductMinusLeftPhiMackeyLocalization,
    MirabolicProductMinusLeftPhiNormalization, MirabolicProductMinusLeftPhiNormalizedSection,
    MirabolicProductMinusLeftPhiSection, MirabolicProductMinusLeftPhiSourceAction,
    MirabolicProductMinusLeftPhiSourceComparison, MirabolicProductMinusLeftPhiStagesComparison,
    MirabolicProductMinusLeftPsi, MirabolicProductMinusLeftPsiInduction,
    MirabolicProductMinusPhiKernelComparison, MirabolicProductMinusRightBoundary,
    MirabolicProductMinusRightPhi, MirabolicProductMinusRightPhiAssembly,
    MirabolicProductMinusRightPhiCycle, MirabolicProductMinusRightPhiCycleCoefficient,
    MirabolicProductMinusRightPhiCycleGroups, MirabolicProductMinusRightPhiIdentity,
    MirabolicProductMinusRightPhiIdentityCoefficient,
    MirabolicProductMinusRightPhiIdentityGroups, MirabolicProductMinusRightPsi,
    MirabolicProductMinusRightPsiCoefficient, MirabolicProductMinusRightPsiGroups,
    MirabolicProductMinusRightPsiZero, MirabolicProductRestriction,
    MirabolicProductRestrictionCasts, MirabolicProductRestrictionFactors,
    MirabolicProductRestrictionMackey, MirabolicProductRestrictionOrbits,
    MirabolicProductRestrictionStabilizers, MirabolicProductRestrictionStatement,
    MirabolicProductRestrictionTransport, MirabolicSmoothPhiPlus,
    MirabolicSmoothPhiPlusAdjunction, MirabolicSmoothPhiPlusIterate,
    MirabolicSmoothPhiPlusProduct, MixedProductDerivativeStatement, MixedProductRankCast,
    OrderRecursion, OrderedCuspidalProductHeadShift, OrderedCuspidalProductNondegeneracyProof,
    OrderedCuspidalProductNondegeneracyStatement, OrderedCuspidalProductTwistOne, Partial,
    PartialDerivativeJacquetComparisonProof, PartialDerivativeJacquetComparisonStatement,
    PartialDerivativeJacquetLHS, PartialDerivativeJacquetNormalization,
    PartialDerivativeJacquetRHS, PartialDerivativeJacquetRHSComparison,
    PartialLocalizationCharacter, PartialLocalizationData, ProductVanishing, RankCastCompat,
    RestrictedProductLevel, RestrictionBridge, RightMixedLevel,
    RightMixedProductDerivativeFiltrationProof, RightMixedProductDerivativeFiltrationStatement,
    RightMixedProductDerivativePositive, RightMixedProductPhiMinusDetectionProof,
    RightMixedProductZeroRank, ShortExactFunctorLaws, TopLocalizationData, ZeroRankTensor
Langlands.Representation.Dual (1): Definitions
Langlands.Representation.Exponents (1): ParabolicPair
Langlands.Representation.Filtration (38): CoinvariantVanishingStatement,
    CommonSubquotientStatement, Definitions, GluedFamily, GradedRefinementProof,
    GradedRefinementStatement, IntervalLiftProof, IntervalLiftStatement, InvariantBilinear,
    InvariantBilinearBounds, IsoTransport, JordanHolderStatement, JordanHolderTransportProof,
    LengthCriterionProof, LengthCriterionStatement, LengthTwoMatching,
    LengthTwoMatchingStatement, MultiplicityStatement, NonzeroHomCommonSubquotientProof,
    NonzeroHomCommonSubquotientStatement, ObjectDefinitions, ObjectTransport, OneStep,
    Precomposition, QuasicuspidalVanishingProof, QuotientFirstIso, QuotientTail,
    RepresentationLength, SimpleSubquotientFactorProof, SimpleSubquotientFactorStatement,
    Splicing, SubquotientAlgebraProof, SubquotientAlgebraStatement, SubsingletonProof,
    Transport, VanishingStatement, ZeroFactorDeletionProof, ZeroFactorDeletionStatement
Langlands.Representation.Filtration.Splicing (1): Basic
Langlands.Representation.Geometric (72): BlockIntersectionSplitting, BlockSixDecomposableProof,
    BlockSixDecomposableStatement, BruhatDescent, BruhatMatrixExistenceProof,
    BruhatMatrixStatement, BruhatWeylReflectionProof, ClosedSubgroupAssembly,
    ClosedSubgroupDefinitions, ClosedSubgroupMackeyProof, ClosedSubgroupStatement,
    CompactOrbitRestriction, CompactSmoothComparison, ConditionalAssembly,
    CorrectionSubgroupCoordinates, CorrectionSubgroupDiagonalHaarProof,
    CorrectionSubgroupDiagonalHaarStatement, CosetAction, CosetOrbitHomeomorph,
    CosetOrbitOrdering, FlattenedLevi, GeneralCorrectionCharacters,
    GeneralIntersectionNormalizers, GeneralIntersections, GeometricLemmaProof,
    GeometricLemmaStatement, IntersectionLeviDiagonalCharacterProof,
    IntersectionLeviDiagonalCharacterStatement, IntersectionLeviModulusBalance,
    IntersectionTransport, MonotoneBlocksProof, MonotoneBlocksStatement, OrbitRepresentatives,
    OrbitRestriction, OrbitSectionExtensionProof, OrbitSectionExtensionStatement,
    PadicCorrectionCancellationProof, PadicCorrectionCancellationStatement,
    PadicParabolicBruhatProof, ParabolicOrbitCoefficientComparison,
    ParabolicOrbitCompactComparison, ParabolicOrbitComparisonData, ParabolicOrbitHaarComparison,
    ParabolicOrbitHaarRatio, ParabolicOrbitHaarTransport, ParabolicOrbitInductionTransport,
    ParabolicOrbitJacquet, ParabolicOrbitJacquetProof, ParabolicOrbitJacquetStatement,
    ParabolicOrbitMeasureData, ParabolicOrbitNestedAction, ParabolicOrbitNormalization,
    ParabolicOrbitNormalizedCoefficient, ParabolicOrbitSectionComparison,
    ParabolicOrbitStagesCoefficient, ParabolicSupportFiltration, ParabolicSupportGradedProof,
    ParabolicSupportGradedStatement, ParabolicSupportJacquetProof,
    ParabolicSupportJacquetStatement, ParabolicSupportTransport, RefinedPositiveCharacter,
    RefinementDefinitions, RefinementFunctors, RefinementUniqueness, SmoothSupportFiltration,
    StandardIntersectionsProof, WeylDefinitions, WeylMinimalRepresentativeProof, WeylStatement,
    WeylUniquenessProof, WeylUniquenessStatement
Langlands.Representation.Hecke (18): ActionIntegrand, ActionLocalUnits, ActionProjection,
    AntiPullback, CommonInvarianceProof, CommonInvarianceStatement, Convolution, Corner,
    CornerAction, CornerDetermination, DoubleCoset, DoubleCosetSandwich, FiniteRankAction,
    IntegratedAction, IntegratedConvolution, NormalizedIndicator, SmoothTranspose, TestFunction
Langlands.Representation.Induction (66): BinaryPositiveCompact, BinaryProduct,
    BlockCharacterAbsorption, BlockEquivalence, BlockFactors, CharacterTwistProof,
    CompactAutomorphism, CompactAutomorphismIntegralProof, CompactAutomorphismIntegralStatement,
    CompactBilinearPairing, CompactCoinvariantBijectivityProof,
    CompactCoinvariantBijectivityStatement, CompactCoinvariantIntegral,
    CompactCoinvariantLocalInverseProof, CompactCoinvariantLocalInverseStatement,
    CompactLocalSection, CompactLocalSectionSpanningProof, CompactLocalSectionSpanningStatement,
    CompactLocallyConstant, CompactPairingDuality, CompactQuotientCutoff, CompactQuotientProof,
    CompactScalarProof, CompactScalarStatement, CompactSurjectivityProof,
    CompactSurjectivityStatement, CompactTransitivityProof, CompactTransitivityStatement,
    ConjugateParabolic, Definitions, Equivalences, FiniteProductTensor,
    FiniteProductTensorBijectiveProof, FiniteProductTensorBijectiveStatement,
    HeterogeneousConstruction, HeterogeneousPairs, InverseTranspose,
    NormalCoinvariantKernelProof, NormalCoinvariantKernelStatement, NormalCoinvariantMap,
    NormalCoinvariantProof, NormalCoinvariantStatement, NormalSplitComparison,
    OppositeParabolic, Parabolic, PiScalarIntegral, SingleBlock, SplitKernelCharacter,
    SplitKernelCharacterExtension, SplitKernelCompact, SplitKernelCovariance,
    SplitKernelEquivariant, SplitKernelHaarTrivial, SplitKernelIntegral,
    SplitKernelLocalizationData, SplitKernelSectionAction, SplitQuotientProof,
    SplitQuotientStatement, SplitStagesCharacterComparison,
    SplitStagesCharacterComparisonStatement, SplitStagesCharacterIntegrand,
    SplitStagesComparison, SplitStagesRetraction, StructuralStatement, SurjectivityProof,
    SurjectivityStatement
Langlands.Representation.Jacquet (38): BlockCompressionProof, BlockCompressionStatement,
    BlockPowerKernelProof, CanonicalLiftBijectivityProof, CanonicalLiftDefinitions,
    CanonicalLiftGroupTransportProof, CanonicalLiftGroupTransportStatement,
    CanonicalLiftIntertwinerNaturalityProof, CanonicalLiftIntertwinerNaturalityStatement,
    CanonicalLiftStatement, CharacterAveraging, CharacterTwistEquiv, Coinvariants,
    CompactCompressionStableDualityProof, CompactCompressionStableDualityStatement,
    CompressionStabilizationProof, CompressionStabilizationStatement, ExactProof,
    ExactStatement, Localization, LocalizationExactnessProof, LocalizationExactnessStatement,
    LocalizationTower, LocalizationTransport, Normalized, OppositeCanonicalLiftProof,
    OppositeCanonicalLiftStatement, Parabolic, PositiveCharacter,
    RefinedOppositeCanonicalLiftProof, RefinedOppositeCanonicalLiftStatement,
    RefinedOppositeCompressionProof, RefinedOppositeCompressionStatement,
    RefinedOppositePowerKernelProof, RefinedOppositeStableImageProof,
    RefinedUpperCanonicalLiftProof, SmoothTwist, StablePairingProof
Langlands.Representation.MatrixCoefficient (3): Definitions, LawsProof, LawsStatement
Langlands.Representation.Mirabolic (2): LeftMixedProductSuccessor, MixedProducts
Langlands.Representation.Parabolic (45): AdmissibilityStatement, ComposedFunctors,
    FlattenedRefinementModulusCalculation, GeometricPrerequisitesStatement,
    HeadTailProductInduction, InductionFactorMatchingProof, InductionFactorMatchingStatement,
    InductionSubrepresentation, LeviBridges, LeviInflationAdmissibilityProof,
    NaturalInductionDualityFromScalar, NaturalInductionDualityProof,
    NaturalInductionDualityStatement, NaturalJacquetDualityProof,
    NaturalJacquetDualityStatement, NormalizedAdmissibilityProof, NormalizedInductionStatement,
    NormalizedJacquetExactnessProof, NormalizedJacquetStatement, OppositeRefinementDefinitions,
    OppositeRefinementFunctors, OrderedProductRegroupingEquivalence,
    OrderedProductRegroupingProof, OrderedProductRegroupingStatement,
    ProductInductionSubrepresentation, QuotientCompactProof, RefinedInductionAdmissibility,
    RefinedInductionTensorMap, RefinedInductionTensorNormalization, RefinedInductionTensorProof,
    RefinedInductionTensorStatement, RefinementCharacter, RefinementComposition,
    RefinementCoordinatesNormalizationProof, RefinementCoordinatesNormalizationStatement,
    RefinementInductionTransitivityProof, RefinementPreimage, RefinementTransitivityStatement,
    RegroupingFactorEquivalences, ThreeBlockCarrierComparison,
    ThreeBlockInductionAssociativityStatement, ThreeBlockRefinementGeometry,
    ThreeBlockRegroupingAssembly, ThreeBlockUniverseReduction, UnipotentFiniteContainment
Langlands.Representation.RankinSelberg (24): AnalyticStatement, EqualRankFrobeniusProof,
    EqualRankFrobeniusStatement, EqualRankTrilinearAssembly, EqualRankTrilinearReduction,
    EqualRankTrilinearUniquenessStatement, FunctionalEquationStatement,
    GeneralLinearUnimodularity, HaarSymmetriesProof, HaarSymmetriesStatement,
    LastRowCompactOrbitProof, LastRowCompactOrbitStatement, LocalFactor, Measures,
    QuotientIntegrals, RankOneQuotient, RationalContinuation, RationalZeta, TwistInvariance,
    UnimodularityStatement, UnipotentQuotient, UnipotentUnimodularity,
    ZeroRowLastRowCutoffProof, ZeroRowLastRowCutoffStatement
Langlands.Representation.Schur (2): CountableDimensionProof, CountableDimensionStatement
Langlands.Representation.Shahidi (3): Geometry, Induction, TwoBlocks
Langlands.Representation.Smooth (3): Definitions, SmallRealizationProof,
    SmallRealizationStatement
Langlands.Representation.Smooth.Admissibility (6): CofinalProof, CofinalStatement,
    EmbeddingProof, EmbeddingStatement, EquivalenceProof, EquivalenceStatement
Langlands.Representation.Smooth.Contragredient (17): AdmissibleDualityProof,
    AdmissibleDualityStatement, CompactDualityProof, CompactDualityStatement, Definitions,
    ExactProof, ExactStatement, FixedVectorsDefinitions, GelfandKazhdanAssembly,
    GelfandKazhdanProof, GelfandKazhdanStatement, HomDualityProof, HomDualityStatement,
    InvariantPairingProof, InvariantPairingStatement, LawsProof, LawsStatement
Langlands.Representation.Smooth.Factorization (3): MultiplicityDefinitions,
    TwoFactorExistenceProof, TwoFactorStatement
Langlands.Representation.Smooth.FixedVectors (5): Definitions, LawsProof, LawsStatement,
    OrderProof, OrderStatement
Langlands.Representation.Smooth.Schur (2): Proof, Statement
Langlands.Representation.Smooth.SmoothPart (4): BasicProof, BasicStatement, Definitions,
    FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer (5): GroupEquivalence, PullbackProof,
    PullbackStatement, SubquotientProof, SubquotientStatement
Langlands.Representation.Tensor (17): CoinvariantReflection, ExternalFiltration,
    ExternalSubrepresentation, Filtration, Finite, FiniteEquivalences, FiniteFiltration,
    FiniteProperties, FiniteRegrouping, FlattenedGLRefinement, GLRefinement, OneFactor,
    SmoothDual, SmoothDualInjectivityProof, SmoothDualInjectivityStatement,
    SmoothDualSurjectivityProof, SmoothDualSurjectivityStatement
Langlands.Representation.Twist (16): AdmissibilityProof, AdmissibilityStatement, AlgebraProof,
    AlgebraStatement, ContinuousCharacterProof, ContinuousCharacterStatement, Definitions,
    DualProof, DualStatement, RealPower, SmoothPartDefinitions, SmoothProof, SmoothStatement,
    SubquotientDefinitions, SubquotientProof, SubquotientStatement
Langlands.Representation.Unitary (1): Basic
Langlands.Representation.Whittaker (45): Algebraic, AlgebraicTwist, BruhatCellDistribution,
    BruhatCellFactorizationProof, BruhatCellFactorizationStatement, BruhatCellInvarianceProof,
    BruhatCellInvarianceStatement, BruhatCellRestrictionVanishingProof,
    BruhatCellRestrictionVanishingStatement, BruhatCellVanishingProof,
    BruhatCellVanishingStatement, BruhatCompatibleSupportProof,
    BruhatCompatibleSupportStatement, BruhatFiberAverage, BruhatFiberCharacterCovarianceProof,
    BruhatFiberCharacterCovarianceStatement, BruhatHaarMeasureProof, BruhatHaarMeasureStatement,
    BruhatOrbitalIntegrationProof, BruhatOrbitalIntegrationStatement, BundledDualTransport,
    CharacterChange, CoefficientDistribution, CompatibleMonomialFixedProof,
    CompatibleMonomialFixedStatement, CompatibleTorus, Distribution,
    DistributionInvarianceProof, DistributionInvarianceStatement, DualTransform,
    EntrywiseCharacter, GeneralLinear, GeneralizedCoefficient, GeneralizedCoefficientDescent,
    GeneralizedCoefficientKernelProof, GeneralizedCoefficientKernelStatement,
    GeneralizedCoefficientSeparation, GenericDualTransport, Iwasawa, MirabolicQuotientMeasure,
    MultiplicityOneProof, MultiplicityOneStatement, PrerequisiteInterfaces,
    PrerequisitesStatement, Twist
Langlands.Topology (1): CompactNormCharacter
Langlands.Topology.CompactOpen (3): ConjugationStabilizer, NeighborhoodBasis,
    NeighborhoodBasisStatement
Langlands.Topology.GroupAction (2): FiniteOrbitProof, FiniteOrbitStatement
Langlands.Topology.Nonarchimedean (1): Subgroup
Langlands.Weil.Representation (6): Basic, Continuity, ContinuityProof, Determinant,
    IsomorphismInvarianceProof, Operations
```
