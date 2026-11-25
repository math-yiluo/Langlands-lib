# BZ77 Theorem 4.11 for ordered cuspidal products (proof)

This module proves the theorem
`Langlands.Derivative.orderedCuspidalProductNoDegenerateSubmodules` (line 692). Its
type is exactly the published proposition
`Langlands.Derivative.OrderedCuspidalProductNoDegenerateSubmodules.{uF,uV} F T` of
module `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement`:

```lean
theorem orderedCuspidalProductNoDegenerateSubmodules {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    OrderedCuspidalProductNoDegenerateSubmodules.{uF, uV} F T
```

This is Bernstein–Zelevinsky 1977, Theorem 4.11, sufficient direction (printed
p. 456, one-based PDF p. 17). The module adds no axioms and has no `sorry` or
`admit`. The theorem
has no premise beyond the target's own telescope. Its universe parameters are
exactly `uF uV`. A Lake build of the module has 0 errors and 0 warnings, and
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
which the statement's page cites, are not needed and are not imported.

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

The gaps in the source argument are resolved as follows.

- **Reduction to an irreducible `ω`.** It is avoided. The binary step proves
  homogeneity of `(D × P)|_P` for all nonzero subrepresentations `W` at once,
  through the published helper `RestrictedProductLevel.isHomogeneous_restrictedProduct`.
  The 4.13(a) dichotomy is applied to `W` through its intersection with
  `σ = range i`, the comap of `σ` along `W ↪ (D × P)|_P`. If this intersection is
  nonzero, Case 1 applies to it, and exactness of the derivatives
  (`level_le_of_injective`, `level_le_max_of_isShortExact`, from
  `Mirabolic.minusExactness`) squeezes the level of `W` between the level of the
  intersection and the level of the whole product. If it is zero, then `W`
  injects into `π/σ = D × (P|_P)` (Case 2). It uses no finite-length, Artinian or submodule-existence premise.
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

The use of Zelevinsky 1980 Proposition 5.3 goes beyond the BZ77 text.

## Helper pairs

Two helper pairs belong to this proof. Each has its own Markdown.

- `Langlands/Representation/Derivative/OrderedCuspidalProductHeadShift.{lean,md}`.
  It proves
  `irreducible_support_of_injective` and `headShift_false`, the head-shift step of
  Case 2 through the published Lemma 4.7(b) `cuspidalProductMirabolicSupportShift`.
  It imports the 4.7(b) proof module, `OrderedCuspidalProductTwistOne`,
  `Induction.SingleBlock` and `Category.UniverseLift`.
- `Langlands/Representation/Derivative/OrderedCuspidalProductTwistOne.{lean,md}`.
  It proves
  `exponent_eq_zero` and `twist_one_ne_self` (`ρ.twist 1 ≠ ρ` for every cuspidal
  datum). The proof evaluates an equivalence `A ≅ |det|^s A` at the scalar
  uniformizer, using the published admissible Schur lemma
  `admissibleSchur_centralCharacter`.

The Library's existing proof of `νρ ≠ ρ`,
`RepeatedCuspidalSupport.twist_one_ne_self`, is not used. It rests on
`CuspidalIntegralTwistFreenessProof`, which belongs to the excluded individual
special-head/reverse-socle existence route.

## Published inputs

Every theorem used has a published proof, or is a lemma inside a published
definition or proof module.
Rows give the module (prefix `Langlands.Representation.` unless stated), the
Library commit that introduced it, and the declarations used.

| Module | Library commit | Used |
| --- | --- | --- |
| `Derivative.OrderedCuspidalProductNondegeneracyStatement` | `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762` | the target proposition only |
| `Classification.SupercuspidalDerivativesProof` | `c5eebf94883144ce00adc4e252995c28082f08a7` | `Classification.supercuspidalDerivatives` (BZ77 §4.4) |
| `Derivative.LeftMixedProductHomogeneityProof` | `da0312e3777850c14b211f6245ff5b08af56f616` | `leftMixedProductHomogeneity` (Ze80 5.3) |
| `Derivative.MirabolicProductRestriction` | `7114a390` and `368b3cec` | `mirabolicProductRestriction` (BZ77 4.13(a)) |
| `Derivative.MirabolicProductMinusCompatibility` | `f6b45fe9` | `mirabolicProductMinusCompatibility` (BZ77 4.13(b,c)); components `RightPhiShortExact`, `RightPhiBoundary` |
| `Derivative.RightMixedProductPhiMinusDetectionProof` | `9a8ca758` | `rightMixedProductPhiMinusDetection` (BZ77 4.13(d)) |
| `Derivative.LeftMixedProductDerivativeProof` | `b4b4160d` | `leftMixedProductDerivative` (BZ77 4.14(a)) |
| `Derivative.MirabolicMinusExactnessProof` | `9a8ca758` | `Mirabolic.minusExactness` |
| `Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | `e3944f76`; statement module `GeneralLinearDerivativeLeibnizFiltrationStatement` | `generalLinearDerivativeLeibnizFiltration` (BZ77 4.5/4.6), `GeneralLinearDerivativeLeibnizFiltrationStatement.filtration`, `leibnizIndices_top`, `mem_leibnizIndices`, `leibnizPiece_obj` |
| `Derivative.MirabolicDerivativeDetectionProof` (through `LevelCalculus`) | `81727e81` | `mirabolicDerivativeDetection` (BZ77 3.5), inside `level_pos` |
| `Derivative.RestrictedProductLevel`, `Derivative.RightMixedLevel`, `Derivative.RestrictionBridge`, `Derivative.ProductVanishing`, `Derivative.LevelCalculus` | `7114a390`; `LevelCalculus`: `5e4a58e8` | `isHomogeneous_restrictedProduct`, `level_leftMixed_le`, `le_level_leftMixed`, `isHomogeneous_mirabolicRankCast`, `RestrictionBridge.generalLinearDerivative_succ_obj_eq`, `isHomogeneous_of_single_order`, `level_mirabolicRankCast`, `mapsShortExact_mirabolicDerivativeOfOrder`, `map_injective_of_exact`, `isHomogeneous_of_iso`, `iso_hom_injective`, `level_eq_of_isHomogeneous` |
| `Derivative.ZeroRankTensor` | `9a8ca758` | `binaryRightZeroIso`, `binaryRightZeroEquiv` |
| `Parabolic.HeadTailProductInduction` | `a8a83747` | `headTailProductInductionIso`, `headTailProductFactors` |
| `Langlands.Group.GL.HeadTailBlocks` | `feda7e54` | `headRank`, `tailRank`, `headIndex`, `tailIndex`, `tailShape`, `headTailShape`, `headRank_add_tailRank`, `headRank_pos`, `tailRank_pos` |
| `Induction.BinaryProduct` | `e40be87d` | `binaryNormalizedProductFunctor`, `binaryNormalizedProductPositiveIso`, `binaryPairFamilyFunctor` |
| `Langlands.Group.GL.MirabolicOppositeIntersection` | `f75d5c19` | `BlockShape.binary` |
| `Langlands.Group.GL.SingleBlock` | `15eedb12` | `BlockShape.singleBlockIndex`, `singleBlock_size`, `eq_singleBlockIndex`, `BlockShape.rankCast` |
| `Parabolic.RegroupingFactorEquivalences`, `Parabolic.ThreeBlockRegroupingAssembly` | `9de4c692` and `65f39f42` | `singleBlockTransportedProductEquiv`, `normalizedProductInductionObjEquiv`, `Parabolic.equivTrans` |
| `Category.UniverseLift` | `feda7e54` | `SmoothRep.universeLift`, `universeLiftEquiv`, `isIrreducible_universeLift_iff` |
| `Derivative.Homogeneity` | `c76b7751` | `IsHomogeneous`, `level`, `HasNonzeroDerivative`, `level_le`, `level_eq_iff`, `le_level_of_hasNonzeroDerivative`, `mirabolicDerivativeOfOrder`, `mirabolicRankCast` |
| `Derivative.Iteration` | `355c0523` | `generalLinearDerivative`, `generalLinearRestriction`, `generalLinearRankCast`, `mirabolicDerivative` |
| `Induction.BlockFactors` | `f8488ce7` | `normalizedProductInductionFunctor` |
| `Classification.SupercuspidalTwist` | `6700bb75` | `supercuspidalClassRealPowerTwist` |
| `Classification.Supercuspidal`, `Category.Basic`, `Category.Subquotients` | `6473a6d8` (their versions at the audit base) | `SupercuspidalRep`, `supercuspidalProperty`, `isSupercuspidal_of_equiv`, `isoClass`, `SmoothRep.mkIso`, `SmoothRep.equivOfIso`, `SmoothRep.subrepresentation` |
| `Filtration.Definitions` | general filtration definitions | `RepFunctorFiltration` (`step`, `graded`, `zero`, `top`) |
| `Tensor.OneFactor` | extracted from `Induction.BinaryProduct` | `BinaryTensor.firstFactor` |

The helper pairs use in addition the published Lemma 4.7(b)
`Classification.cuspidalProductMirabolicSupportShift` (commit `9a8ca758`), the
admissible Schur lemma `admissibleSchur_centralCharacter` (commit `01a58491`),
`Induction.SingleBlock` and the definitions of
`Classification.SupercuspidalSupport`. Their Markdown lists the details.

The §4.4 proof `Classification.SupercuspidalDerivativesProof` was checked. It
proves the statement `Langlands.Classification.SupercuspidalDerivatives`, and
its inputs are the multiplicity-one proof `Whittaker.MultiplicityOneProof`
(Gelfand–Kazhdan) and the statement module
`Classification.SupercuspidalDerivativesStatement`. Its 303-module import closure contains no segment,
socle, multisegment or exhaustion module. Its `Classification` modules are
`ConstituentRelations`, `Segments` (cuspidal data and their twists only),
`Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalDerivativeVanishing`,
`SupercuspidalDerivativesProof`, `SupercuspidalDerivativesStatement`,
`SupercuspidalSupport`, `SupercuspidalTopDerivative` and `SupercuspidalTwist`. The
statement module `SupercuspidalDerivativesStatement` is the isolated
cuspidal-derivative statement (it imports only `Classification.Supercuspidal`,
`Derivative.Iteration` and `HarmonicAnalysis.Basic`), not the segment-socle
statement module. So it is independent of the segment-socle part of the six
statements of `Classification.SegmentSocleDerivativesStatement`.

## Scope of the exclusions

- Only fully proved and published BZ77 general derivative theory is used. The
  closure avoids the excluded results listed below and the segment-socle part
  of the six statements of `Classification.SegmentSocleDerivativesStatement`.
  This file records the audit.
- The 4.7(b) proof imports `CuspidalProductDerivativeQuotientSupport` and
  `WholeLeviTransport`; its closure was audited.
- `cuspidalProductMirabolicSupportShift` is imported with its whole closure,
  including `CuspidalProductDerivativeQuotientSupport`, `WholeLeviTransport` and
  `PartialDerivativeJacquetComparisonProof`. A fully proved general comparison
  of derivatives and Jacquet modules such as Ze80 3.7(b) counts as general
  derivative theory. An import whose audit finds an excluded result or module
  is not used.
- `leftMixedProductHomogeneity` (Ze80 5.3) is imported with its closure,
  under the same conditions. `Classification.Supercuspidal*`,
  `Whittaker.Algebraic`, `Whittaker.GeneralLinear` and `Whittaker.Iwasawa` are
  checked explicitly below.
- The nine definition and statement modules introduced with the excluded socle
  exhaustion, `TwoSupercuspidalNonadjacentProductIrreducible` and the six
  statements of `SegmentSocleDerivativesStatement`, listed in the closure audit
  below, stay in the closure. The exclusions target the excluded mathematical
  conclusions and whatever depends on them, not general infrastructure
  introduced with them. The nine modules were checked at Library `b1c8a5e8`:
  they hold definitions and a few generic lemmas, and their project imports are
  generic too. None states or uses socle exhaustion, the two-supercuspidal
  product theorem or any other excluded conclusion. Each module is documented
  below with its content and this check. A module that contains or depends on
  an excluded conclusion is not imported; the two listed next are replaced by
  local proofs.

Two modules on excluded routes are not imported:

- `Classification.CuspidalIntegralTwistFreenessProof` (individual
  special-head/reverse-socle existence route). `OrderedCuspidalProductTwistOne`
  is used in its place.
- `Derivative.TopProduct` with `Filtration.SingletonIso` (introduced with
  `SegmentHeadProductIrreducibility`). The dimension of the top derivative of a
  binary product is derived locally from the Leibniz filtration, in the section
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

**Provenance.** Every module was matched against the publication records of
the Library, whether a record introduces the module or only bundles a copy.
889 modules have such records. The other 17 have none:

- the three modules of this proof (this module and the two helpers);
- 14 extractions of infrastructure from other modules: `Group.GL.OneBlockShape`,
  `Group.GL.RankReindex`, `Group.GL.ReindexCongr`, `Group.GL.Transvection`,
  `HarmonicAnalysis.FiniteProductMeasureScaling`,
  `HarmonicAnalysis.PadicLatticeTopology`, `Representation.Compact.OrbitMeanTranslation`,
  `Representation.CuspidalSupport.WholeLeviTransport`,
  `Representation.Derivative.MirabolicDeterminant`,
  `Representation.Derivative.ShortExactFunctorLaws`, `Representation.OrbitSpan`,
  `Representation.Smooth.Transfer.GroupEquivalence`, `Representation.Tensor.OneFactor`
  and `Topology.CompactNormCharacter`.

The provenance of every module, followed transitively through the recorded
requirements, was compared with the excluded results (all of them, including
the Whittaker finiteness results and the mirabolic finite-length route). Four
excluded results appear. In every case the module is a definition or statement
module, and none of them states or proves an excluded conclusion:

- Six general filtration and tensor adapters were introduced with socle
  exhaustion: `Filtration.ObjectTransport`, `Tensor.FiniteFiltration`,
  `Tensor.ExternalFiltration`, `Tensor.ExternalSubrepresentation`,
  `Parabolic.InductionSubrepresentation` and
  `Parabolic.ProductInductionSubrepresentation`. They are reached only
  through the chain `RestrictedProductLevel` ← `RightMixedLevel` ←
  `ProductVanishing` ← `ProductInductionSubrepresentation` ←
  `ExternalSubrepresentation` ← `ExternalFiltration` ← `FiniteFiltration` ←
  `ObjectTransport`. So they are reached through `RestrictedProductLevel` and
  through the Ze80 5.3 proof, which imports `RestrictedProductLevel`. The
  list-counting API `Combinatorics.RelationInversions` was introduced with the
  same result. It is reached only through the §4.4 proof
  (`SupercuspidalDerivativesProof` ← `Whittaker.MultiplicityOneProof` ← … ←
  `Group.GL.UpperBruhatFiltration`).
- `Derivative.MirabolicMinusNormalization`, the Haar-normalization adapter for
  `Ψ⁻`/`Φ⁻`, was introduced with the two-supercuspidal nonadjacent product
  result. It is reached only through the 5.3
  proof (`LeftMixedProductPhiHatIterate` ← `MirabolicSmoothPhiPlusProduct` ← … ←
  `MirabolicPlusNormalization`).
- `Classification.SupercuspidalDerivativesStatement` is part (a) of the six
  statements of `Classification.SegmentSocleDerivativesStatement`. It is the
  cuspidal-derivative statement of the §4.4 proof, which may be used. No
  segment-socle module of the six statements is in the
  closure. In particular, neither `SegmentSocleDerivativesStatement` nor any
  `HighestDerivativeSupportShift` module is in it.
- The publication of the excluded `SupercuspidalCoinvariantFinitenessProof` only
  bundles copies of seven modules: `Derivative.MirabolicDerivativeVanishing`,
  `MirabolicHighestDerivativeDescent`, `MirabolicHighestDerivativePairingProof`,
  `MirabolicPhiMinusNondegeneratePairing`,
  `PartialDerivativeJacquetComparisonStatement`, and
  `Geometric.ParabolicOrbitSectionComparison` and `ParabolicOrbitStagesCoefficient`.
  These copies are byte-identical to the Library files. The modules were
  published earlier with other results: the BZ77 3.8 proof, the positive
  two-block Jacquet comparison statement and two geometric definition modules.
  They are reached through the 4.7(b) closure, and
  `MirabolicDerivativeVanishing` also through the
  detection proof. `Whittaker.SupercuspidalCoinvariantFinitenessStatement`, the
  excluded conclusion, is not in the closure.

**Modules of excluded results kept in the closure.** The nine modules above,
introduced with socle exhaustion, the two-supercuspidal nonadjacent product and
the six statements of `SegmentSocleDerivativesStatement`, stay in the closure
(see "Scope of the exclusions"). Each is listed here with its content.
Module names have the prefix `Langlands.Representation.` except
`Langlands.Combinatorics.RelationInversions`.

| Module | Introduced with | Content | Project imports |
| --- | --- | --- | --- |
| `Filtration.ObjectTransport` | socle exhaustion | Transport of an `ObjectRepFiltration` along a group homomorphism (`comp`, `compGradedEquiv`) and along an equivalence of representations (`mem_equivTransport_subrepresentation`, `equivTransportGradedEquiv`) | `Filtration.LengthTwoMatching` |
| `Tensor.FiniteFiltration` | socle exhaustion | Finite tensor products of representations: `congrEquiv`, `slotEquiv`, the filtration induced by a filtration of one slot (`slotFiltration`), its graded pieces and the injectivity of their maps | `Tensor.Finite`, `Tensor.Filtration`, `Filtration.ObjectTransport` |
| `Tensor.ExternalFiltration` | socle exhaustion | The same slot filtration for an external tensor product (`externalSlotFiltration`, its graded pieces and maps) | `Tensor.FiniteFiltration` |
| `Tensor.ExternalSubrepresentation` | socle exhaustion | The subrepresentation of an external tensor product generated by a subrepresentation of one slot (`externalSlotSubrepresentation`) with its `⊥`, `⊤`, order, `≠ ⊥` and `≠ ⊤` lemmas, and `leftTensorImage_le_iff` | `Tensor.ExternalFiltration` |
| `Parabolic.InductionSubrepresentation` | socle exhaustion | Normalized parabolic induction of a subrepresentation (`normalizedInducedSubrepresentation`) with its `⊥`, `⊤`, order, `≠ ⊥` and `≠ ⊤` lemmas; `exists_valueSubrep_eval`, `valueSubrep_le_iff` | `Parabolic.InductionFactorMatchingProof` |
| `Parabolic.ProductInductionSubrepresentation` | socle exhaustion | The subrepresentation of a normalized block product induced from a subrepresentation of one factor (`normalizedProductSlotSubrepresentation`) with the same lemmas; a proper nonzero subrepresentation of one factor gives a proper nonzero one of the product | `Tensor.ExternalSubrepresentation`, `Parabolic.InductionSubrepresentation`, `Induction.BlockFactors` |
| `Combinatorics.RelationInversions` | socle exhaustion | For a relation on a type, `relationPairCount` and `relationInversions` of lists, with append, vanishing, monotonicity and swap lemmas | Mathlib and Lean only |
| `Derivative.MirabolicMinusNormalization` | `TwoSupercuspidalNonadjacentProductIrreducible` | Half-modulus character identities, the characters `psiMinusHaarInverseHalf` and `phiMinusHaarInverseHalf` with their formulas and open kernels, and the Haar-normalization identities `psiMinus_haarNormalization` and `phiMinus_haarNormalization` | `Group.GL.MirabolicModulusProof`, `Derivative.MirabolicMinus` |
| `Classification.SupercuspidalDerivativesStatement` | the six statements of `SegmentSocleDerivativesStatement` (part (a)) | The Prop-valued definition `SupercuspidalDerivatives` (BZ77 §4.4), which may be used and which the §4.4 proof `SupercuspidalDerivativesProof` proves | `Classification.Supercuspidal`, `Derivative.Iteration`, `HarmonicAnalysis.Basic` |

These modules are reached as described above. The six filtration and tensor
adapters enter through `RestrictedProductLevel` and the Ze80 5.3 proof.
`RelationInversions` and `SupercuspidalDerivativesStatement` enter through the
§4.4 proof, and `MirabolicMinusNormalization` through the 5.3 proof. The
check was made at `b1c8a5e8`. The declarations of the nine
modules are the definitions and lemmas named in the table. None of them states
or uses socle exhaustion, the irreducibility or structure of a product of two
supercuspidals, a segment or multisegment result, or any other excluded
conclusion. The recursive import closures of the nine modules have 7, 19, 20,
21, 60, 72, 1, 62 and 59 modules, in the order of the table. In each of these
closures the only modules introduced with an excluded result are modules from
this table.

**Names.** All 906 Lean files were scanned for the excluded declaration
and module names: every excluded name listed in this file, the three Whittaker
coinvariant-finiteness statements, `CuspidalIntegralTwistFreeness`,
`RepeatedCuspidalSupportShift`, `TopProduct`, `topProductTensorEquiv` and
`segmentDerivative`. There is no Lean hit.

**Supercuspidal and Whittaker modules.** The `Classification.Supercuspidal*`
modules in the closure are cuspidal infrastructure:

- `Supercuspidal` (definitions);
- `SupercuspidalTwist`;
- `SupercuspidalSupport`;
- `SupercuspidalSupportStatement`;
- `SupercuspidalSupportUniquenessProof`;
- `SupercuspidalContragredient`, `…Statement`, `…Aux` and `…Proof`;
- `SupercuspidalDerivativeVanishing`, `SupercuspidalTopDerivative`,
  `SupercuspidalDerivativesStatement` and `SupercuspidalDerivativesProof`.

None states a segment, socle, classification or exhaustion result.
`Whittaker.Algebraic`, `Whittaker.GeneralLinear` and `Whittaker.Iwasawa`
are definitions of Whittaker functionals and models.
The other Whittaker modules in the closure are the Gelfand–Kazhdan
multiplicity-one development: `Whittaker.MultiplicityOneProof`, its statement,
`PrerequisitesStatement` and the Bruhat-cell distribution lemmas. No
coinvariant-finiteness module is in the closure:

- not `IrreducibleCoinvariantFinitenessStatement`;
- not `LeviCuspidalCoinvariantFinitenessStatement`;
- not `SupercuspidalCoinvariantFinitenessStatement`;
- no module of their proofs or of the mirabolic finite-length route.

The only finite-length modules are the general `Filtration` Jordan–Hölder and
length APIs, which are not used to prove any finiteness of derivatives.

## Condition-by-condition exclusion audit

Two checks support the table. The mathematical proof chain above (this module, the
two helpers and the published inputs listed) uses none of the excluded results.
The import closure audit confirms this at the level of modules, their
provenance and their names. A name scan cannot exclude a
renamed result, so each row also records the mathematical inspection.

| Excluded conclusion | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | Not imported and not used. The proof concerns products of supercuspidal blocks, not segment products. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom` and their proofs | Not used. |
| `SegmentSocleProductIrreducibility` | Not used. |
| `AdjacentUnlinkedSegmentSocleSwap` | Not used. |
| `TwoSegmentSocleCommutation` | Not used. |
| `LinkedSegmentSocleGluing` | Not used. |
| `OrderedMultisegmentSocleExistence` | Not used. |
| `MultisegmentSocleExhaustion`, socle exhaustion | No conclusion used. The closure contains seven definition modules introduced with it (general filtration and tensor adapters and a list-counting API). They enter through `RestrictedProductLevel`, the Ze80 5.3 proof and the §4.4 proof, and contain no socle or exhaustion statement; see the closure audit. |
| Analytic segment classification | Not used. |
| Special-head multisegment exhaustion | Not used. |
| Ordered strong-head existence | Not used. |
| Quotient coverage | Not used. |
| Ordered conversion | Not used. |
| Tempered uniqueness | Not used. |
| `GenericSegmentProductUniqueness` | Not used. |
| `SquareIntegrableLanglandsClassification` | Not used. |
| Square-integrable exhaustion | Not used. |
| Regular exhaustion | Not used. |
| `SegmentSpecialEssentialSquareIntegrability` | Not used. |
| `SegmentHeadProductIrreducibility`, special-head criterion and special-head product irreducibility | Not used. The definition modules introduced with it, `Derivative.TopProduct` and `Filtration.SingletonIso`, are not imported. The dimension of the top derivative of a binary product is proved locally from the Leibniz filtration. `SegmentHeadProductIrreducibility` is a consumer of the theorem. |
| Individual special-head/reverse-socle existence | Not used. `CuspidalIntegralTwistFreenessProof` and `RepeatedCuspidalSupport` are not in the closure. `νρ ≠ ρ` is proved in `OrderedCuspidalProductTwistOne`. |
| Individual segment-socle/reverse-head existence | Not used. |
| `SegmentFullJacquetFormula` and its proof `segmentFullJacquetFormula` (`Classification.SegmentFullJacquetProof`) | Not used. The only Jacquet input, inside the 4.7(b) closure, is the general geometric lemma together with the Ze80 3.7(b) comparison. |
| `SegmentHeadJacquetFormula` | Not used. |
| `SegmentSocleJacquetFormula` | Not used. |
| `SegmentSpecialJacquetExponentNormFormula` | Not used. |
| `TwoSupercuspidalNonadjacentProductIrreducible` | No conclusion used. The definition module introduced with it, `MirabolicMinusNormalization` (the `Ψ⁻`/`Φ⁻` Haar adapter), is in the 5.3 closure. It contains no product or irreducibility statement; see the closure audit. |
| `TwoSupercuspidalProductStructure` | Not used. No product structure or two-factor conclusion appears. |
| `SupercuspidalCoinvariantFinitenessStatement` (all-character single-block) and its consequences | Not used. The publication of its proof only bundles byte-identical copies of seven lower modules, published earlier with other results. |
| Whittaker finiteness: `IrreducibleCoinvariantFinitenessStatement`; `LeviCuspidalCoinvariantFinitenessStatement`; the mirabolic finite-length route | Not used, and none of their modules is in the closure. No finite length of mirabolic representations or derivatives is used at all. |
| Segment-socle part of the six statements of `Classification.SegmentSocleDerivativesStatement`; their clauses (b), (d), (e), (f) | Not used. Only the cuspidal-derivative statement `SupercuspidalDerivativesStatement` and its proof `SupercuspidalDerivativesProof` are used, and their closure has no segment-socle module. |
| Zelevinsky 1980 segment derivative formulas (§3.5, §9.6), segment, socle or classification results | Not used. The derivative inputs are BZ77 general derivative theory (4.4, 4.5/4.6, 4.13, 4.14, 3.5, 4.7(b)), exactness, Ze80 5.3 and Ze80 3.7(b) inside the 4.7(b) closure. |
| Ze80 product criteria 4.2 and 9.7, the analytic or square-integrability result 9.3, classification and exhaustion theorems | Not used. |
| Unproved derivative statements, citations, conditional assemblies or theorem-valued hypotheses | None is used. Every lower result is applied as a published proof term. The hypotheses of `isHomogeneous_restrictedProduct` and `level_of_injective_rightMixed` are discharged by published proofs. The two helper pairs are proved in full. |

All rows exclude mathematical conclusions, the modules that prove them and
transitive dependents, including renamed versions.

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
