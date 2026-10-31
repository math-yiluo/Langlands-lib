# Adjacent two-supercuspidal products: the algebraic part of Ze80 1.11(b)

Author: Worker 892. Worker 163 preserved the Lean source from the author's
shared draft and updated the dependency count and publication-scope wording
when preparing the separate ordered Jacquet proof.

This internal module proves the length-two structure and the actual ordered
Jacquet factors of Zelevinsky 1980, Proposition 1.11(b). It also derives the
complete proposition `Langlands.Classification.TwoSupercuspidalProductStructure`
from four explicit inputs (`productStructure_of`). Those inputs are theorem
statements that this module does not prove.

The nonzero-vector argument reuses
`Langlands.CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible`
from `QuasicuspidalLeviAdmissibilityProof`.

All declarations defined here are in the namespace
`Langlands.Classification.TwoSupercuspidalAdjacent`.

## Conventions

- `𝔅 = Shahidi.twoBlocks k k hk hk` is the standard two-block shape `(k, k)` of
  `GL_{k+k}`, with `0 < k`. Block `0` is the upper-left block.
- For a smooth representation `σ` of the Levi `𝔅.Levi F.Carrier`,
  `π = T.normalizedParabolicInduced 𝔅 σ.representation` is the actual upper
  normalized induction. It uses positive half-modulus covariance and right
  translation. `T.normalizedJacquet 𝔅` is the actual normalized Jacquet module,
  with the inverse half-modulus.
- The product in the target is
  `P = (T.normalizedProductInductionFunctor 𝔅).obj (twoBlockFactors hk hk ρ.obj ρ'.obj)`.
  `ρ` is in block `0` and `ρ'` in block `1`. By the published `rfl` lemmas
  `normalizedProductInductionFunctor_obj` and `normalizedProductInduced_eq`,
  `P.representation` is definitionally
  `T.normalizedParabolicInduced 𝔅 σ.representation` with
  `σ = FiniteTensor.externalSmoothObject (twoBlockFactors hk hk ρ.obj ρ'.obj)`,
  that is `ρ ⊗ ρ'`. The swapped tensor `σ'` is `ρ' ⊗ ρ`.
- Universes: the field is in `uF` and the input carriers in `uV`. The induced
  representation, its subspaces, quotients and Jacquet modules have carriers in
  `max uF uV`. The tensor targets `ρ ⊗ ρ'` and `ρ' ⊗ ρ` have carriers in `uV`.
  The equivalences are actual `Representation.Equiv` values across these
  universes.
- Twists: the adjacency hypothesis is
  `ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
  ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass`, that is
  `ρ' ≅ νρ` or `ρ ≅ νρ'` with `ν = |det|`. The disjuncts are taken exactly in
  this order.

## Shapes and minimal permutations of `(k, k)` (sections `Shapes`, `Pieces`, `Structure`)

- `eq_of_levisAssociated`: the only standard shape associated to `(k, k)` is
  `(k, k)`. An associated shape has the same number of blocks, and the
  surjective block map preserves block sizes
  (`TotalConjugatingCount.length_eq`, `blockMap_surjective`, `size_blockMap`,
  `shape_ext`).
- `card_minimalConjugating`: there are exactly two minimal permutations
  conjugating the `(k, k)` Levi to itself. Proof: the published
  `totalConjugatingCount` sums these counts over all shapes to `2! = 2`, and
  every other shape contributes zero by `eq_of_levisAssociated`.
  `levisAssociated_self` follows.
- A minimal permutation `w` from `(k, k)` to itself is determined by
  `blockMap 𝔅 𝔅 w 0 ∈ Fin 2` (`eq_of_blockMap_zero_eq`, using
  `TotalConjugatingCount.eq_of_blockValue_eq`).
  - If `blockMap … w 0 = 0`, then `w` lies in the block Weyl group
    (`mem_blockWeyl_of_blockMap`). Transport along `w` is then equivalent to
    the identity (`fixEquiv`, the published `transportWeylEquiv`).
  - If `blockMap … w 0 = 1`, then `w` maps the first block onto the second in
    order, and vice versa (`apply_castAdd_of_blockMap`,
    `apply_natAdd_of_blockMap`, using `StrictMono.range_inj_of_wellFoundedLT`).
    Pulling a Levi element back along `w` exchanges its two blocks
    (`leviConjugation_symm_zero`, `leviConjugation_symm_one`). So transport of
    `A₀ ⊗ A₁` along `w` is equivalent to `A₁ ⊗ A₀` by the tensor flip
    (`swapEquiv`, built from the published `Shahidi.pairSwap` and
    `Shahidi.pairSwap_external`).

## Separation of `ρ ⊗ ρ'` from `ρ' ⊗ ρ` (sections `Separation`, `Adjacent`)

- `external_firstBlock`: a `g` acting by a scalar `c` on `A₀`, placed in the
  first block with `1` in the second (`firstBlock`), acts by `c` on `A₀ ⊗ A₁`.
- `not_equiv_swap`: let `z` act by scalars `c` on `A₀` and `c'` on `A₁`, let
  `A₁ ≅ χ A₀` for a character `χ` with `χ z ≠ 1`, and let both tensors be
  nonzero. Then `A₀ ⊗ A₁` and `A₁ ⊗ A₀` are not equivalent. The first block
  copy of `z` acts by `c` on the first tensor and by `c'` on the second, and
  `c' = χ(z) c ≠ c`.
- `isEmpty_equiv_swap_of_twist` applies this with `z` the scalar uniformizer
  matrix of `GL_k` and `χ = T.determinantPowerCharacter k 1 = ν`. The scalars
  are the central characters from the published `admissibleSchur_centralCharacter`.
  `χ z = q^(-k) ≠ 1` by `IntegralTwistFreeness.scalar_uniformizer_value` and
  `1 < q`. `isEmpty_equiv_swap` covers both adjacency disjuncts: the second
  case is the first with the roles exchanged, and the equivalence is inverted.
- `tensor_irreducible_cuspidal`: `ρ ⊗ ρ'` is irreducible and Levi cuspidal,
  from the published `glCuspidalTensor` (`twoBlockCuspidal`,
  `twoBlockCuspidal_obj` identify the factor families).

## Generic helpers (sections `Quotients`, `SmoothSubquotients`)

These hold for representations of any monoid over `ℂ`, or any bounded
lattice.

- `quotientRepBotTopEquiv`, `nonempty_equiv_quotientRep_bot`,
  `nonempty_equiv_quotientRep_top`: the successive quotients `quotientRep ⊥ ⊤`,
  `quotientRep ⊥ S` and `quotientRep S ⊤` of `LengthCriterionProof` are
  equivalent to the representation, to `S`, and to the quotient by `S`.
- `twoStep_pieces_of_exact`: for an exact sequence `0 → ρ → σ → τ → 0` with
  injective `i` and surjective `q`, the two graded pieces of
  `LengthTwo.twoStep i.range` are equivalent to `ρ` and to `τ`.
- `second_factor_of_series`: given two series of length two with simple
  factors, suppose the first factor of `t` is `≅ X`, each factor of `s` is
  `≅ X` or `≅ Y`, and the factors of `s` are not both `≅ X`. Then the second
  factor of `t` is `≅ Y`. Proof: the published `jordanHolderSeriesComparison`.
- `hasCompositionSeriesLength_two`: `⊥ ⋖ S ⋖ ⊤` gives
  `HasCompositionSeriesLength A 2`, with the filtration `0 ⊂ S ⊂ A` and
  `LengthCriterionProof.hasSimpleFactors_iff_covBy`.
- `inf_eq_bot_and_sup_eq_top`: two distinct elements, each covering `⊥` and
  covered by `⊤`, have `a ⊓ b = ⊥` and `a ⊔ b = ⊤`.
- `nonempty_equiv_quotient_of_compl`: if `S ⊓ S' = ⊥` and `S ⊔ S' = ⊤`, then
  the composite `S' → V → V/S` is an actual equivalence.
- `subrepresentationEquiv`: `SmoothRep.subrepresentation A S` has the same
  action as `S.toRepresentation` (identity equivalence).
- `eq_one_of_one_add_eq_two`: in `ℕ∞`, `1 + x = 2` gives `x = 1`.

## The core lemma `properStructure`

Hypotheses: `hnon : NonassociatedJacquetSubquotientsTheorem F T (k + k)`,
`hfilt : AssociatedJacquetFiltrationTheorem F T (k + k)`, smooth `σ, σ'` on the
`(k, k)` Levi, `σ` irreducible and quasicuspidal, `σ ≇ σ'`, and for every
block-swapping minimal permutation `w`, transport of `σ` along `w` is
equivalent to `σ'`.

Conclusions, for `π = T.normalizedParabolicInduced 𝔅 σ.representation`:

- `jacquetLength T {𝔅} π = 2`, and `⊥ ≠ ⊤` among invariant subspaces of `π`.
- For every invariant subspace `S ≠ ⊥, ⊤`: `⊥ ⋖ S` and `S ⋖ ⊤`. Also
  `T.normalizedJacquet 𝔅 S.toRepresentation ≅ σ` and
  `T.normalizedJacquet 𝔅 (π / S) ≅ σ'`.

Implemented proof:

1. `hfilt` at the shape `C = 𝔅` gives a filtration `s` of `r(π)` with `r`
   graded pieces. The pieces are in bijection `e` with the minimal
   conjugating permutations and each is equivalent to a transport of `σ`.
   So `r = 2`, every piece is irreducible (`isIrreducible_transport`), and
   `repLength r(π) = 2` (`repLength_eq_of_hasSimpleFactors`). Hence the
   summed length over `{𝔅}` is `2`.
2. `{𝔅}` contains every shape associated to `𝔅`. So the published
   `one_le_jacquetLength_stepQuotient` (from `minimalNonzeroJacquet` and
   `hnon`) and `count_strictMono` make the count
   `S ↦ (jacquetLength T {𝔅} S).toNat` strictly monotone. Its values are `0`
   at `⊥` (`count_bot`) and `2` at `⊤` (`count_top`). Hence `⊥ ≠ ⊤`, a proper
   `S` has count `1`, and `⊥ ⋖ S ⋖ ⊤` (`LengthTwo.covBy_of_count`).
3. Additivity on `0 → S → π → π/S → 0` (`jacquetLength_eq_add_of_exact`)
   gives Jacquet length `1` for `S` and for `π/S`. Both Jacquet modules are
   then irreducible (`repLength_eq_one_iff`).
4. Frobenius reciprocity (`Parabolic.FirstAdjointness.equiv`) turns the
   nonzero inclusion `S → i(σ)` into a nonzero intertwiner `r(S) → σ`. Both
   sides are irreducible, so Schur's lemma
   (`IsIrreducible.bijective_or_eq_zero`) makes it an equivalence:
   `r(S) ≅ σ`.
5. Exactness of the normalized Jacquet functor (`normalizedJacquetMap_exact`)
   gives `0 → r(S) → r(π) → r(π/S) → 0`. The filtration `t` of `r(π)` by the
   image of `r(S)` has pieces `≅ σ` and `≅ r(π/S)`
   (`twoStep_pieces_of_exact`). Both are irreducible.
6. Each piece of `s` is `≅ σ` (block-fixing permutation, `fixEquiv`) or
   `≅ σ'` (block-swapping permutation, hypothesis). A piece `≅ σ` must come
   from a block-fixing permutation, otherwise `σ ≅ σ'`. Both pieces cannot be
   `≅ σ`: their permutations would both fix the first block and be equal, so
   `e` would not be injective. `second_factor_of_series` then gives
   `r(π/S) ≅ σ'`.

The route uses only Frobenius reciprocity, not second adjointness.

## Per-instance assembly `adjacentStructure`

Take `hnon`, `hfilt` at rank `k + k`, supercuspidal `ρ, ρ'` of `GL_k` and the
adjacency hypothesis. With `σ = ρ ⊗ ρ'` and `σ' = ρ' ⊗ ρ`:
`tensor_irreducible_cuspidal` gives irreducibility and quasicuspidality,
`isEmpty_equiv_swap` gives `σ ≇ σ'`, and `swapEquiv` gives the transport
hypothesis. `properStructure` then applies to `P`. The statement has two
parts.

- Jacquet part, with no reducibility hypothesis. For every invariant subspace
  `S ≠ ⊥, ⊤` of `P.representation`, the result has actual equivalences.
  `((T.normalizedJacquetFunctor 𝔅).obj (SmoothRep.subrepresentation P S)).representation`
  is `≅ ρ ⊗ ρ'` (through `subrepresentationEquiv` and
  `JacquetLength.normalizedJacquetEquiv`).
  `((T.normalizedJacquetFunctor 𝔅).obj (SmoothRep.quotient P S)).representation`
  is `≅ ρ' ⊗ ρ`.
- Composition part, under `¬ P.IsIrreducible`. Since `⊥ ≠ ⊤` and the lattice of
  invariant subspaces is not simple, some `S ≠ ⊥, ⊤` exists. Then:
  - `HasCompositionSeriesLength P.obj 2` follows from `⊥ ⋖ S ⋖ ⊤`.
  - `S` is the only such subspace, up to equality of invariant subspaces.
    Suppose `S' ≠ S` were another one. Then `S ⊓ S' = ⊥` and `S ⊔ S' = ⊤`,
    so `S' ≅ P/S`, and `r(S') ≅ r(P/S)`. With `r(S') ≅ ρ ⊗ ρ'` and
    `r(P/S) ≅ ρ' ⊗ ρ`, this contradicts `isEmpty_equiv_swap`.
  - For every `S' ≠ ⊥, ⊤`, the smooth subrepresentation and the smooth
    quotient are irreducible. The covering relations make the successive
    quotients irreducible (`LengthTwo.isIrreducible_gradedRep_of_covBy`), and
    these are equivalent to the actual subrepresentation and quotient.

## Conditional assembly `productStructure_of`

`productStructure_of F T ha hred hnon hfilt : TwoSupercuspidalProductStructure F T`
takes four inputs:

- `ha : TwoSupercuspidalNonadjacentProductIrreducible F T` (part (a));
- `hred : TwoSupercuspidalAdjacentProductReducible F T` (reducibility of the
  adjacent products, published statement
  `TwoSupercuspidalAdjacentReducibilityStatement`);
- `hnon n : NonassociatedJacquetSubquotientsTheorem F T n` and
  `hfilt n : AssociatedJacquetFiltrationTheorem F T n` for every rank.

The composition conjunct is `(adjacentStructure …).1 (hred …)`, and the
Jacquet conjunct is `(adjacentStructure …).2`. A proof of the complete
proposition must discharge the four inputs. This module proves none of them.
The companion `TwoSupercuspidalAdjacentJacquetProof` supplies the two Jacquet
inputs and proves the Jacquet conjunct without either irreducibility or
reducibility as a premise; the other two conjuncts remain separate obligations.

## Provenance

Zelevinsky, *Induced representations of reductive p-adic groups II*
(1980), Proposition 1.11, printed p.175 (PDF p.12). Conventions are in §1.1
and §§1.8–1.10 (literature ID `zelevinsky-1980-induced-ii`). Ze80 refers to
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), §2.16(1), printed pp.449–450 (literature ID
`bernstein-zelevinsky-1977-induced-i`). There the Jacquet module of `i(σ)`
along the inducing Levi is filtered by the Weyl transports of `σ`. If these are
pairwise inequivalent, the induced representation is irreducible or has length
two.

The implemented argument follows BZ77 §2.16(1) for `GL_{2k}` and `(k, k)`. The
two transports are `ρ ⊗ ρ'` and `ρ' ⊗ ρ`. The Jacquet count bounds the length.
The order of the Jacquet factors comes from first adjointness, exactness of the
Jacquet functor and Jordan–Hölder comparison, not from second adjointness.
The inequivalence of `ρ ⊗ ρ'` and `ρ' ⊗ ρ` in the adjacent case comes from
central characters. This is internal content, and Ze80 does not spell it out.

## Dependency audit

Imports: the published statement modules
`TwoSupercuspidalProductStructureStatement` and
`TwoSupercuspidalAdjacentReducibilityStatement`, and the published modules
`CuspidalSupport.InducedJacquetCount`, `CuspidalSupport.BlockPermutationTensor`,
`CuspidalSupport.CuspidalTensorProof`, `CuspidalSupport.MinimalJacquetProof`,
`Classification.CuspidalIntegralTwistFreenessProof`,
`Parabolic.NaturalFirstAdjointness`, `Filtration.LengthTwoMatching`,
`Filtration.JordanHolderProof` and `Shahidi.IntertwiningInduced`.

The recursive project import closure has 185 modules, including this module.
None is a module or theorem of a
task on the contract's independence list, and a text search of their sources
finds none of the excluded declaration names. None is a derivative, segment
product, segment Jacquet, square-integrability, tempered, classification or
exhaustion result. The one segment-named module, `Classification.Segments`, is
imported by `CuspidalIntegralTwistFreenessStatement` and
`SupercuspidalSupport`. It contains only definitions and elementary lemmas, and
none of its declarations is used here.

Proof dependencies are the following published theorems:

- `totalConjugatingCount`, `minimalNonzeroJacquet` and `glCuspidalTensor`;
- `admissibleSchur_centralCharacter` and `IntegralTwistFreeness.scalar_uniformizer_value`;
- `Parabolic.FirstAdjointness.equiv` and `normalizedJacquetMap_exact`;
- `jordanHolderSeriesComparison`;
- the length and count lemmas of `JacquetLengthDetector` and
  `InducedJacquetCount`, including `one_le_jacquetLength_stepQuotient`;
- `Shahidi.pairSwap_external` and `transportWeylEquiv`.

Only algebraic constructions of `Shahidi.IntertwiningInduced` are used (the
tensor flip), with no analytic intertwining operator. The theorem-valued
statements `NonassociatedJacquetSubquotientsTheorem`,
`AssociatedJacquetFiltrationTheorem`, `TwoSupercuspidalAdjacentProductReducible`
and `TwoSupercuspidalNonadjacentProductIrreducible` enter only as explicit
hypotheses.
