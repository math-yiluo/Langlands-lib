# Non-unitarizability of `ν^s ρ × ν^(-s) ρ` for `s < -k/2`

Author: Worker 235 (Lean implementation and proof documentation).

`Langlands.Classification.twoBlockLargeExponentNonUnitarizable` proves exactly the
published proposition
`Langlands.Classification.TwoBlockLargeExponentNonUnitarizable.{uF,uV} F T`
of `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement`,
for every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p` and every
`T : F.TopologicalData`. The universes `uF` and `uV` are independent and the
theorem has no further hypotheses.

The proposition says: under `T.topology`, for `k > 0`, an irreducible
unitarizable smooth representation `ρ` of `GL_k(F)` and a real `s < -k/2`, the
actual upper normalized product
`T.twistedProductInduced (Shahidi.twoBlocks k k hk hk) (twoBlockFactors hk hk ρ ρ) ![s, -s]`,
that is `ν^s ρ × ν^(-s) ρ` on `GL_{2k}(F)` with `ν = |det|`, admits no invariant
positive definite Hermitian form.

## Implemented argument

The proof exhibits an unbounded matrix coefficient. A smooth functional `μ` and
a smooth vector `f` are constructed with `|μ(π(a^n) f)|` growing like
`‖c‖^n`, where `a = diag(ϖ I_k, I_k)` and `‖c‖ = q^{-k(k/2+s)} > 1`. An
invariant positive form would make every such coefficient bounded. The
helper results live in namespace
`Langlands.Classification.TwoBlockExponentNonUnitarizability` and are grouped in
the sections below.

### Section `Bounded`

`exists_bound_smoothDualPairing`. Let `ρ` be an admissible representation of a
topological group `G` in which compact open subgroups are cofinal among open
subgroups, and let `b` be an invariant positive form. The published
`InvariantPositiveForm.toSmoothDual_surjective` (the Riesz step for admissible
representations) writes any smooth functional `ℓ` as `b(w, ·)`. Equip the carrier
with the inner product space structure of `b.toInnerProductCore`. Invariance of
`b` gives `‖ρ(g) v‖ = ‖v‖`, and Cauchy–Schwarz (`norm_inner_le_norm`) gives
`|ℓ(ρ(g) v)| ≤ ‖w‖ ‖v‖` for every `g`.

### Section `Average`

This section works with `P ≤ G`, a representation `σ` of `P` and the smooth
induced representation `Induction.smoothInduced P σ`.

- `eval_isLocallyConstant`: every smooth induced function is locally constant,
  by the existing `Langlands.Induction.eval_isLocallyConstant` theorem in
  `Induction.CompactQuotientProof`, specialized to complex coefficients.
- `averageFunctional`: for a measure `ν` that is finite on compacts, a compact
  open subgroup `K` and `ℓ ∈ Module.Dual ℂ V`, put
  `μ(f) = ∫_{x ∈ K} ℓ(f(x⁻¹)) dν(x)`. The integrand is continuous
  (`continuous_averageIntegrand`), hence integrable on the compact set `K`
  (`integrableOn_averageIntegrand`), and `μ` is linear.
- `averageFunctional_mem_smoothVectors`: if `ν` is left invariant, then `μ` is
  fixed by `K` under the dual action. For `k ∈ K`, the translate is
  `f ↦ μ(π(k⁻¹) f)`. Its integrand is `ℓ(f(x⁻¹k⁻¹))` on `K`. Rewriting the set
  integral as an integral of an indicator function and substituting
  `x ↦ k⁻¹ x` (`integral_mul_left_eq_self`) returns `μ(f)`, since
  `k⁻¹ x ∈ K ↔ x ∈ K`. Hence `μ` is a smooth functional, `averageSmoothDual`.
- `averageFunctional_translate`: if `f(k g) = u` for every `k ∈ K`, then
  `μ(π(g) f) = ν(K) ℓ(u)`, because `(π(g) f)(x⁻¹) = f(x⁻¹ g)` and `x⁻¹ ∈ K`.

### Section `Abstract`

`not_isUnitarizable_of_growth`. Suppose `Induction.smoothInduced P σ` is
admissible, compact open subgroups are cofinal, `ν` is a left invariant measure
that is finite on compacts and positive on open sets, `K` is a compact open
subgroup, `ℓ(w) ≠ 0`, `1 < ‖c‖`, and `f(k A^n) = c^n w` for all `n ∈ ℕ` and
`k ∈ K`. Then the representation is not unitarizable. Given a form, the
`Bounded` section bounds `‖μ(π(A^n) f)‖` by a constant `C`. By
`averageFunctional_translate` this quantity is `ν(K) ‖c‖^n ‖ℓ(w)‖`, with
`0 < ν(K) < ∞` because `K` is open and compact. `pow_unbounded_of_one_lt`
yields `n` with `‖c‖^n > C / (ν(K) ‖ℓ(w)‖)`, a contradiction.

`eval_doubleCosetSection_mul_pow` computes the vector `f`. Let `e` be fixed by
`P ∩ K` (`Induction.conjOpenSubgroup P K 1`). Let `f_e` be the published local
section `Induction.compactDoubleCosetSection P σ K hK 1 e he`, supported on `PK`
with `f_e(q k') = σ(q) e`. Suppose `A ∈ P` satisfies `σ(A) e = c e`, and every
`k A^m` with `k ∈ K` factors as `q A^m k'` with `q ∈ P ∩ K` and `k' ∈ K`. Then
`f_e(k A^m) = σ(q) σ(A)^m e = c^m e`.

### Section `GeneralLinearLevel`

- `leviSubgroup_le_parabolic` and `unipotentSubgroup_le_parabolic` re-prove that
  the Levi and unipotent subgroups of a block shape lie in its upper parabolic.
  The Library versions are private.
- `exists_mul_blockScalar_pow`. Let `K` have the block Iwahori factorization
  `HasBlockIwahoriFactorization` and let the block scalar `A = blockScalar a` be
  weakly contracting. The Library factorization of `k⁻¹ ∈ K` is in the order
  `k⁻¹ = l x u`: a lower unipotent part `l`, then a Levi part `x`, then an upper
  unipotent part `u`, each in `K`. Inverting gives `k = u⁻¹ x⁻¹ l⁻¹`, so
  `k A^m = (u⁻¹ x⁻¹) A^m (A^{-m} l⁻¹ A^m)`. Here `q = u⁻¹ x⁻¹` lies in `P ∩ K`.
  Weak contraction is closed under products (`IsWeaklyContracting.mul`, by
  induction from `isWeaklyContracting_one`), so `a^m` is weakly contracting. The
  lower-part condition of the factorization then puts `A^{-m} l⁻¹ A^m` in the
  lower Iwahori part of `K`. This is the reordering requested in the task's
  suggested route.
- `not_isUnitarizable_normalizedParabolicInduced`. Let `τ` be an admissible
  representation of the block Levi, `a` weakly contracting, and `e` a vector with
  `ℓ(e) ≠ 0` such that the Levi element `blockScalarLevi a` acts on `e` by `c`
  in the inflated representation twisted by `δ_P^{1/2}`
  (`T.parabolicHalfModulus B`), with `1 < ‖c‖`. Then
  `T.normalizedParabolicInduced B τ` is not unitarizable. The proof checks the
  hypotheses of `not_isUnitarizable_of_growth`:
  - The inducing representation `σ_P` is admissible by
    `Parabolic.leviInflationAdmissibility` and `isAdmissible_twist_iff`, because
    the kernel of the half modulus is open.
  - The induced representation is admissible by
    `Parabolic.normalizedInductionAdmissibility`.
  - The stabilizer `H` of `e` is open in `P`, so `H = P ∩ O` for an open
    `O ∋ 1` of `G`. `exists_compactOpenSubgroup_hasBlockIwahoriFactorization`
    gives a compact open `K ⊆ O` with a block Iwahori factorization, so `P ∩ K`
    fixes `e`.
  - Cofinality is `GeneralLinear.compactOpen_cofinal`, and `ν` is the Haar
    measure of `GL_n(F)` for the Borel σ-algebra.
  - The growth hypothesis is `eval_doubleCosetSection_mul_pow` applied with
    `exists_mul_blockScalar_pow`.

### Section `TwoBlock`

- `exists_dual_tprod_eq_one`. A pure tensor `⊗ x_i` of nonzero vectors has a
  functional with value one. Choose `φ_i` with `φ_i(x_i) = 1`
  (`Module.Projective.exists_dual_eq_one`) and lift the multilinear map
  `v ↦ ∏ φ_i(v_i)` to `PiTensorProduct`.
- `exists_segmentFactor_scalar_eigen`. For an irreducible unitarizable smooth
  `ρ` of `GL_r(F)`, a real `t` and `z ∈ F^×`, there are `x ≠ 0` and `ω` with
  `‖ω‖ = |z|^{rt}` and the scalar matrix `z I_r` acting on `x` in `ν^t ρ`
  (`T.segmentFactor ρ t`) by `ω`. The argument:
  - `ρ` is admissible by `CuspidalSupport.cuspidalEmbedding` (first component).
  - The published `unitarizableCentralCharacter` then supplies a central
    character of norm one that acts by scalars on the centre.
  - The carrier is nontrivial because the group-algebra module is simple.
  - `ω = ν^t(z I_r) χ(z)`, and `T.norm_determinantPowerCharacter_scalar` gives
    its norm.

### Final theorem

Fix `k`, `hk`, `ρ`, `s < -k/2`, and put `B = Shahidi.twoBlocks k k hk hk`,
`u = ![s, -s]`, `ϖ = T.uniformizerUnit` and `a = ![ϖ, 1]`.

1. For each block `i`, `exists_segmentFactor_scalar_eigen` gives `x_i ≠ 0` and
   `ω_i`, with `‖ω_0‖ = |ϖ|^{ks}` and `‖ω_1‖ = |1|^{k(-s)} = 1`.
2. The twisted blocks `σ_i` are admissible: `ρ` is admissible, and the twisting
   character `T.determinantPowerCharacter` has open kernel.
   `FiniteTensor.isAdmissible_external` makes `B.blockTensor σ` admissible.
3. The functional `ℓ` from `exists_dual_tprod_eq_one` has `ℓ(⊗ x_i) = 1`.
4. Put `e = ⊗ x_i`. By `T.parabolicHalfModulus_section`,
   `B.leviProjection_section`, `B.blockTensor_tprod` and
   `MultilinearMap.map_smul_univ`, the Levi element `blockScalarLevi a` acts on
   `e` by `c = δ^{1/2}(blockScalarLevi a) · ω_0 ω_1`, where `δ^{1/2}` is
   `T.leviHalfModulus B`.
5. Weak contraction of `a` reduces to the one pair `(0,1)`:
   `|ϖ · 1⁻¹| = q^{-1} ≤ 1`, using `T.normalizedAbs_uniformizer`.
6. `T.leviModulus_twoBlocks` and `T.determinantNorm_scalar` give
   `δ(blockScalarLevi a) = (|ϖ|^k)^k / 1 = |ϖ|^{k²}`. Since
   `T.leviHalfModulus_apply` is the square root,
   `‖c‖ = |ϖ|^{k²/2} |ϖ|^{ks} = |ϖ|^{k(k/2+s)}`.
7. Since `0 < |ϖ| < 1` and `k(k/2+s) < 0`, `‖c‖ > 1`
   (`Real.one_lt_rpow_of_pos_of_lt_one_of_neg`).
8. `not_isUnitarizable_normalizedParabolicInduced` now applies. The target
   representation is by definition the normalized parabolic induction of
   `B.blockTensor σ`.

In the language of the suggested route, `μ(π(a^n) f_e) = ν(K') c^n ℓ(e)` with
`|c| = q^{-k(k/2+s)}`. This matches step 4 of the route up to the positive
factor `ν(K')`.

## Provenance

The statement isolates one sentence of Zelevinsky 1980, Proposition 1.11, proof,
printed p.175 (PDF p.12). After assuming irreducibility of `ρ × νρ`, the
sketch there says that the matrix coefficients of `π_s` can be computed
directly and that "for large |s| there exists a non-bounded matrix coefficient
of π_s. Therefore such π_s cannot be unitary". The PDF text layer garbles the
Greek letters of this passage. The source gives no
computation, so the computation above is an internal derivation following the
route in the task contract. It is not a verbatim reproduction of a published
proof. Source: `zelevinsky-1980-induced-ii`, retained at
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`,
SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`
(verified 2026-10-30).

## Independence audit

**Imports.** The module imports
`TwoBlockExponentNonUnitarizabilityStatement`, `Unitary.HermitianDual`,
`Unitary.CentralCharacterProof`, `CuspidalSupport.CuspidalEmbeddingProof`,
`Tensor.FiniteProperties`, `Induction.CompactLocalSection`,
`Group.GL.BlockIwahoriBasis`, `Category.Contragredient`,
`Parabolic.NormalizedAdmissibilityProof`, `Group.GL.UnramifiedCharacter` and
`LocalField.Normalization.Proof`, together with two Mathlib measure theory
modules.

**Import closure.** The transitive `Langlands` import closure has 157 modules.
It was computed on Library base `5a2bfe4d` by following `import` lines. The
only `Classification` modules in it are definition-level or statement modules:
`ConstituentRelations`, `Essential`, `LanglandsData`, `Segments`,
`Supercuspidal`, `SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalTwist`, `Tempered`, the
target statement, and `TwoSupercuspidalProductStructureStatement`. The last
module is imported by the target statement itself. It defines the propositions
`TwoSupercuspidalAdjacentProductComposition` and `...Jacquet`; this proof
neither states nor uses them.

**Forbidden modules and names.** No module in the closure is a segment,
multisegment, ordered, tempered-block, square-integrable,
regular-exhaustion, product-irreducibility, segment Jacquet-formula, or
adjacent-reducibility module of the forbidden tasks. No module mentions
`SegmentSpecialEssentialSquareIntegrability`,
`SquareIntegrableLanglandsClassification`, `GenericSegmentProductUniqueness`,
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
`SegmentSocleProductIrreducibility`, `SegmentFullJacquetFormula`,
`SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`,
`SegmentSpecialJacquetExponentNormFormula` or
`TwoSupercuspidalAdjacentProductReducible`.

**Mathematical dependencies.** The mathematical inputs are:

- the Riesz representation of smooth functionals for an admissible
  representation with an invariant positive form;
- admissibility of irreducible smooth representations of `GL_r(F)` (the
  cuspidal embedding theorem, as suggested by the task);
- the unitary central character of an irreducible admissible unitarizable
  representation;
- admissibility of external tensor products and of normalized parabolic
  induction;
- the block Iwahori basis, the compact local section of induced
  representations, the modulus of the two-block Levi, and Haar measure.

No derivative formula (Ze80 §3.5 or §9.6, BZ77), segment product irreducibility
criterion (Ze80 4.2 or 9.7), square-integrability result (Ze80 9.3), or
classification or exhaustion theorem is used. The proof does not depend on the
adjacent reducibility task `0988a3e0` or its target.

## Axioms

`#print axioms`-style inspection of
`Langlands.Classification.twoBlockLargeExponentNonUnitarizable` reports only
`propext`, `Classical.choice` and `Quot.sound`. The module contains no `sorry`,
`admit`, new axiom or theorem-valued hypothesis.
