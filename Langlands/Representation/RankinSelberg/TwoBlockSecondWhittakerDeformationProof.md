# Proof of the entire standard-character deformation on the second lower block

Module `Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof`.

Authors: Worker 831 and Worker 15. The proof implements the transport rationale
that Worker 15 wrote in the statement's Markdown.

The theorem `Langlands.RankinSelberg.twoBlockSecondWhittakerDeformation.{uF,uW}`
proves exactly the published proposition
`Langlands.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement.{uF,uW}`.
Its scope is the scope of the statement: every prime `p`, every canonical
`p`-adic field `F`, every unitary additive character `ψ`, both positive block
ranks `m 0 + 1` and `m 1 + 1` with `h : ∑ i, (m i + 1) = t + 1`, and arbitrary
complex block representations `σ i` of full standard Whittaker type, possibly
reducible. The field universe `uF` and the carrier universe `uW` are
independent. The family is the published
`ρ_u = twoBlockSecondDeformedInduced F m h σ u`: canonical normalized lower
parabolic induction of the block tensor, with only the second block twisted by
`|det|^u`.

For every nonzero standard-character functional `ℓ₀` of `ρ_0` and every vector
`v₀`, the theorem gives a family `Wu u g` with the four clauses of the
statement: the initial coefficient at `u = 0`, membership in an actual nonzero
standard-character coefficient image of `ρ_u` for every `u`, one compact open
right level for every `u`, and analyticity at every complex `u` for every `g`.
No further hypothesis is added.

## Implemented proof

The proof transports the published first-block theorem
`Langlands.RankinSelberg.twoBlockWhittakerDeformation`
(module `TwoBlockWhittakerDeformationProof`). Write
`T = F.canonicalTopologicalData`, `η = ψ.scale (-1)`,
`S_s = twoBlockDeformedInduced F m h σ s` (first block twisted by `|det|^s`),
and `χ_u = T.determinantComplexPower (t + 1) u`. All helper declarations are
in the namespace `Langlands.RankinSelberg.TwoBlockSecondDeformation`.

### Generic lemmas

- `blockTensor_twist_apply`: if each block factor `σ i` is twisted by a
  character `c i`, the dependent block-tensor action of a Levi element `L` is
  `(∏ i, c i (L i)) •` the untwisted action. The proof checks it on pure
  tensors (`PiTensorProduct.ext`, `blockTensor_tprod`) and uses
  `MultilinearMap.map_smul_univ`.
- `inducingEquivOfApply`: identity coordinates `τ.Equiv τ'` between two
  representations of a subgroup on the same carrier that agree pointwise.
- `equiv_apply_symm_apply_rep`, `equiv_symm_apply_apply_rep`: intertwining
  of a `Representation.Equiv` and of its inverse, evaluated at transported
  vectors.
- `functionalsCongr_val_rep`, `functionalsCongr_symm_val_rep`: a functional
  transported by `Langlands.Whittaker.functionalsCongr E` (or its inverse) has
  the same matrix coefficients at transported vectors.
  `functionalsCongr_val_ne_zero` and `functionalsCongr_symm_val_ne_zero`:
  transport preserves nonzeroness.

### The comparison `E_u`

- `determinantComplexPower_oppositeParabolic`: on the lower block parabolic,
  `χ_u(q)` is the product of the block powers `|det a_i|^u` of the Levi
  projection `a` of `q`. It unfolds `χ_u` as the unramified character composed
  with the determinant and uses the published
  `TwoBlockConvergence.determinant_oppositeParabolic` with `map_prod`.
- `ambient_mul_firstBlock_eq_secondBlock`: on the lower parabolic,
  `χ_u(q) · ∏ i |det a_i|^(if i = 0 then -u else 0)` equals
  `∏ i |det a_i|^(if i = 1 then u else 0)`. This is the exponent identity
  `u + (if i = 0 then -u else 0) = (if i = 1 then u else 0)` of the
  statement's rationale, proved with `determinantComplexPower_neg` and
  `determinantComplexPower_zero`.
- `ambientCharacter u`: `χ_u` as a smooth character of `GL_(t+1)`, smooth
  because its kernel is open (`isOpen_ker_determinantComplexPower`).
- `twistComparison F m h σ u :
  (Langlands.twist χ_u S_{-u}).Equiv ρ_u` is an actual representation
  equivalence. It is the composite of two published equivalences. The first is
  `Induction.smoothInductionTwistEquiv` for the lower parabolic and the
  smooth character `ambientCharacter u`. It multiplies sections by `χ_u`, and
  it identifies the global twist of the induction with the induction of the
  restricted twist of the covariance action. The second is
  `Induction.smoothInducedEquiv` of `inducingEquivOfApply`, the identity on the
  dependent `PiTensorProduct`. Its pointwise hypothesis states that the
  restricted twist of the first-block covariance at `-u` equals the
  second-block covariance at `u`. The inverse upper half-modulus factor is
  unchanged on both sides. The block tensors are compared by
  `blockTensor_twist_apply` applied to both families, and the scalars by
  `ambient_mul_firstBlock_eq_secondBlock`, `mul_smul` and `smul_comm`.
- `zeroComparison F m h σ : S_0.Equiv ρ_0` is `Induction.smoothInducedEquiv`
  of identity coordinates. Its pointwise hypothesis is closed by rewriting
  with the published `twoBlockDeformedBlocks_zero` and
  `twoBlockSecondDeformedBlocks_zero`.

### Coefficients

- `exists_second_coefficient`: let `ℓ` be a nonzero standard-`ψ` functional of
  `S_{-u}` and `v` a vector. Then some nonzero standard-`ψ` functional `ℓ'` of
  `ρ_u` and some vector `v'` satisfy
  `χ_u(g) · ℓ(S_{-u}(g) v) = ℓ'(ρ_u(g) v')` for every `g`. The functional
  `twistFunctional` (module `Whittaker.AlgebraicTwist`) regards `ℓ` as a
  functional of `Langlands.twist χ_u S_{-u}`. Its hypothesis is
  `determinantComplexPower_upperUnipotent`: `χ_u` is trivial on the upper
  unipotent group. The proof then sets
  `ℓ' = Whittaker.functionalsCongr E_u (twistFunctional … ℓ)` and `v' = E_u v`.
  The identity follows from `functionalsCongr_val_rep`, the definition of the
  twisted action, and linearity of `ℓ`.
- `secondCoefficient_of_firstCoefficient`: the first-block clause at `-u`
  gives a nonzero functional for the inverse character of `η`. It is turned
  into a standard-`ψ` functional of `S_{-u}` by
  `Langlands.RankinSelberg.functionalsCongr` along the published character
  identity `inverseStandardCharacter_scale_neg_one`, which keeps the
  underlying linear map. `exists_second_coefficient` then applies.

### Level and analyticity

- `exists_level_twistedFamily`: if one compact open `K₀` fixes every `V s`
  on the right, then `K = K₀ ⊓ (T.determinantNorm (t + 1)).ker` fixes every
  `g ↦ χ_u(g) · V (-u) g`. The kernel is open
  (`isOpen_ker_determinantNorm`), hence closed, so `K` is compact open. On it
  `|det k| = 1`, so `χ_u(k) = 1` for every `u` (`determinantComplexPower_apply`),
  and multiplicativity of `χ_u` gives the invariance.
- `analyticAt_twistedFamily`: for fixed `g`, `z ↦ χ_z(g)` is
  `(|det g| : ℂ) ^ z` with positive real base `|det g|`
  (`determinantComplexPower_apply`). It is analytic by `AnalyticAt.cpow`
  (base in the slit plane, from `Complex.ofReal_mem_slitPlane`).
  Composition with `z ↦ -z` (`AnalyticAt.comp_of_eq`) and multiplication
  preserve analyticity.

### Main theorem

`twoBlockSecondWhittakerDeformation` proceeds as follows.

1. The block hypothesis is transferred from the standard character of `ψ` to
   the standard character of `η`. It uses the published
   `isOfWhittakerType_standard_iff_inverse` and
   `standardCharacter_scale_neg_one`.
2. Initial data for the first-block theorem are
   `ℓs = functionalsCongr (inverseStandardCharacter_scale_neg_one ψ t).symm
   ((Whittaker.functionalsCongr E0).symm ℓ₀)` and `E0.symm v₀`, with
   `E0 = zeroComparison F m h σ`. `ℓs` is nonzero by
   `functionalsCongr_symm_val_ne_zero`.
3. `twoBlockWhittakerDeformation` with `η` gives a family `V` with clauses
   `hV0`, `hVu`, `hVK` and `hVa`.
4. The new family is `Wu u g = χ_u(g) · V (-u) g`. Clause 1 uses
   `χ_0 = 1`, `-0 = 0`, `hV0` and `functionalsCongr_symm_val_rep`. Clause 2 is
   `secondCoefficient_of_firstCoefficient` applied to `hVu (-u)`. Clause 3 is
   `exists_level_twistedFamily`, and clause 4 is `analyticAt_twistedFamily`.

The equivalence `E_u` is constructed in the proof; it is not a hypothesis.
The coefficient membership at every `u` comes from the actual transported
functional on the actual carrier of `ρ_u`. The uniform level is constructed
explicitly from the first-block level.

## Scope: deformation only, no factor specialization

This module proves only the deformation of Whittaker coefficients itself. It
does not specialize the family into any Rankin–Selberg integral or local
factor. In particular, it proves no convergence, integrability or analyticity
of zeta integrals or determinant-slice integrals, and no gamma or L factor
identity, multiplicativity, or adjacent-rank factor relation. It also does not
remove a large-real-twist restriction from a factor identity. JPSS Sections
(6.1) and (6.3) refer to (4.5) for such a reduction to large positive real
`u`, as recorded in the statement's Markdown. Those subsequent
specializations need their own statements and proofs.

## Imports and excluded inputs

Beyond the target statement and `TwoBlockWhittakerDeformationProof`, the module
imports published Library modules for the determinant of lower block matrices
(`TwoBlockJacquetConvergence.RadicalIwasawa`), functional transport
(`WhittakerTypeEquivalence`, `LocalFactor`), the character-change adapter
(`WhittakerGammaAdapters`, used only for
`isOfWhittakerType_standard_iff_inverse`), induction equivalences
(`Induction.CharacterTwistProof`, `Induction.Equivalences`), twisted
functionals (`Whittaker.AlgebraicTwist`), and Mathlib's
`Analysis.SpecialFunctions.Complex.Analytic` for `AnalyticAt.cpow`. The proof
uses no gamma or L multiplicativity, no lower-to-upper reversal, and no
analyticity of an integral.

## Provenance

The statement is an internal transport of the lemma of JPSS 1983 (source ID
`jpss-1983-rankin-selberg`), Section (4.5), printed pages 408–409. The
statement's Markdown records its provenance and the Section 6 uses on printed
pages 427 and 432. The implemented proof follows the transport rationale given
there, with the direct lower construction of `E_u` rather than the reversal
route. It does not formalize a printed proof of the second-block assertion.
