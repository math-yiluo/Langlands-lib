# A uniform regular numerator for the actual standard compact operator

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. Its main
theorem `exists_uniform_standardCompactOperator_numerator` supplies the
numerator hypothesis `hpoly` of the published
`parabolicLevi_standardCompactRationalOn_of_dominated`, in a general setting.

Fix the published data of `CompactIntertwiningFamilies`: a source decomposition
`P = M ⋉ U`, a target decomposition `P' = M ⋉ U'`, a compact open `K` with
`G = P K = P' K`, the actual quotient measures, and the squared-modulus
compatibility. Fix a set `Ω` of unramified parameters at which the actual
standard-integral domain is the whole source (`hfull`). Assume further:

- an opposite subgroup `Ubar` of the source radical, normalized by `M`, with
  `P ∩ Ubar = 1`, and an element `g` with the published
  `Jacquet.HasOppositeIwahoriContractionBasis U M Ubar g`;
- an element `a` and a subgroup `Obar` with
  `Jacquet.HasOppositeIwahoriContractionBasis U' M Obar a` for the target
  radical;
- `A` admissible and of finite length;
- `U'` locally compact (an instance argument).

Then there is one nonzero `b` in the concrete regular algebra
`unramifiedRegularFunctions ν` such that `χ ↦ b(χ) •` (the published
`standardCompactOperator` at `χ`) is a polynomial operator family on `Ω`. That
is, it satisfies the published `IsPolynomialOperatorOn`: for every source
compact section `f`, the family `χ ↦ b(χ) • A_χ f` is a finite expansion with
regular coefficients and fixed target compact sections. The scalar `b` is
chosen before `f`. The theorem does not claim that `b` is nonzero at points of
`Ω`; that is supplied later by the published local divisibility and weak
continuity theorems.

## Auxiliary statements

- `inductionScalarRegularOf p` is the regular function `χ ↦ δ^{1/2}(p) χ(proj p)`
  for `p ∈ P`: a constant times the published character evaluation
  `unramifiedEvaluationRegular` at `proj p`. Its value is `inductionScalar χ p`
  of `CompactInductionGeneration` (`inductionScalarRegularOf_apply`).
- `standardCompactOperator_compactTranslate`: the standard compact operator at
  `χ` intertwines the source and target parameter translates `compactTranslate`
  of `CompactInductionGeneration`. The operator is the compact-picture
  conjugate of the published `fullSourceIntertwiner`, an actual intertwiner of
  the two inductions.
- `eval_standardCompactOperator_eq`: the value of the operator output at `k ∈ K`
  is the published `compactIdentityValue` of the `k`-translate of the input.
  The proof combines the published `standardCompactOperator_eval`,
  `unramifiedLeviInductionCompactEquiv_translate` and `operator_right_action`.
- `compactPictureAction_mem_compactFixed`: if every `K`-conjugate of `H₁ ∩ K`
  lies in `L₀`, every `K`-translate of an `L₀`-fixed section is fixed by `H₁`.
- `isPolynomialOn_compactTranslate_standardCompactOperator`: assume that `b`
  makes the identity values of all `H₁`-fixed sections polynomial, and that the
  `K`-conjugates of `H₁ ∩ K` lie in `L₀ ⊆ K`. Then for every `L₀`-fixed source
  section `φ` and every `g ∈ G`, the family
  `χ ↦ T'_χ(g)(b(χ) • A_χ φ)` is polynomial. Here `T'_χ` is the target
  parameter translate. The family consists of target sections fixed by
  `K ∩ g L₀ g⁻¹`, because `A_χ φ` is fixed by `L₀ ∩ K`. Its value at `y ∈ K`
  is computed by writing `y g = p' k'` with `p' ∈ P'` and `k' ∈ K`, a choice
  independent of `χ`. The published extension formula gives
  `δ'^{1/2}χ(p') • A(proj' p')(b(χ) • identity value of R(k') φ)`, and `R(k') φ`
  is `H₁`-fixed. Each value is therefore polynomial. The published
  `isPolynomialOn_compactFixed_of_eval` of `CompactIntertwiningCompression`
  then makes the whole family polynomial.

## Proof of the main theorem

1. `exists_regularTranslateSpan_eq_top` of `CompactInductionGeneration` gives a
   compact open `L₀ ≤ K` such that every source compact section is
   `∑ᵢ cᵢ(χ) • T_χ(gᵢ) φᵢ` for all `χ`. Here the `cᵢ` are regular and the `φᵢ`
   are `L₀`-fixed.
2. The normal core of `L₀ ∩ K` in the compact group `K` (Mathlib's
   `Subgroup.normalCore`) has finite index and is closed, hence open
   (`Subgroup.isOpen_of_isClosed_of_finiteIndex`). Its image in `G` is open. The
   target basis gives a compact open `H₁` inside it with
   `IsIwahoriContraction H₁ U' M Obar a`. Thus `H₁ ≤ K`, and every
   `K`-conjugate of `H₁` lies in `L₀`.
3. The published `exists_regular_compactIdentityValue_numerator` of
   `CompactIntertwiningCompression`, applied to `H₁`, gives `b ≠ 0` making the
   identity values of all `H₁`-fixed sections polynomial.
4. For a source section `f`, the equivariance gives
   `b(χ) • A_χ f = ∑ᵢ cᵢ(χ) • T'_χ(gᵢ)(b(χ) • A_χ φᵢ)`. Each summand is
   polynomial by the preceding lemma and the published `regular_smul`, and
   finite sums are polynomial.

## Scope and provenance

The opposite subgroups, contracting elements, Iwahori bases, admissibility,
finite length and full convergence are explicit hypotheses. The module does not
construct these data for the host's rational-point radicals. It proves neither
domination, nor nonvanishing of `b` on `Ω`, nor `StandardCompactRationalOn`, nor
the host theorem. All steps are internal compositions of the published Library
declarations named above, of `CompactInductionGeneration` and of
`CompactIntertwiningCompression`; no literature theorem replaces a proof.
Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après
Harish-Chandra* (2003), IV.1, printed pp.280–282, obtains rationality instead
from a Jacquet-module filtration; that route is not used.
