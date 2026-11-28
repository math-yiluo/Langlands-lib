# Orthogonal projection extensions of Arthur truncation from the pointwise statements

**Sources.** J. Arthur, *An introduction to the trace formula* (2005), §13: (13.1),
Proposition 13.1 and the paragraph after its proof, printed pp. 68–69 (PDF pp. 80–81), in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`. That paragraph states that `Λ^T`
extends to an orthogonal projection, deduced from (ii) idempotence and (iii) the pairing. J. Arthur,
*A trace formula for reductive groups II* (1980), §1, Remark after Lemma 1.3, printed p. 92
(PDF p. 7), `arthur-1980-trace-formula-reductive-groups-II`, states the norm-one projection
on `L²(G(ℚ) \ G(𝔸)¹)`. E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series* (2011), §2, printed pp. 311–312 (PDF pp. 320–321),
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, uses the full-adelic operator and the
decomposition `G(𝔸) = G(𝔸)¹ × A_G`.

The module derives the conclusion of
[`TruncationOrthogonalProjectionStatement`](ArthurTruncationL2Statement.md) from the pointwise
statements of [ArthurTruncationStatement](ArthurTruncationStatement.md). It applies the general
criterion of [ArthurTruncationL2Criterion](ArthurTruncationL2Criterion.md) through the
transfer of [ArthurTruncationL2Quotient](ArthurTruncationL2Quotient.md).

## Homogeneity

`truncation_const_mul`: `Λ^T (c φ) = c Λ^T φ` for a constant `c`, with no convergence assumption.
Each constant term is an integral and each coset sum is an unconditional sum. Both commute
with multiplication by a constant, the sum even when it is not summable.

## The full quotient

`isOrthogonalL2Extension_truncation` fixes `K`, `D`, `hρ` and `Tp`. It assumes
three properties of `truncation` at `Tp`: it preserves measurable, locally bounded, left
`G(F)`-invariant functions; it is idempotent on them; and the pairing identity of
Proposition 13.1(c) holds against continuous left `G(F)`-invariant functions supported on the
`G(F)`-saturation of a compact set. The integrability of `φ₁ · (Λ^T φ₂)‾` is part of that
assumption. The conclusion is `IsOrthogonalL2Extension` for `rationalQuotientHaarMeasure F G`
and the full-quotient operator of the target. It is the transfer theorem with
`H = G(𝔸_F)` and `Γ = G(F)`.

## The norm-one quotient

The operator is `normOneTruncation`, the full formula applied to the zero extension
`normOneExtend` of a function on `G(𝔸_F)¹`. The same three hypotheses on the full truncation
at `Tp`, together with genericity of `ν`, give `IsOrthogonalL2Extension` for
`normOneRationalQuotientHaarMeasure F G` (`isOrthogonalL2Extension_normOneTruncation`). The
transfer theorem is applied with `H = G(𝔸_F)¹` and `Γ = G(F)`. Its three hypotheses are proved as follows.

- **Local boundedness** (`normOneTruncation_locallyBounded`). Let `φ` on `G(𝔸_F)¹` be
  measurable, bounded on compact sets and invariant under the principal norm-one subgroup.
  Then `normOneExtend φ` is measurable, since `G(𝔸_F)¹` is closed. It is bounded on compact
  sets, by the closed embedding of `G(𝔸_F)¹`, and left `G(F)`-invariant, since `G(F) ⊆ G(𝔸_F)¹`
  (`isLocallyBoundedInvariant_normOneExtend`). The norm-one truncation is the restriction of
  its full truncation.
- **Idempotence** (`normOneTruncation_idem`). By `normOneTruncation_restrict`, the norm-one
  truncation of the restriction of `Λ^T (normOneExtend φ)` is the restriction of
  `Λ^T Λ^T (normOneExtend φ) = Λ^T (normOneExtend φ)`.
- **Pairing** (`normOneTruncation_pairing_of_split`). Choose a split component `A ⟶ G`
  (`splitComponentStatement`). Its character restriction is injective
  (`characterRestrict_injective_of_centralSplitTorusCharacter` with the proved
  `centralSplitTorusCharacter`) and has finite-index range
  (`IsSplitComponent.finiteIndex_range_characterRestrict`). It factors through the maximal
  split torus (`IsCentralSplitTorus.exists_commFactor_of_isMaximalSplitTorus`). With split
  coordinates on `A`, `rationalQuotientDecomposition` identifies `A(ℝ)⁺ × G(F) \ G(𝔸_F)¹`
  with `G(F) \ G(𝔸_F)` and carries `normalizedPositiveHaarMeasure × normOneRationalQuotientHaarMeasure`
  to `rationalQuotientHaarMeasure` (`measurePreserving_rationalQuotientDecomposition`). Let
  `π` and `pf` be the norm-one projection and the positive factor. Take a nonnegative
  continuous compactly supported `χ` on the positive points with positive integral
  (`exists_bump_integral_pos`: an Urysohn function for a Haar measure). For a test function
  `φ₂` and an input `φ₁` on the norm-one group, put
  `Φ₁ = φ₁ ∘ π` and `Ψ = (χ ∘ pf) · (φ₂ ∘ π)`. They satisfy the hypotheses of the full pairing.
  At the class of `z_a n`, with `z_a` the positive point of `a` and `n` a norm-one representative,
  the following hold.
  - `Φ₁ = φ₁(n)` and `Ψ = χ(a) φ₂(n)`.
  - `Λ^T Φ₁ = Λ¹ φ₁ (n)`. Since `z_a` is central, `truncation_rightTranslate_splitCentral` turns
    evaluation at `n z_a` into truncation of the right translate by `z_a`, and `Φ₁` is invariant
    under it. Then `truncation_congr_on_normOne` compares with the zero extension of `φ₁`.
  - `Λ^T Ψ = χ(a) Λ¹ φ₂ (n)`. On `G(𝔸_F)¹` the right translate of `Ψ` by `z_a` is
    `χ(a) · normOneExtend φ₂`, and `truncation_const_mul` applies.

  The pushforward formula and `integral_prod_mul` then write both sides of the full
  pairing identity as `(∫ χ̄) · I`. Here `I` is the corresponding side of the norm-one identity,
  and `∫ χ̄ = ∫ χ ≠ 0`. Cancelling gives the identity. For integrability, the full
  integrability transported to the product shows that, for almost every `a`, the function
  `q ↦ χ(a)‾ · φ₁(q.out) · (Λ¹ φ₂ (q.out))‾` is integrable. The open set `{χ ≠ 0}` has positive
  Haar measure, so this holds at some `a` with `χ(a) ≠ 0`.

## The reduction

`truncationOrthogonalProjection_of_projection_of_selfAdjoint` proves
`TruncationProjectionStatement → TruncationSelfAdjointStatement →
TruncationOrthogonalProjectionStatement`. The compact subgroup `K` with its Iwasawa,
maximality and positive-torus compatibility clauses is taken from the projection statement.
For `D` and `hρ`, the threshold is the maximum of the idempotence threshold for `K` and the
pairing threshold of the self-adjointness statement for `K`. Above it, both extensions follow
from the two results above.

`truncationOrthogonalProjection_of_projection` proves
`TruncationProjectionStatement → TruncationOrthogonalProjectionStatement`. It applies the
reduction with the pairing statement discharged by `truncationSelfAdjoint`
([ArthurTruncationSelfAdjointProof](ArthurTruncationSelfAdjointProof.md)).
