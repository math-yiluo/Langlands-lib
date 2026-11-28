# Truncated Eisenstein families: reduction to the asymptotic and square-integrability parts

Module `Langlands.Global.AdelicTruncatedEisensteinUniformAsymptoticsReduction`
proves two theorems:

- `exists_isOrthogonalL2Extension_of_isIwasawaCompact`: Arthur's orthogonal
  projection property of the truncation operators for every compact `K` with
  `P_0(𝔸)K = G(𝔸)`;
- `localTruncatedEisensteinFamilyUniformInnerProduct_of_asymptotics`:
  [`LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement`](AdelicTruncatedEisensteinFamilyUniformAsymptoticsStatement.md)
  implies
  [`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`](AdelicTruncatedEisensteinUniformAsymptoticsStatement.md).

Neither proposition is proved here.

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`: §13,
  Proposition 13.1 (b), (c), p.68 (PDF p.80), and the paragraph after its
  proof, p.69 (PDF p.81). Arthur works over `ℚ`. Proposition 13.1 states the
  pointwise identities `Λ^T ∘ Λ^T = Λ^T` and
  `(Λ^T φ₁, φ₂) = (φ₁, Λ^T φ₂)` for locally bounded measurable `φ₁` and
  compactly supported continuous `φ₂` on the norm-one quotient
  `G(ℚ) \ G(𝔸)¹`. The paragraph after the proof says that `Λ^T` "extends to
  an orthogonal projection from the space `L²(G(ℚ) \ G(𝔸))` to itself"; the
  printed quotient there is the full one.
- J. Arthur, *A trace formula for reductive groups II: applications of a
  truncation operator*, Compositio Math. 40 (1980), registered as
  `arthur-1980-trace-formula-reductive-groups-II`: §1, the Remark after
  Lemma 1.3, p.92 (PDF p.7): "`Λ^T` extends to an orthogonal projection on
  `L²(G(ℚ) \ G(𝔸)¹)`", the norm-one version.
- For the two propositions, the sources listed in their Markdown (Lapid 2011,
  Proposition 1; Arthur 1980, Lemma 1.4; Arthur 2005, §4 and §13; Arthur 1981,
  §1).

The Lean theorem `exists_isOrthogonalL2Extension_of_isIwasawaCompact` is
derived. It is stated over an arbitrary number field `F`, for both the
norm-one quotient and the full quotient, and for every compact `K` with
`P_0(𝔸)K = G(𝔸)`. Its proof uses only the Library's proved pointwise
identities (idempotence and the pairing identity, for every such `K`), not
the printed projection sentences.

## The projection property for every compact Iwasawa subgroup

`exists_isOrthogonalL2Extension_of_isIwasawaCompact` takes `hG`, `hi`, `hν`,
reflection data `D`, a subgroup `K` of `G(𝔸)` with
`hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K` and the bijectivity
`hρ`. It concludes that there is `C` such that for every `Tp` with
`C < eval T β Tp` for all simple relative roots `β`:

- `IsOrthogonalL2Extension (normOneRationalQuotientHaarMeasure F G)` holds for
  the operator `f ↦ (q ↦ normOneTruncation hG hi D hK hρ Tp (f ∘ mk) q.out)`
  on functions on `G(F) \ G(𝔸)¹`;
- `IsOrthogonalL2Extension (rationalQuotientHaarMeasure F G)` holds for
  `f ↦ (q ↦ truncation hG hi D hK hρ Tp (f ∘ mk) q.out)` on functions on
  `G(F) \ G(𝔸)`.

This is exactly the first part of the conclusion of
`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`, with `hK` in
the place of `hK₀`, for an arbitrary compact `K` with `P_0(𝔸)K = G(𝔸)`.

**Proof.** Two Library results hold for every such `K` and all reflection
data:

- `iwasawaTruncationIdempotent : IwasawaTruncationIdempotentStatement` (module
  `Langlands.Global.ArthurTruncationIdempotenceProof`) gives `C₁` such that
  for `Tp` beyond `C₁` the truncation is idempotent on measurable, locally
  bounded, left `G(F)`-invariant functions (`IsTruncationIdempotent`);
- `truncationSelfAdjoint : TruncationSelfAdjointStatement` (module
  `Langlands.Global.ArthurTruncationSelfAdjointProof`) gives `C₂` such that
  for `Tp` beyond `C₂` the truncation preserves these functions and satisfies
  the pairing identity of Proposition 13.1(c) against continuous left
  `G(F)`-invariant functions supported on the `G(F)`-saturation of a compact
  set, with both products integrable.

With `C = max C₁ C₂` both apply. The preservation, the idempotence and the
pairing identity (together with the integrability of
`y ↦ φ₁(y.out) · (Λ^T φ₂(y.out))‾`) are the three hypotheses of
`isOrthogonalL2Extension_truncation` and of
`isOrthogonalL2Extension_normOneTruncation` (module
[`Langlands.Global.ArthurTruncationL2Reduction`](ArthurTruncationL2Reduction.md)),
which give the two conclusions.

## The reduction

`localTruncatedEisensteinFamilyUniformInnerProduct_of_asymptotics` assumes
`LocalTruncatedEisensteinFamilyUniformAsymptoticsStatement` and proves
`LocalTruncatedEisensteinFamilyUniformInnerProductStatement`. For given `F`,
`G`, `T`, `i`, `ν`, `hG`, `hi`, `hν` it takes the subgroup `K` of the
hypothesis with its four properties (maximal compact, the two Iwasawa
conditions, positive-torus compatibility), which are the four properties the
conclusion asks for. For `D`, `hρ`, `hK₀`, `hK` it supplies the first part
from `exists_isOrthogonalL2Extension_of_isIwasawaCompact` applied with
`hK₀`, and the second and third parts from the hypothesis, whose conclusion
after `∀ D hρ hK₀ hK` is literally their conjunction.
