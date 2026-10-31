# Proof of the entire Whittaker deformation for two lower-induced blocks

Module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof`.

Authors: Worker 831 and Worker 814.

The theorem `Langlands.RankinSelberg.twoBlockWhittakerDeformation.{uF,uW}` proves
exactly the published proposition
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement.{uF,uW}`, the
inverse-character form of the lemma of JPSS 1983, Section (4.5). Its scope is
the scope of the statement. The field universe `uF` and the block-carrier
universe `uW` are independent. The theorem covers every prime `p`, every
canonical `p`-adic field, every unitary additive character `ψ`, and the two
positive block ranks `m 0 + 1` and `m 1 + 1` with
`h : ∑ i, (m i + 1) = t + 1`. The blocks `σ` are arbitrary representations on
complex modules, possibly reducible, of full standard Whittaker type. The
deformed representation is the published
`ρ_u = twoBlockDeformedInduced F m h σ u`: canonical normalized lower parabolic
induction of the block tensor, with only the first block twisted by `|det|^u`.

For every nonzero inverse-character Whittaker functional `ℓ₀` of `ρ_0` and
every vector `v₀`, the theorem gives a family `W_u(g)` with the four clauses
of the statement:

1. `W_0(g) = ℓ₀(ρ_0(g) v₀)`.
2. For each `u`, `W_u` is the coefficient of a nonzero inverse-character
   functional of `ρ_u` at a vector of the actual induced carrier.
3. One compact open subgroup `K` satisfies `W_u(gk) = W_u(g)` for every `u`.
4. `u ↦ W_u(g)` is analytic at every complex `u`, for every `g`.

The theorem has no further hypothesis. In particular, it assumes no
irreducibility, induced Whittaker type, stabilization, nonvanishing, analytic
family or uniform subgroup.

## Implemented proof

The proof is one application:

```
TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of_normalizedProduct
  normalizedProductWhittakerType.{uF, uW}
```

The first theorem, in `TwoBlockDeformationAssembly`, proves the target from
`H : NormalizedProductWhittakerTypeStatement.{uF,uW}`. The second,
`Langlands.RankinSelberg.normalizedProductWhittakerType` in
`NormalizedProductWhittakerTypeProof`, proves `H` with the same universes. It
states that canonical normalized upper block induction of full-type blocks
has full Whittaker type. Both theorems are published closed results, and the
proof adds no new hypothesis.

The route through the helper modules is as follows. Each module's Markdown
gives its proof in detail.

- `TwoBlockDeformationUniqueness`. From `H`, every `ρ_u` has full
  inverse-standard Whittaker type, so its inverse-character functionals form
  a line (`functional_eq_smul`). This uses three conversions. The twist by
  `|det|^u` preserves full type (`isOfWhittakerType_twist_iff`). Lower
  normalized induction is equivalent to upper normalized induction of the
  reversed blocks (`glOppositeProductReversal`). Full standard type and full
  inverse-standard type agree (`isOfWhittakerType_standard_iff_inverse`). The
  same module gives one nonzero inverse-character functional `ell i` on each
  block. This functional serves every `u`, because `|det|^u` is trivial on
  upper unipotent matrices.
- `TwoBlockDeformationCell` and `TwoBlockDeformationNonvanishing`. Let `V'_u`
  be the sections whose restriction to the upper radical has compact support.
  On `V'_u`, the JPSS integral (4.6.2) at the identity converges absolutely
  and is equivariant for the inverse standard character. Some section in
  `V'_u` has a nonzero integral.
- `Jacquet.CharacterAveraging`, used in `TwoBlockDeformationAssembly`
  (`exists_jacquetFunctional`). Character averaging over compact open
  subgroups of the upper unipotent group extends this integral to an
  inverse-character functional `J_u` on all of `ρ_u`, with `J_u ≠ 0`.
  Uniqueness on `ρ_u` then gives `relations ⊔ V'_u = ⊤`.
- `TwoBlockDeformationFlat`. The flat sections `f_u` with `f_0 = v₀` are all
  fixed by one compact open subgroup (`exists_uniform_stabilizer`).
- `TwoBlockDeformationAnalysis` and `TwoBlockDeformationAnalytic`
  (`flatCoefficientDifferentiable`). For every `g`, `u ↦ J_u(ρ_u(g) f_u)` is
  differentiable on all of `ℂ`. On a sufficiently large averaging level, the
  averaged value is an integral of exponential sums in `u`. A countable-union
  argument shows that one level serves every `u`.
- `TwoBlockDeformationAssembly` (`exists_deformation_of_functionals`).
  Uniqueness at `u = 0` gives `ℓ₀ = c • J_0` with `c ≠ 0`. Set
  `W_u(g) = c · J_u(ρ_u(g) f_u)`. The four clauses then follow from
  `f_0 = v₀`, the nonzero functional `c • J_u`, the uniform stabilizer of the
  `f_u`, and differentiability on `ℂ`, which implies analyticity.

No stable Jacquet integration (`HasStableIntegral`) is used. Coefficient
membership at every `u` comes from the actual functional `c • J_u` on the
actual carrier of `ρ_u`, not from unipotent equivariance alone. The uniform
subgroup comes from the flat sections, not from smoothness at each separate
`u`.

## Excluded inputs

The proof uses no gamma or L multiplicativity result, no finite-block parent
and no descendant of this deformation. The import closure consists of the
target statement, the deformation helper modules above, the published Library
modules they import, and `NormalizedProductWhittakerTypeProof`. The imported
modules include `WhittakerGammaAdapters`, but only for its character-change
adapter `isOfWhittakerType_standard_iff_inverse`. That module proves no
multiplicativity. The last
module combines the published raw upper induced finite-type and Whittaker-type
theorems, the normalized admissibility and tensor admissibility results, the
half-modulus absorption equivalence and the functional-line adapter. It uses
no Rankin–Selberg multiplicativity consumer.

## Provenance

The target is the lemma of JPSS 1983 (source ID `jpss-1983-rankin-selberg`),
Section (4.5), printed pages 408–409, in the inverse-character form applied on
page 409. The statement's Markdown records the conventions: lower parabolic
`Q̄`, inverse character, and twist `|det|^u` on the first block. JPSS obtain the
functional on `σ_u` from the Jacquet integral (4.6.2), printed page 410, with
the coefficient-membership conclusion on page 411, and cite Shahidi (1978) and Casselman–Shalika (1980, Section 2) for its
continuation. The Lean route is internal and does not formalize JPSS's proof
step by step. It replaces stable integration by the character-averaged
extension `J_u` of the compactly supported integral. The holomorphy step
follows the countability argument of Casselman–Shalika, Section 2 (source ID
`casselman-shalika-1980-whittaker`), as described in
`TwoBlockDeformationAnalytic.md`. The uniqueness input is the Library's
upper-block form of the heredity assertion of JPSS Section (2.3), proved by
`normalizedProductWhittakerType`.
