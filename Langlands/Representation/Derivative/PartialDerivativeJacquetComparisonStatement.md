# Positive two-block Jacquet-to-derivative comparison

Author: Worker 723.

This module states the positive-block clause of Zelevinsky (1980),
Proposition 3.7(b): the ordinary `m`-th derivative of a representation of
`GL_(k+m)` is naturally isomorphic to the partial derivative of its normalized
Jacquet module for the standard parabolic of shape `(k,m)`. It has one helper
functor, `Langlands.Derivative.positiveTwoBlockNormalizedJacquet`, and one
Prop-valued definition, the principal proposition
`Langlands.Derivative.PartialDerivativeJacquetComparisonStatement.{uF, uV} F T`.
It proves nothing. The comparison remains a proof obligation.

## The helper functor

`positiveTwoBlockNormalizedJacquet.{uF, uV} T k m hk hm` takes implicit
`{p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}` and explicit
`(T : F.TopologicalData) (k m : ℕ) (hk : 0 < k) (hm : 0 < m)`. After
`letI := T.topology` it is a functor

```
SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + m) F.Carrier) ⥤
  SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier)
```

defined as the composite

```
T.normalizedJacquetFunctor (Shahidi.twoBlocks k m hk hm) ⋙
  Mirabolic.continuousPullbackFunctor
    (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.toMonoidHom
    (Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm.continuous
```

All three ingredients are published and used unchanged:

- `Shahidi.twoBlocks k m hk hm : BlockShape (k + m)` is the ordered standard
  shape with first block `GL_k` (indices `i.castAdd m`) and second block
  `GL_m` (indices `i.natAdd k`). `BlockShape` requires positive blocks, which
  is why `hk` and `hm` are needed.
- `T.normalizedJacquetFunctor B` (`Langlands.Representation.Jacquet.Parabolic`)
  sends a smooth representation `ρ` of `GL_(k+m)` to its actual coinvariant
  quotient by the unipotent radical of the parabolic `P = MN`. The Levi
  `B.Levi F.Carrier` acts by
  `m · [v] = δ_P(m)^(-1/2) · [ρ(leviEmbedding m) v]` (`normalizedJacquet_mk`),
  with `δ_P = T.leviModulus B`. For this shape, `T.leviModulus_twoBlocks`
  gives `δ_P(g) = |det g 0|^m / |det g 1|^k`. The first-factor determinant
  twist is kept. Morphisms go to the induced quotient maps.
- `Mirabolic.continuousPullbackFunctor φ hφ`
  (`Langlands.Representation.Derivative.MirabolicMinus`) restricts along a
  continuous homomorphism `φ`, with unchanged carriers and linear maps. Here
  `φ` is the inverse of the continuous group equivalence
  `twoBlockLeviContinuousEquiv : (twoBlocks k m hk hm).Levi F.Carrier ≃ₜ* GL_k × GL_m`,
  `g ↦ (g 0, g 1)`. Pullback is contravariant in the group, so the inverse
  `GL_k × GL_m → Levi` is what turns a Levi representation into one of the
  product. A pair `(a, b)` acts on the normalized Jacquet module as the Levi
  element with blocks `a` and `b` does: by `δ_P^(-1/2)` of that element times
  the induced action of `diag(a, b)` in `GL_(k+m)`.

The carriers stay those of the normalized Jacquet module, in `Type uV`. No
new representation, quotient or action is constructed.

## The principal proposition

The parameters are `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`, with level parameters in the order `uF, uV`. The
carrier universe `uV` is independent of `uF`. The Lean body is

```
letI := T.topology
∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) (hk : 0 < k)
  (hm : 0 < m),
  Nonempty
    (generalLinearDerivative.{uF, uV} T ψ (k + m) m (Nat.le_add_left m k) ⋙
        generalLinearRankCast.{uF, uV} T (Nat.add_sub_cancel k m) ≅
      positiveTwoBlockNormalizedJacquet.{uF, uV} T k m hk hm ⋙
        partialDerivative.{uF, uV} T ψ k m)
```

Both sides are functors from
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + m) F.Carrier)` to
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)`, and `≅` is an
isomorphism in the functor category. Such an isomorphism consists of
isomorphisms of smooth representations, that is, invertible equivariant
linear maps, one for each object, natural with respect to every morphism.
The morphisms of both sides are the actual mapped intertwiners of the
published functors. The proposition is not about isomorphism classes,
Grothendieck groups or a replacement functor. It assumes no comparison.

There is no hypothesis on representations: no finite length, admissibility,
irreducibility, genericity or dimension condition. `F` is an arbitrary p-adic
field with the supplied `T`; no canonical field or topology is substituted.
`letI := T.topology` selects, through instance inference, the matrix-unit
topology on every `GL` group, the product topology on `GL_k × GL_m` and the
product topology on the Levi. These are by definition the topologies
`T.generalLinearTopology` and `T.leviTopology` used by the published functors.
`UnitaryAdditiveCharacter` bundles continuity for `T.topology` and
nontriviality. The same `ψ` is used in both derivatives.

### The left-hand side

`generalLinearDerivative T ψ (k + m) m (Nat.le_add_left m k)` is the published
ordinary `m`-th derivative of `Langlands.Representation.Derivative.Iteration`,
with target `GL_((k + m) - m)`. Since `m > 0`, write `m = j + 1`. Then it is
`generalLinearRankCast T (rank_eq_of_succ_le _) ⋙ generalLinearDerivativePositive T ψ ((k + m) - m) j`
(`generalLinearDerivative_succ`), and the positive derivative is
`generalLinearRestriction T (n + j) ⋙ phiMinusIterate T ψ n j ⋙ Mirabolic.psiMinus T n`
with `n = (k + m) - m` (`generalLinearDerivativePositive_eq_comp`). This is
restriction to the mirabolic subgroup, `j = m - 1` steps of the
determinant-normalized `Φ⁻`, then the determinant-normalized `Ψ⁻`.

`generalLinearRankCast T (Nat.add_sub_cancel k m)` then transports from
`GL_((k + m) - m)` to `GL_k`. It is `Eq.rec` of the identity functor along an
equality of ranks, so it changes no carrier or map
(`generalLinearRankCast_map_heq`).

### The right-hand side

`positiveTwoBlockNormalizedJacquet T k m hk hm`, described above, followed by
`partialDerivative T ψ k m` of `Langlands.Representation.Derivative.Partial`.
The partial derivative takes the coinvariants of a representation of
`GL_k × GL_m` for the subgroup `{1} × U_m` of upper unipotent matrices in the
second factor, twisted by `Whittaker.entrywiseCharacter ψ m`, which is
`u ↦ ψ(∑ u_(i,i+1))` on adjacent upper entries. `GL_k` acts through `g ↦ (g, 1)`.
As recorded in the published `Partial` pair, the conjugation modulus of this
localization is one, so no normalizing twist enters.

## Source and provenance

Page numbers are printed numbers, with one-based PDF pages in parentheses.

Zelevinsky, *Induced representations of reductive p-adic groups II.
Irreducible representations of GL(n)* (1980), `zelevinsky-1980-induced-ii`,
SHA256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
§3.7, p.182 (PDF 19). For `k, m ≥ 0` the source defines the partial
derivative `∂ = r_(U,θ) : Alg(G_k × G_m) → Alg G_k`, where `U` is the upper
unipotent subgroup of `{e} × G_m` and
`θ(u) = ψ(∑_(1 ≤ i ≤ m-1) u_(k+i,k+i+1))`. Proposition 3.7(b) says that, for
`n = k + m`, the `m`-th derivative `Alg G_n → Alg G_k` is isomorphic to the
composite of `∂` with the normalized Jacquet functor `r_((k,m),(n))`. The
source says this "follows immediately from the definition of m-th derivative"
and Bernstein–Zelevinsky (1977) 1.9(c),(g).

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`:

- §1.8(b), pp.444–445 (PDF 5–6): the localization `r_(U,θ)`, the coinvariant
  quotient by the span of `π(u)ξ − θ(u)ξ`, with the descended action
  multiplied by `mod_U^(-1/2)`, the inverse half modulus.
- Proposition 1.9(c), p.445 (PDF 6): transitivity of localization,
  `r_(V,θ') ∘ r_(U,θ) = r_(U°,θ°)` with `θ°(uv) = θ(u)θ'(v)`. Proposition
  1.9(g), same page: compatibility with inductive limits and tensoring.
- §3.5, p.452 (PDF 13): `τ^(k) = Ψ⁻ ∘ (Φ⁻)^(k-1)(τ)` for `τ ∈ Alg P_n`.
- §4.3, p.454 (PDF 15): `π^(0) = π` and `π^(k) = (π|_(P_n))^(k)` for
  `π ∈ Alg G_n`.

Both hashes were verified against the registered files. No errata or
source-specific notes file for either source was found in the central
library, the literature index or the public notes. This is a bounded check,
not a claim that no errata exist.

### Internal formalization

The statement formalizes the source assertion for positive `k` and `m`. The
following parts are internal packaging, not source text:

- the explicit `Nonempty` natural isomorphism of functors, which makes the
  source's "isomorphic" functorial and equivariant;
- the rank cast `Nat.add_sub_cancel k m`, needed because the published
  derivative has target rank `(k + m) - m`;
- the transport of the Levi action to `GL_k × GL_m` along the inverse of
  `twoBlockLeviContinuousEquiv`; the source identifies the Levi with
  `G_k × G_m` silently;
- quantifying `ψ`, `k`, `m`, `hk` and `hm` in one proposition.

### Normalizations

The source normalizes the Jacquet functor and every localization with
`mod^(-1/2)`. The Library uses these choices:

- the normalized Jacquet functor uses `δ_P^(-1/2)` with
  `δ_P = T.leviModulus (twoBlocks k m hk hm)`, which is
  `|det g 0|^m / |det g 1|^k` (`T.leviModulus_twoBlocks`);
- the partial derivative has trivial normalization, as its modulus is one;
- the published `Ψ⁻` and `Φ⁻` use the fixed twists `|det|^(-1/2)` where the
  source writes `mod_V^(-1/2)`, as recorded in the published `MirabolicMinus`
  and `Iteration` pairs.

As an informal consistency check, not a proof: an element `g` of `GL_k`
acts on the left side through `m − 1` normalized `Φ⁻` steps and one
normalized `Ψ⁻`, contributing the scalar `|det g|^(-m/2)`. On the right side
`(g, 1)` contributes `δ_P^(-1/2) = |det g|^(-m/2)` and the partial derivative
contributes nothing. Likewise, the `Φ⁻` steps use the character `ψ` of the
entry just above the diagonal in the last column. After `m − 1` steps and the
trivial-character `Ψ⁻` this gives `ψ(∑ u_(k+i,k+i+1))` on the unipotent upper
`m × m` block, the same as `entrywiseCharacter ψ m` on the second factor.
The proposition therefore uses the same character and compatible
normalizations on both sides.

## Scope and boundary obligations

This is the positive-block clause only. The source allows all `k, m ≥ 0`; the
published `BlockShape` requires positive blocks, so `(0, m)` and `(k, 0)` are
not two-block shapes and are not covered:

- `k = 0`: the single-block top-localization comparison belongs to the
  separate task owned by Worker 288.
- `m = 0`: the zeroth derivative is the identity functor
  (`generalLinearDerivative_zero`), and the partial derivative of second rank
  zero is naturally isomorphic to first-factor restriction
  (`partialDerivativeZeroIso`), keeping the whole carrier. That boundary is
  handled by identity and partial-zero adapters elsewhere.

Ze80 3.7(a), the exterior-tensor comparison, and the product or Leibniz
filtration are separate tasks and are not stated here.

## Remaining proof obligation

A proof of `PartialDerivativeJacquetComparisonStatement F T` must construct,
for every `ψ` and all positive `k` and `m`, an actual natural isomorphism
between the two functors. The source route needs transitivity of normalized
character localization (BZ77 1.9(c)), its equivariance and functorial
naturality, together with the modulus bookkeeping above. Untwisted quotient
identities alone do not give the character or normalization comparison. This
module provides none of that and does not prove itself. The published
derivative and Jacquet definitions are constructions, not comparison proofs.

## Imports and independence

The module imports `Langlands.Representation.Derivative.Iteration`,
`Langlands.Representation.Derivative.Partial`,
`Langlands.Representation.Jacquet.Parabolic` and
`Langlands.Representation.Shahidi.TwoBlocks`. Not counting this module, its
`Langlands` import closure has 64 modules. Besides these four, they are
`MirabolicMinus`, `MirabolicCharacter`, and modules on groups, block
parabolics and moduli, local fields, smooth representations, twists,
coinvariants and localization, normalized Jacquet functors, matrix
coefficients and Whittaker characters. All 128 Lean and Markdown files of the
closure are identical in Library commits
`7e64f8e360c8778e04e5da7f9cd382cda7c837f6` and
`f60a6c408d4d2ab4d0217f8be1dd8745e54a207c`. `Representation/Dual/Definitions`
in the closure only builds algebraic dual maps; it is not a duality theorem.
The closure contains no classification, segment, multisegment,
square-integrable, tempered, socle, irreducibility, plus-functor, adjunction,
pairing or filtration module.

Neither the module nor its closure uses `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
`UnlinkedSegmentSocleProductIrreducible`,
`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, or any result of the excluded exhaustion,
existence, coverage, conversion, uniqueness, socle-commutation, gluing or
segment-classification tasks.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
