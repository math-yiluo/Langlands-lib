# Unramified descent of smooth integral models (KP Fact 2.10.16)

This module states, as an unproved proposition, the unramified descent of
smooth integral group models with Galois-stable integral points. It also proves
the converse (necessity) direction from published API.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Section 2.10.
Definition 2.10.15 and Fact 2.10.16 with its proof are on printed pp. 126–127
(PDF pp. 157–158). The section's standing conventions are on printed p. 121
(PDF p. 152) and Remark 2.10.3 is on printed p. 122 (PDF p. 153). The registered
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The registered corrections `kaletha-prasad-2024-corrections` (1 November
2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, do not
amend Section 2.10: their entries pass from Section 2.6 directly to
Section 2.11. Their PDF p. 50 cites Fact 2.10.16 unchanged, in the added
Remark B.10.15.

## Source content

In Section 2.10, `k` is a field with a discrete valuation whose ring of
integers `o` is Henselian, `K` is a fixed maximal unramified extension of `k`,
`O` is the ring of integers of `K`, and `X` is an affine variety over `k` (a
reduced affine scheme of finite type). An integral model (Definition 2.10.1) is
an affine flat finite-type `o`-scheme with an isomorphism from its generic fibre
to `X`. For a model `X` over `o`, `X(O)` denotes its `O`-points, viewed inside
`X(K)`.

- **Definition 2.10.15.** An open bounded subset `U ⊂ X(K)` is *schematic* if
  there is a (necessarily unique) smooth integral model `X` of `X` over `o` with
  `X(O) = U`, and *connected* if moreover `X` has connected fibres. The text
  then notes that a schematic `U` is necessarily `Gal(K/k)`-invariant.
- **Fact 2.10.16.** Let `U ⊂ X(K)` be closed, open, bounded and
  `Gal(K/k)`-invariant. Suppose there is a smooth model `X'` of `X_K` over `O`
  with `X'(O) = U`. Then `X'` descends: there is a smooth model `X` of `X` over
  `o` and an isomorphism `X ×_o O → X'`. In particular, `U` is schematic. The
  proof cites unramified Galois descent over discrete valuation rings
  ([BLR90, §6.2, Ex. B]) and Corollary 2.10.11, and notes that
  `o[X] = O[X'] ∩ k[X]`.

## Lean declarations

All rings, fields and schemes lie in one arbitrary universe `u`.

`UnramifiedSmoothModelDescentStatement.{u}` is a `Prop`-valued definition; it
is not proved here. It quantifies over

- a nonarchimedean local field `F` (`[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]`);
- a group scheme `G : GroupScheme (Spec (CommRingCat.of F))`;
- a model
  `M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
  (baseChanged F (inertiaFixedField F) G)`.

Its two hypotheses are `M'.IsSmooth` and

```lean
∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
  ∀ g ∈ M'.integralPoints,
    rationalConjugate F (inertiaFixedField F) G σ g ∈ M'.integralPoints
```

Its conclusion is

```lean
∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
  Nonempty (M.baseChangeUnramified.Iso M' (CategoryTheory.Iso.refl _))
```

`galois_stable_of_iso_baseChangeUnramified` is a proved theorem: for a model
`M : IntegralModel 𝒪[F] F G`, a model `M'` as above and
`e : M.baseChangeUnramified.Iso M' (Iso.refl _)`, every
`rationalConjugate F (inertiaFixedField F) G σ` maps `M'.integralPoints` into
itself. It needs no smoothness hypothesis.

## Identification with the source's objects

- **`k` and `o`.** `k` is `F` and `o` is its valuation ring `𝒪[F]`. A
  nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`: locally
  compact, with a nontrivial valuation defining its topology) is complete for a
  discrete valuation with finite residue field, so `𝒪[F]` is Henselian. The Lean setting is therefore a special case of the source's
  setting. The statement adds no hypothesis beyond `IsNonarchimedeanLocalField`:
  no further completeness, perfectness, reductivity or connectedness premise.
- **`K`.** `K` is the existing `inertiaFixedField F`, the fixed field of the
  inertia subgroup of `Gal(SeparableClosure F / F)`. This is the maximal
  unramified extension of `F` inside the chosen separable closure; the Library
  abbreviation `Langlands.Geometry.Building.UnramifiedClosure F` names the same
  field as KP's `K`.
- **`O`.** `O` is the existing `fixedFieldIntegers F`, the valuation subring of
  `fixedFieldValuation F`. That valuation is the restriction to `K` of the
  spectral (unique) extension of the valuation of `F`. The Library theorem
  `fixedFieldIntegers_eq` identifies this ring with
  `extensionIntegers F (inertiaFixedField F)`. The coefficient map `o → O` used
  by `baseChangeUnramified` is the integer algebra induced by this valuation
  extension (`Valuation.HasExtension.instAlgebraInteger`), compatible with
  `F → K`.
- **`Gal(K/k)`.** This is `inertiaFixedField F ≃ₐ[F] inertiaFixedField F`, the
  group of `F`-algebra automorphisms of `K`. The Library instance
  `inertiaFixedField_isGalois` records that `K/F` is Galois.
- **`X(K)` and the Galois action.** `X(K)` is
  `rationalPoints (baseChanged F (inertiaFixedField F) G)`, the `K`-points of
  the actual base change `G_K`. The existing `baseChangeCoeffEquiv` identifies
  them with the `K`-valued points of `G`. `σ` acts by the existing
  `rationalConjugate F (inertiaFixedField F) G σ`, which is transported through
  `baseChangeCoeffEquiv` from the action of `σ` on the coefficients
  (`affinePointAut`), i.e. the action of KP.
- **Models and `X(O)`.** The models are the published `IntegralModel`s: affine,
  flat, locally of finite type (hence finite type, being affine) group schemes
  over the integral base, each with a specified group-scheme isomorphism from
  its actual generic fibre to the given generic group. `IsSmooth` is
  smoothness of the actual structure morphism. For a model over `O`, KP's
  `X'(O) ⊂ X(K)` is `M'.integralPoints`, the image of the integral sections in
  the generic rational points. For a model `M` over `o`, KP's `X(O)` is
  `M.baseChangeUnramified.integralPoints`. Here `M.baseChangeUnramified` is the
  published base change of `M` along `o → O` (KP's `X ×_o O`) with its generic
  identification transported from that of `M`.

## Comparison with Fact 2.10.16

- **The set `U`.** In the source, `U` is given together with `X'` satisfying
  `X'(O) = U`. In Lean, `U` is by definition `M'.integralPoints`, so the
  hypothesis `X'(O) = U` is built in.
- **Closed, open and bounded.** These hypotheses are automatic. Remark 2.10.3
  shows that the integral points of an integral model are a closed, open and
  bounded subset of its rational points: choose a closed immersion of the model
  into affine space over the integers; then the integral points are the
  rational points with integral coordinates. Section 2.10 allows any Henselian
  discrete valuation ring, and `O` is one (`K/k` is unramified and algebraic),
  so the remark applies to `X'` over `O`. Hence any `U` of the form `X'(O)`
  already has these properties, and the Lean statement does not repeat them.
- **Galois invariance.** The Lean hypothesis asks that every `σ` map
  `M'.integralPoints` into itself. Since `σ⁻¹` is also quantified, this is
  equivalent to `Gal(K/k)`-invariance of `U`.
- **Smoothness of `X'`.** This is `M'.IsSmooth`.
- **Conclusion.** The source's smooth model `X` of `X` over `o` is
  `M : IntegralModel 𝒪[F] F G` with `M.IsSmooth`. The source's isomorphism
  `X ×_o O → X'` is an isomorphism of models of `X_K`, compatible with the two
  generic identifications. In Lean it is an actual element of
  `M.baseChangeUnramified.Iso M' (Iso.refl _)`: a group-scheme isomorphism
  `M.baseChangeUnramified.group ≅ M'.group` over `Spec O` whose generic fibre,
  composed with the two specified generic isomorphisms, is the identity of
  `baseChanged F (inertiaFixedField F) G`. The conclusion is not weakened to an
  equality of point sets or to a predicate on a supplied model.
- **"In particular, `U` is schematic."** The published
  `Iso.integralPoints_eq` turns the conclusion into
  `M.baseChangeUnramified.integralPoints = M'.integralPoints`, which is the
  defining condition of Definition 2.10.15 (with `M` smooth).
- **Not stated here.** The uniqueness clause and the notion of a connected
  schematic subset in Definition 2.10.15 are not formalized. Neither is the
  coordinate-ring formula `o[X] = O[X'] ∩ k[X]` from the proof.

## Group-scheme setting

The source states Fact 2.10.16 for affine varieties. Here `G` is a group scheme
over `F`, `M'` is a group-scheme model of `G_K`, and the conclusion asks for a
group-scheme model `M` of `G` and a group-scheme isomorphism. This is the
setting of every intended consumer.

No affineness, finiteness or reducedness hypothesis is placed on `G`. None is
missing: the hypotheses make `G_K` isomorphic to the generic fibre of the smooth
affine finite-type `O`-group `M'.group`. Affineness, finite type and smoothness
descend along the faithfully flat extension `F → K`, so `G` is then a smooth
affine algebraic group over `F`, in particular an affine variety in KP's sense.
This remark explains the comparison; the Lean statement neither uses nor proves
it.

The group version follows from the variety version as in KP Remark 2.10.19.
Once a smooth `o`-model `X` with `X ×_o O ≅ X'` exists, its `O`-points form the
subgroup `U`. By Corollary 2.10.10 the generic multiplication, inverse and unit
then extend uniquely to `X`. The group axioms and the compatibility of the
isomorphism with the group laws hold generically and therefore integrally,
because the models are flat. This explanation is mathematical context for the
statement; it is not a Lean proof.

## Necessity lemma and its proof

The remark after Definition 2.10.15, that a schematic subset is
`Gal(K/k)`-invariant, is the converse of Fact 2.10.16. The proved theorem
`galois_stable_of_iso_baseChangeUnramified` is that converse in the present
setting. It is an internal consequence of published API, not a new source
claim.

The Lean proof has two steps. First, `e.integralPoints_eq` rewrites membership
in `M'.integralPoints`, both in the hypothesis on `g` and in the goal, as
membership in `M.baseChangeUnramified.integralPoints`. Second, the `mpr`
direction of the published
`mem_baseChangeUnramified_integralPoints_rationalConjugate_iff σ g` concludes.
That published lemma says that coefficient conjugation by `σ` preserves and
reflects the integral image of a base-changed model. Its input is that every
`σ` preserves `fixedFieldIntegers F`, because the spectral norm is invariant
under `F`-automorphisms.

## Status

This module publishes the interface, not a proof of
`UnramifiedSmoothModelDescentStatement`. A proof is the subject of a separate
successor task naming this exact declaration.

## Intended consumers

The construction of the integral models for KP Axioms 4.1.20 and 4.1.22
(task `cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) needs this statement. KP build
the parahoric and bounded-subgroup models over the maximal unramified extension
first (Sections 8.3 and 9.3), where the bounded subgroups are Galois-stable,
and descend them to `𝒪[F]` by this fact.
