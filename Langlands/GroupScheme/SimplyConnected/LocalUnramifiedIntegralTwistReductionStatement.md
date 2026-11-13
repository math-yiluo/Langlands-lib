# Integral twists give vanishing on finite unramified covers: the statement

Authors: Worker 5015.

This module states the proposition definition
`Langlands.GroupScheme.LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement.{u}` at
arbitrary universe `u`. It is the cohomological half of the proof of
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`: the building-theoretic twisting
statement implies vanishing on finite unramified covers. The module proves nothing.

## Exact statement

```
def LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement : Prop :=
  LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u} →
    LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}
```

Both sides are published proposition definitions in the namespace `Langlands.GroupScheme`, at the
same universe `u`. Their paired Markdown files state them in full. In short:

- The hypothesis `LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u}` (module
  `Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIntegralTwistStatement`) says the
  following. Let `F : Type u` be a nonarchimedean local field and `G` an affine group scheme
  over `Spec F` with `IsSimplyConnected G`. Then there is an integral model
  `M : IntegralModel 𝒪[F] F G`, smooth with connected special fibre, with this property. Let
  `L₀ = LocalGalois.Separable.inertiaFixedField F`. For every finite Galois `E/F` with an
  `F`-embedding into `L₀`, and every crossed homomorphism `c : Gal(E/F) → G(E)`, some `h ∈ G(L₀)`
  makes all twisted values `h⁻¹ * relativeExtend (c (σ|E)) * σ(h)`, `σ ∈ Gal(L₀/F)`, have
  integral coordinates for `M`.
- The conclusion `LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}` (module
  `Langlands.GroupScheme.SimplyConnected.LocalUnramifiedCocycleVanishingStatement`) says the
  following. For every nonarchimedean local field `F : Type u`, every group scheme `G` over
  `Spec F` with `[IsAffineHom G.X.hom]` and `IsSimplyConnected G`, every finite-dimensional
  intermediate field `E` of `SeparableClosure F / F` with `E ≤ L₀`, and every cocycle
  `ξ : Cocycle G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F E))))`, `ξ.IsTrivial`.

The implication adds no premises: no restriction on the characteristic of `F`, and no
splitness, isotropy or simplicity assumption on `G`. The extension `E` in the conclusion is not
assumed Galois.

## Provenance

Provenance: derived. This is an internal reduction statement, not a numbered result of the
source. The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`.

- Theorem 10.6.1 (printed pp. 397–398, PDF pp. 428–429) twists a cocycle of `Gal(K/k)` in
  `G(K)` by some `g ∈ G(K)`, `K` the maximal unramified extension, into a `Γ`-stable Iwahori
  subgroup. It then applies Lemma 8.1.4 (printed p. 285, PDF p. 316) to the Iwahori group
  scheme, which is smooth with connected fibres.
- Theorem 10.6.4 (printed p. 399, PDF p. 430) specializes this to simply connected groups, whose
  Iwahori subgroups are self-normalizing. This gives `H¹(Gal(K/k), G(K)) = 1`.

The hypothesis of the implication packages the building step of these proofs. The implication
itself is the remaining cohomological part: Lemma 8.1.4 at a finite unramified level and the
passage from cocycles on finite covers to Galois cocycles. It splits the proof of
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement` into this implication and a proof of
the twisting statement.
