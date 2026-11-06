# Properness over a normal local domain from its two fibres

Module `Langlands.AlgebraicGeometry.ProperOfFibres.ValuationCore`, namespace
`Langlands.AlgebraicGeometry.ProperOfFibres`. This module removes the noetherian hypothesis
from `isProper_pullback_snd_of_mono` (module `NoetherianCore`) by noetherian approximation
(module `Approximation`). It is the local step of the properness criterion used for
relative parabolic quotients (compare Conrad, *Reductive group schemes* (2014), proof of
Theorem 2.3.6(2), pp. 73–74, which reduces properness of `G/H` to a noetherian local base).
The statements are internal helpers; the proofs below are the implemented Lean proofs.

## Helper lemmas

- `surjective_flat_quasiCompact_SpecMap`: for a ring map `φ : K →+* L` between fields,
  `Spec.map φ` is surjective, flat and quasi-compact. Proof: `L` is a faithfully flat
  `K`-module (every module over a field is free), so `flat_and_surjective_SpecMap_iff`
  gives flatness and surjectivity; quasi-compactness holds for any morphism of affine
  schemes.
- `exists_isPullback_of_fac`: given a pullback square `X → X₁`, `X → Y`, `f : X₁ ⟶ B`,
  `ι : Y ⟶ B` and a factorization `ι = ι' ≫ κ`, the scheme `X` is also the pullback of
  `pullback.snd f κ` along `ι'`. Proof: `isPullback_lift_of_fac` from `Approximation`.
- `exists_isPullback_fibre`: let `X ⟶ Spec V` be the base change of `X₀ ⟶ Spec N` along
  `α : N →+* V`, and let `β : N →+* B`, `γ : B →+* F`, `δ : V →+* E` and `ε : F →+* E` be
  ring maps with `δ ∘ α = ε ∘ γ ∘ β`. Then the base change of `X` along `δ` is the base
  change of `(X₀ ×_N B) ×_B F` along `ε`. Proof: paste the pullback square of `X` along
  `δ` onto the given square, then apply `exists_isPullback_of_fac` twice (factor
  `Spec.map ε ≫ Spec.map γ ≫ Spec.map β` first through `Spec.map β`, then through
  `Spec.map γ`).
- `lift_injective_isLocalHom`: let `φ : N →+* V` be an injective ring map from a domain to
  a local ring, `p` the preimage of the maximal ideal of `V`, and `B` a localization of `N`
  at `p`. The lift `B →+* V` of `φ` is injective and a local homomorphism. Proof:
  injectivity by `IsLocalization.lift_injective_iff`, since `N ⟶ B` is injective (`p`
  avoids zero) and `φ` is injective. Locality: write `b = n / s` with `s ∉ p`; if the image
  of `b` is a unit then so is `φ n`, hence `n ∉ p`, so `n / s · s = n` is a unit of `B` and
  therefore `b` is a unit.

## Main theorem `isProper_of_isLocalRing`

Hypotheses: `V` is an integrally closed local domain with fraction field `K`;
`f : X ⟶ Spec V` is smooth and quasi-compact; `g : Y ⟶ Spec V` is proper and locally of
finite presentation; `j : X ⟶ Y` is a monomorphism with `j ≫ g = f`; the generic fibre
`pullback.snd f (Spec.map (algebraMap V K))` is proper and geometrically connected; the
closed fibre `pullback.snd f (Spec.map (residue V))` is proper and its source is nonempty.
Conclusion: `f` is proper.

Proof as implemented:

1. `exists_normal_model` gives a finitely generated, integrally closed `ℤ`-subalgebra
   `N ⊆ V` and a model `M` of `(f, g, j)` over `N` (schemes `X₀`, `Y₀` over `Spec N` whose
   base changes to `V` are `X`, `Y`, with `j₀ : X₀ ⟶ Y₀` a monomorphism lifting `j`),
   such that `X₀ ⟶ Spec N` is smooth and `Y₀ ⟶ Spec N` is proper.
2. Let `φ : N → V` be the inclusion, `p` the preimage of the maximal ideal of `V`, and `B`
   a localization of `N` at `p` (obtained as an abstract type carrying the instances of
   `Localization.AtPrime p`; this avoids an instance-search failure for
   `IsFractionRing (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))`). `B`
   is a local domain. The lift `ψ : B →+* V` is injective and local
   (`lift_injective_isLocalHom`), with `ψ ∘ (N → B) = φ`.
3. Generic fibre: the injective composite `B → V → K` induces `ε : Frac B →+* K`
   (`IsFractionRing.lift`). By `exists_isPullback_fibre`, the generic fibre of `f` is the
   base change along `Spec ε` of the generic fibre of `X₀ ×_N B ⟶ Spec B`. Since `Spec ε` is
   surjective, flat and quasi-compact, properness descends
   (`MorphismProperty.of_isPullback_of_descendsAlong` with the Library instance from
   `Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent`), and geometric connectedness
   descends by `geometricallyConnected_of_surjective_isPullback`.
4. Closed fibre: `ψ` is local, so it induces `ρ : κ(B) →+* κ(V)`
   (`IsLocalRing.ResidueField.map`) with `ρ ∘ residue B = residue V ∘ ψ`. The same
   argument shows the closed fibre of `X₀ ×_N B ⟶ Spec B` is proper; it is nonempty because
   the nonempty closed fibre of `f` maps to it.
5. `isProper_pullback_snd_of_mono` (module `NoetherianCore`) applied to the model, with
   fraction field `Frac B`, shows that `X₀ ×_N B ⟶ Spec B` is proper.
6. `X` is the base change of `X₀ ×_N B ⟶ Spec B` along `Spec ψ`
   (`exists_isPullback_of_fac` with `ψ ∘ (N → B) = φ`), so `f` is proper by stability of
   properness under base change (`MorphismProperty.of_isPullback`).
