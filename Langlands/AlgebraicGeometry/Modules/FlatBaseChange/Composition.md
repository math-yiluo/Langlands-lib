# Invertibility of base change transformations across composed squares

Helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.FlatHigherDirectImageBaseChangeStatement`
(see `FlatHigherDirectImageBaseChangeProof.md`). Namespace
`Langlands.AlgebraicGeometry.Modules.FlatBaseChange`.

## Setting

Two commutative squares are pasted horizontally:
`w : p ≫ f = f' ≫ b` with `f : X ⟶ S`, `b : S' ⟶ S`, `f' : X' ⟶ S'`,
`p : X' ⟶ X`, and `v : q ≫ f' = f'' ≫ c` with `c : S'' ⟶ S'`,
`f'' : X'' ⟶ S''`, `q : X'' ⟶ X'`. The composite square is
`(q ≫ p) ≫ f = f'' ≫ (c ≫ b)`, proved by the Library's
`compositeBaseChangeSquare b c f f' f'' p q w v`. Pullbacks along `b`, `c`,
`c ≫ b`, `p`, `q` and `q ≫ p` preserve finite limits (instance arguments).

## Declarations

- `pushforwardBaseChange_composite_eq`: the degree-zero base change map of the
  composite square equals
  `(pullbackComp c b).inv ≫ c^*(pushforwardBaseChange b f f' p w N) ≫
   pushforwardBaseChange c f' f'' q v (p^* N) ≫ f''_*((pullbackComp q p).hom)`.
  It is the Library's `pushforwardBaseChange_composition`, solved for the
  composite map with `Iso.eq_inv_comp`.
- `isIso_pullback_map_higherDirectImageBaseChange_iff b c f f' f'' p q w v M n hB`:
  if the component at `p^* M` of
  `higherDirectImageBaseChangeNatTrans c f' f'' q v n` is an isomorphism (`hB`),
  then `c^*` of the component at `M` of
  `higherDirectImageBaseChangeNatTrans b f f' p w n` is an isomorphism if and
  only if the component at `M` of the composite square's transformation is.

## Proof of the criterion

All three transformations are computed with injective resolutions through
`isIso_map_baseChangeNatTrans_app_iff` (module `Cohomology.ExactBaseChange.ResolutionMap`).

1. Let `I₀`, `I₁`, `I₂` be Mathlib's injective resolutions of `M`, `p^* M`
   and `q^* p^* M`. The Library's `AcyclicResolution.lift` gives cochain maps
   `ψ₁ : p^* I₀ ⟶ I₁` and `ψ₂ : q^* I₁ ⟶ I₂` over the identities, with the
   augmentation identities from `comp_lift`.
2. For the composite square, `ε'' := (single₀).map ((pullbackComp q p).inv) ≫ I₂.ι`
   is a right resolution of `(q ≫ p)^* M` (a quasi-isomorphism), and
   `ψ'' := (pullbackComp q p).inv ≫ q^* ψ₁ ≫ ψ₂` satisfies the augmentation
   identity: in degree zero this is the naturality of `(pullbackComp q p).inv`
   followed by the degree-zero identities of `ψ₁` and `ψ₂`.
3. With `Φ_A`, `Φ_B`, `Φ_C` the maps `resolutionBaseChangeMap` of the three
   squares, `Φ_C = E ≫ c^* Φ_A ≫ Φ_B`, where `E` is the isomorphism of complexes
   induced by `(pullbackComp c b).inv`. Componentwise this is
   `pushforwardBaseChange_composite_eq`, cancellation of
   `(pullbackComp q p).hom ≫ (pullbackComp q p).inv`, and the published
   naturality `pushforwardBaseChange_naturality` of the second square's map.
4. All terms of `I₀`, `I₁`, `I₂` are injective, hence acyclic for every
   pushforward. `isIso_map_baseChangeNatTrans_app_iff` therefore gives:
   `c^*` of the first component is invertible iff `c^* (Hⁿ Φ_A)` is (with
   `γ = c^*`); the second component at `p^* M` is invertible iff `Hⁿ Φ_B` is, so
   `Hⁿ Φ_B` is invertible by `hB`; the composite component is invertible iff
   `Hⁿ Φ_C` is (with `γ` the identity).
5. `Hⁿ Φ_C = Hⁿ E ≫ Hⁿ(c^* Φ_A) ≫ Hⁿ Φ_B` with the outer factors invertible, so
   `Hⁿ Φ_C` is invertible iff `Hⁿ(c^* Φ_A)` is. Naturality of the published
   `LeftExactHomology.homologyNatTrans c^*`, an isomorphism since `c^*`
   preserves homology, shows that `Hⁿ(c^* Φ_A)` is invertible iff
   `c^*(Hⁿ Φ_A)` is.

The proof needs no composition law for the derived transformations
themselves, only this transfer of invertibility. The proof uses only the
standard axioms.
