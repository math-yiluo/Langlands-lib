# Detecting isomorphisms out of the structure module on a fibre

Author: Worker 1119.

This helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement` proves that a morphism out of
the structure module of a scheme whose global functions form a field is an isomorphism as soon
as one pullback of it to a nonempty scheme is. It contains no `sorry` and no new axioms.

## Declarations

- `eq_zero_or_isUnit_of_smoothProperConnected`: if `κ` is a field and `p : F ⟶ Spec κ` is
  smooth, proper and geometrically connected, every `c : Γ(F, ⊤)` is zero or a unit. The
  published `smoothProperConnectedGlobalFunctions` makes `p.appTop` an isomorphism, and
  composed with `Scheme.ΓSpecIso κ` it gives a ring isomorphism `Γ(F, ⊤) ≃+* κ`.
- `structureModule_id_ne_zero`: on a nonempty scheme the identity of the structure module is
  not zero, because its value at `1` on global sections would be `1 = 0` in the nontrivial ring
  `Γ(Y, ⊤)`.
- `isIso_of_isIso_pullback_map`: let `F` be a scheme whose global functions are all zero or
  units, `e : N ≅ 𝒪_F`, `τ : 𝒪_F ⟶ N`, and `h : F₁ ⟶ F` with `F₁` nonempty. If
  `(pullback h).map τ` is an isomorphism, then `τ` is an isomorphism. Proof: the endomorphism
  `τ ≫ e.hom` of `𝒪_F` has a global value `c` (`structureEndValue`). If `c` is a unit,
  `τ ≫ e.hom` equals `structureAutOfUnit` by `structureEnd_ext`, so `τ` is an isomorphism. If
  `c = 0`, then `τ ≫ e.hom = 0` (`structureModule_hom_eq_zero_iff`), so `τ = 0` and its
  pullback is zero. A zero isomorphism forces the identity of `h^* 𝒪_F`, hence via
  `pullbackUnitIso h` the identity of `𝒪_{F₁}`, to vanish, contradicting
  `structureModule_id_ne_zero`.

## Provenance

Internal lemmas. In the proof of Stacks tag 0BF2 (lines 9615–9616 of `more-morphisms.tex` in
the registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`), the lifted section
restricts on the fibre `X_s` to a trivializing section. In the Lean proof this is verified on
the fibre of `X ×_S U ⟶ U` by this module's criterion, applied with `F₁` the nonempty fibre of
the first closed piece.
