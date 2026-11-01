# Pullback squares for the fibre frame lifting assembly

Author: Worker 1119.

Two general facts used by the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`. The module contains no
`sorry` and no new axioms.

- `isPullback_of_over`: in any category, let `P₁` and `P` be pullbacks of `h₁ : X₁ ⟶ S` and
  `h : X ⟶ S` along the same `t : T ⟶ S`, and let `i : X₁ ⟶ X` satisfy `i ≫ h = h₁`. Then a
  morphism `m : P₁ ⟶ P` compatible with `i` and with the projections to `T` makes
  `(P₁ ⟶ X₁, m, i, P ⟶ X)` a pullback square. Proof: `IsPullback.of_bot` (pullback pasting).
- `fromSpecResidueField_eq_comp_fromSpec`: for an affine open `V ∋ s` of a scheme `S`,
  `S.fromSpecResidueField s` is `Spec` of `germ ≫ residue : Γ(S, V) ⟶ κ(s)` followed by
  `hV.fromSpec`. Proof: unfold `fromSpecResidueField`, rewrite `S.fromSpecStalk s` as
  `hV.fromSpecStalk hs` (Mathlib's `IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`), and use
  `Spec.map_comp`.

## Provenance

Internal lemmas, used to place the fibre `Spec κ(s) ⟶ S` over an affine open neighbourhood
of `s`. The proof of Stacks tag 0BF2 does this when it shrinks `S` to an affine
neighbourhood of `s`.
