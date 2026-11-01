# A section whose fibre pullback is a frame

Author: Worker 1119.

This helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement` turns surjectivity of the
restriction to a closed piece on global sections into a section whose fibre pullback is an
isomorphism. It contains no `sorry` and no new axioms.

## Main result: `exists_isIso_fiber_pullback`

Let `b : X' ⟶ B` be smooth, proper and geometrically connected, `g' : Y' ⟶ X'` with `g' ≫ b`
geometrically connected, `x : B`, and `M` a module on `X'`. Suppose `ζ : g'^* M ≅ 𝒪_{Y'}`, the
global sections of the unit `M ⟶ g'_* g'^* M` are surjective, and
`e : (b.fiberι x)^* M ≅ 𝒪` on the fibre `b.fiber x`. Then there is `σ : 𝒪_{X'} ⟶ M` with
`(b.fiberι x)^* σ` an isomorphism.

Proof.

1. Choose a global section `σ₀` of `M` whose unit image is `ζ⁻¹(1)`, and let
   `σ = sectionHom M σ₀`, so `σ(1) = σ₀` (`sectionHom_app_one`). By
   `isIso_pullback_map_of_unit_app`, `g'^* σ` is an isomorphism.
2. The fibre `b.fiber x` is smooth, proper and geometrically connected over `Spec κ(x)`, so its
   global functions are zero or units (`eq_zero_or_isUnit_of_smoothProperConnected`).
3. The fibre `(g' ≫ b).fiber x` is nonempty (Mathlib's `ConnectedSpace` instance for fibres of
   geometrically connected morphisms). It maps to `b.fiber x` by `hmap`, with
   `hcomm : hmap ≫ b.fiberι x = (g' ≫ b).fiberι x ≫ g'`.
4. Let `τ = (pullbackUnitIso (b.fiberι x)).inv ≫ (b.fiberι x)^* σ`. Its pullback along `hmap`
   is an isomorphism. Indeed, `g'^* σ` is an isomorphism, so is its pullback along
   `(g' ≫ b).fiberι x`. `pullbackComp` and `NatIso.isIso_map_iff` turn this into the pullback
   of `σ` along `(g' ≫ b).fiberι x ≫ g' = hmap ≫ b.fiberι x` (`hcomm`), and then into the
   pullback along `hmap` of `(b.fiberι x)^* σ`.
5. `isIso_of_isIso_pullback_map` with `e` gives that `τ`, hence `(b.fiberι x)^* σ`, is an
   isomorphism.

## Provenance

Internal lemma for the last step of the proof of Stacks tag 0BF2 (`more-morphisms.tex`, lines
9615–9616, registered source `stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`): "the
trivializing section of `𝓛_s` lifts to a section of `𝓛` over `X`". The source lifts the frame
of the fibre. The Lean proof lifts the frame of the first closed piece, which exists on all of
`Y'`, and checks the fibre condition with the field-valued global functions of the fibre.
