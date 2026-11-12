# Determinant multiplication by any Hecke character and adelic differential operators

Author: Worker 5136.

This internal module computes how the multiplier
`FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ` (module
`Langlands.Automorphic.HeckeTwist.SmoothMultiplier`), multiplication by
`g ↦ χ(det g)`, interacts with the Library's enveloping-algebra action
`finiteSmoothEnvelopingAction` on finite-smooth adelic functions. It also shows
that the multiplier preserves center finiteness. `χ` is any Hecke character. For
finite order, the Library's `DifferentialDeterminantMultiplier.lean` shows that
the multiplier commutes with every enveloping operator. For a general character
the operators commute only after a shift automorphism of the enveloping algebra.

All declarations are in the namespace `Langlands.Automorphic`.

- `heckeEnvelopingShift n χ` is the algebra endomorphism
  `ArchimedeanGL.characterShift` (module
  `Langlands.Global.ArchimedeanCharacterMultiplier`) for the smooth archimedean
  character `a ↦ χ(det a)` (`infiniteDeterminantCharacter`). On a complexified
  Lie algebra element `U` it is `U ↦ U + λ(U)`, where `λ` is the derivative of
  that character at the identity. `heckeCenterShift n χ` is its restriction to
  the center, and `centerInclusion_heckeCenterShift` relates the two.
- `finiteSmoothSlice_heckeDeterminantMultiplier`: on the infinite slice at a
  finite matrix `b`, the multiplied function is the constant `χ(det b)` times
  the archimedean character times the slice. This is
  `adelicDeterminant_pair_val`.
- `finiteSmoothEnvelopingAction_heckeDeterminantMultiplier`: for every
  enveloping element `u`, `D(u) (M_χ f) = M_χ (D(θ u) f)` with
  `θ = heckeEnvelopingShift n χ`. The Library's slice map is injective
  (`finiteSmoothSlice_injective`), and the action is computed slice by slice
  (`finiteSmoothSlice_envelopingAction`). On a slice the constant commutes with
  the linear operator, and `envelopingAction_characterMultiplier_apply` moves
  the operator past the character multiplier.
- `finiteSmoothCenterAction_heckeDeterminantMultiplier` is the case of a
  central element `z`, with `θ z` central.
- `orbitSpan_heckeDeterminantMultiplier_le`: the span of the center orbit of
  `M_χ f` lies in the image under `M_χ` of the span of the center orbit of `f`,
  because `z · M_χ f = M_χ (θ(z) · f)`.
- `isCenterFinite_heckeDeterminantMultiplier`: if the center orbit of `f` spans
  a finite-dimensional space, so does that of `M_χ f`. The proof uses the
  Library's `isCenterFinite_iff_finiteSmoothCenterVector`, the previous item and
  `Submodule.finiteDimensional_of_le`.

Provenance: internal. The commutation formula
`X ∘ M_χ = M_χ ∘ (X + dχ_∞(tr X))` and the preservation of center finiteness
are the steps for the enveloping algebra in the route sketched in the Markdown
of `Langlands.Automorphic.HeckeDeterminantTwistStatement`. No correspondence
with a particular passage of the literature is claimed.
