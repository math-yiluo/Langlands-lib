# Multiplication by a smooth character and the archimedean enveloping action

Author: Worker 5136.

This internal module describes how multiplication by a smooth character of the
archimedean matrix group interacts with the Library's enveloping-algebra action
on smooth functions (`ArchimedeanGL.envelopingAction`). The Library's
finite-order development multiplies by a locally constant character, which
commutes with every differential operator
(`ArchimedeanLocallyConstantMultiplier.lean`). A general character is only
smooth, and then the operators commute only after an automorphism `θ` of the
enveloping algebra.

All declarations are in the namespace `Langlands.Global.ArchimedeanGL`.

## Products of smooth functions

`mul_mem_smoothFunctions`: the pointwise product of two smooth functions is
smooth, by `ContDiff` of multiplication on `ℂ`.

## The shift automorphism of the enveloping algebra

Let `μ : ComplexLieAlgebra F n →ₗ[ℂ] ℂ` be a complex-linear form with
`μ ⁅U, V⁆ = 0` for all `U V`.

- `envelopingShiftLie μ hμ` is the Lie algebra map `U ↦ ι U + μ(U) · 1` into the
  enveloping algebra. It respects brackets because the scalars `μ(U) · 1` are
  central and `μ ⁅U, V⁆ = 0`.
- `envelopingShift μ hμ` is its extension to an algebra endomorphism of the
  enveloping algebra (`UniversalEnvelopingAlgebra.lift`), with
  `envelopingShift_generator` on generators.
- `envelopingShift_neg_comp` and `envelopingShift_comp_neg`: the shifts by `μ`
  and `-μ` are mutually inverse (both composites fix the generators;
  `UniversalEnvelopingAlgebra.hom_ext`). `neg_lie_eq_zero` records that `-μ`
  vanishes on brackets.
- `envelopingShift_mem_center`: the shift maps central elements to central
  elements, because it is surjective. `centerShift μ hμ` is its restriction to
  `EnvelopingCenter F n`, with `centerInclusion_centerShift`.

## The derivative of a smooth character

Let `c : GL_n(F_∞) →* ℂˣ` be a group homomorphism whose values form a smooth
function (`hc`).

- `characterFunction c hc` is `c` as an element of `SmoothFunctions F n`, and
  `characterMultiplier c hc` is the complex-linear operator `f ↦ c · f`.
- `smoothDifferential_characterMultiplier_apply` is the Leibniz rule
  `D_X (c f) = c · D_X f + D_X c · f`. It is computed on the Library's
  coordinate extensions (`smoothDifferential_apply`) with `fderiv_fun_mul`.
- `characterDifferential c hc : RealLieAlgebra F n →ₗ[ℝ] ℂ` is
  `X ↦ (D_X c)(1)`, the derivative of `c` at the identity.
  Linearity comes from linearity of `realSmoothDifferential`.
- `smoothDifferential_characterFunction`: `D_X c = λ(X) · c` with
  `λ = characterDifferential c hc`. Near the identity, the coordinate extension
  `E` of `c` satisfies `E (g a) = c(g) E(a)`, because `c` is multiplicative.
  Differentiating at `a = 1` in the direction `X` by the chain rule gives
  `(D_X c)(g) = c(g) λ(X)`.
- `characterDifferential_lie`: `λ ⁅X, Y⁆ = 0`. The Library's commutator law
  `smoothDifferential_commutator` gives
  `D_{⁅X, Y⁆} c = D_X D_Y c - D_Y D_X c = λ(Y)λ(X) c - λ(X)λ(Y) c = 0`.
  Evaluate at `1`.
- `complexCharacterDifferential c hc` is the complex-linear extension of `λ` to
  `ComplexLieAlgebra F n = ℂ ⊗[ℝ] RealLieAlgebra F n`, with
  `complexCharacterDifferential_tmul`. `complexCharacterDifferential_lie`
  shows that it vanishes on brackets, by induction on tensors and
  `complexLieAlgebra_lie_tmul`.
- `characterShift c hc` and `characterCenterShift c hc` are the shift by this
  form on the enveloping algebra and on its center.

## Commutation

- `smoothDifferential_characterMultiplier`:
  `D_X ∘ M_c = M_c ∘ (D_X + λ(X))`, from the Leibniz rule and
  `D_X c = λ(X) c`.
- `complexSmoothLieAction_characterMultiplier` extends this to the complexified
  Lie algebra action, by induction on tensors.
- `envelopingAction_characterMultiplier`:
  `envelopingAction u ∘ M_c = M_c ∘ envelopingAction (characterShift c hc u)`
  for every enveloping element `u`. The proof writes `u` as the image of a
  tensor-algebra element and inducts on it (`TensorAlgebra.induction`), as the
  Library's `ArchimedeanLocallyConstantMultiplier.lean` does. Scalars commute
  with `M_c`. On generators this is the previous item. Products and sums
  follow because both sides are multiplicative and additive in `u`.
- `envelopingAction_characterMultiplier_apply` is the pointwise form, and
  `centerAction_characterMultiplier` is its specialization to central
  elements, with the shifted central element `characterCenterShift c hc z`.

Provenance: internal. Twisting by `χ ∘ det` changes infinitesimal characters by
the derivative of `χ_∞ ∘ det`. This is standard, and this module proves it in
the Library's setting. It is an ingredient for Henniart (2000), §2.2, which
twists by arbitrary quasicharacters. No correspondence with a particular passage
of the literature is claimed.
