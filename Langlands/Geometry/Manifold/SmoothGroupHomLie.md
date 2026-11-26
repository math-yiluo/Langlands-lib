# Tangent maps of smooth group homomorphisms and smooth characters

Module `Langlands.Geometry.Manifold.SmoothGroupHomLie`, namespace
`Langlands.Geometry.Manifold`. Internal calculus on real Lie groups in Mathlib's sense
(`LieGroup I ∞ G` on a charted space modelled on `I : ModelWithCorners ℝ E H`). The derivative
`groupDirectionalValue I X f g = mvfderiv I (fun h => f (g * h)) 1 X` is the Library's
positive right-orbit derivative (module `SmoothGroupDifferential`), and the bracket on
`GroupLieAlgebra I G` is Mathlib's bracket of left-invariant vector fields. There is no
literature source: these are the standard facts that the differential of a homomorphism of Lie
groups is a homomorphism of Lie algebras and that the differential of a character kills brackets.

## Declarations

- `groupHomTangent I I' φ` is `mfderiv I I' φ 1`, the derivative at the identity of a
  homomorphism `φ : G →* G'`, as a continuous real-linear map
  `GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I' G'`.
- `groupDirectionalValue_comp_hom`: for a smooth homomorphism `φ` and a smooth
  `f : G' → ℂ`, the orbit derivative of `f ∘ φ` in the direction `X` at `g` is the orbit
  derivative of `f` in the direction `groupHomTangent I I' φ X` at `φ g`. The proof writes
  `h ↦ f(φ(g h))` as `(k ↦ f(φ(g) k)) ∘ φ` and applies the chain rule at the identity,
  using `φ 1 = 1`.
- `groupDirectionalValue_one`: at the identity the orbit derivative is `mvfderiv I f 1 X`.
- `groupHomTangent_lie_of_separating`: with complete boundaryless models, if every tangent
  vector `W` at the identity of `G'` with `mvfderiv I' f 1 W = 0` for all smooth
  `f : G' → ℂ` is zero, then `groupHomTangent I I' φ ⁅X, Y⁆` is the bracket of the images
  of `X` and `Y`. The proof applies the commutator identity
  `groupDirectionalValue_commutator_of_vectorFieldCommutator` (module
  `SmoothGroupLieDifferential`) on `G` to `f ∘ φ` and on `G'` to `f`, with the scalar
  commutator `smoothVectorFieldCommutator_proof` (module `VectorFieldCommutator`) on both
  groups. Two applications of the chain rule identify the two right-hand sides at the
  identity, so the difference of the two tangent vectors is killed by every `mvfderiv I' f 1`.
- `eq_zero_of_forall_mvfderiv_eq_zero`: on a Hausdorff manifold modelled on a
  finite-dimensional real space, smooth complex functions separate the tangent vectors at
  each point. For a real functional `ℓ` on the model space, a smooth bump function `b` at `x`
  multiplies `y ↦ ℓ(φ y)` (`φ` the extended chart at `x`) to a global smooth function equal to
  it near `x`. Its derivative at `x` in the direction `W` is `ℓ` applied to the chart derivative
  of `W`. If all these vanish, the chart derivative of `W` is zero; it is invertible
  (`isInvertible_mfderiv_extChartAt`), so `W = 0`.
- `groupDirectionalValue_character`: if `χ : G → ℂ` is smooth and multiplicative
  (`χ (x * y) = χ x * χ y`), its orbit derivative is `χ g * mvfderiv I χ 1 X`.
- `mvfderiv_character_lie`: for such `χ`, `mvfderiv I χ 1 ⁅X, Y⁆ = 0`. The commutator
  identity gives `dχ(Y) dχ(X) χ(1) - dχ(X) dχ(Y) χ(1)`.
