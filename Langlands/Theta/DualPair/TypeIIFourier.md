# The type II splitting through the Fourier transform

**GKT Proposition 12.21** (the splitting `s_ψ(g, h) = (m(g ⊗ h), 1)` of a type II pair through the
Siegel parabolic `P(𝕏)`, in the model `C_c^∞(𝕏^*)`) and **§18.5.2** (p. 549: the passage to the model
`C_c^∞(𝕏)` "by the Fourier transform"), with Theorem 1.25 (p. 34) and Lemma 2.16 (p. 58).

The module `Langlands.Theta.DualPair.TypeIIFourier` identifies `typeIISplitting` (module `Langlands.Theta.DualPair.TypeII`) with the
book's `s_ψ`: the Fourier transform between the two Schrödinger models carries the operators of the
one to the standard Weil operators of the other.

## Content

- `siegelLeviGroup.swap β`: a Levi pair `(a, a')` of `β` (`β(a x, a' y) = β(x, y)`) is the Levi
  pair `(a', a)` of `−β.flip`, the Siegel Levi of the other Lagrangian; `siegelLeviGroup.swap_apply`.
- `isPerfPair_neg` (instance): `−p` is perfect when `p` is.
- `det_siegelLevi_snd`: for a perfect pairing of finite-dimensional spaces, **`det a' =
  (det a)⁻¹`** (`a` is conjugate to the transpose of `a'⁻¹` through `X ≃ Y^*`;
  `LinearMap.det_conj`, `LinearMap.det_dualMap`).
- `schrodingerFourier_siegelLeviWeil`: **`F (|det a|^{-1/2} φ(a⁻¹ ·)) =
  |det a'|^{-1/2} (F φ)(a'⁻¹ ·)`**: the Fourier transform `F_{Y,X}` of
  `Langlands.Theta.Heisenberg.SchrodingerFourier` carries `siegelLeviWeil β` (module `Langlands.Theta.Metaplectic.SiegelLevi`) to
  `siegelLeviWeil (−β.flip)` composed with `swap` (change of variables `x = a x'`,
  `integral_comp_linearEquiv`; `β(a x, y) = β(x, a'⁻¹ y)`). This is the remark of GKT p. 549 that
  the Fourier transform turns `|det a|^{1/2} φ(a^* ·)` into `|det a|^{-1/2} φ(a⁻¹ ·)`.
- `isPerfPair_typeIIPairing` (instance): the trace pairing `(x, y) ↦ tr(x y)` of `M_{n×m}(F)` and
  `M_{m×n}(F)` is perfect (`Matrix.ext_iff_trace_mul_left`, `…_right`).
- `schrodingerFourier_typeIIWeil`: **`F ∘ typeIIWeil(g, h) = r'(m(g ⊗ h)) ∘ F`**, where `r'` is the
  standard Weil operator of the polarization `M_{m×n}(F) × M_{n×m}(F)` (functions on
  `𝕏^* = M_{m×n}(F)`, Lagrangian `𝕏 = M_{n×m}(F)`) at the image of `(g, h)` in its Siegel Levi
  (`standardOperator_siegelLevi`). So `typeIISplitting`, transported by `F`, is the book's splitting
  `(g, h) ↦ (m(g ⊗ h), r(m(g ⊗ h)))` of Proposition 12.21.

The matrix topology is supplied by the local instance `isModuleTopology_matrix`, as in
`Langlands.Theta.DualPair.TypeII`.

## Declarations

- `siegelLeviGroup.swap`, `siegelLeviGroup.swap_apply`, `isPerfPair_neg`, `det_siegelLevi_snd`.
- `schrodingerFourier_siegelLeviWeil`, `isPerfPair_typeIIPairing`, `schrodingerFourier_typeIIWeil`.

All in the name space `Langlands.Theta`.

## Dependencies

`Langlands.Theta.DualPair.TypeII` (`typeIIWeil`, `typeIISplitting`, `typeIILevi`),
`Langlands.Theta.Heisenberg.SchrodingerFourier` (`schrodingerFourier`),
`Langlands.Theta.Metaplectic.SiegelParabolic` (`standardOperator_siegelLevi`,
`integral_comp_linearEquiv`).
