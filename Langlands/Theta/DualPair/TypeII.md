# The Weil representation of the type II dual pair `(GL_m(F), GL_n(F))`

**GKT §18.5.1–18.5.2** (the type II pair in the Siegel Levi `M(𝕏)`, p. 548; the matrix realization
of the Schrödinger model, p. 549), **§12.3.2** (Proposition 12.21 and Definition 12.22, the Leray
splitting of a type II pair, p. 367) and **§12.4.5** (Proposition 12.35, p. 384), for `D = F`.

The module `Langlands.Theta.DualPair.TypeII` defines the Weil representation of the type II dual
pair `(GL_m(F), GL_n(F))` in the model on Schwartz–Bruhat functions on `M_{n×m}(F)`. Howe duality
for it is stated in `Langlands.Theta.Correspondence.TypeII`.

## Content

- `typeIIWeil F m n : Representation ℂ (GeneralLinear m F × GeneralLinear n F)
  (SchwartzBruhat (Matrix (Fin n) (Fin m) F))`, for a locally compact topological field `F`:
  `(g, h) · Φ (x) = |det g|^{n/2} |det h|^{-m/2} Φ(h⁻¹ x g)` (`typeIIWeil_apply`), where
  `|·| = distribHaarChar F` is the modulus of `F` (for a nonarchimedean local field, the normalized
  absolute value). It is the Weil representation of the dual pair `(GL_m, GL_n)` inside `Sp_{2mn}`
  in the model attached to the polarization `M_{n×m}(F) ⊕ M_{m×n}(F)`, on which the metaplectic
  cover splits and the Weil representation is a geometric action twisted by the moduli of the
  determinants. The two actions commute and `x ↦ h⁻¹ x g` is a left action of the product, so this
  is a representation of `GL_m(F) × GL_n(F)`; the Schwartz–Bruhat space is preserved since
  `x ↦ h⁻¹ x g` is a homeomorphism (internal: `TypeII.Internal.act`, `.scalar`).
Literature: A. Mínguez, *Correspondance de Howe explicite : paires duales de type II*, Ann. Sci. Éc.
Norm. Sup. (4) 41 (2008), 717–741, Théorème 1, p. 718 (= Corollaire 6.3, p. 734), with the model
(1.4) of `ω_{n,m}`, pp. 721–722, which is `typeIIWeil` (Mínguez allows matrices over a division
algebra with centre `F`); Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps
p-adique* (Lecture Notes in Math. 1291, Springer 1987), chapter 2, III.1–III.2, pp. 44–45 (the
Schrödinger model of a type II pair, written on `𝒮(X₁ ⊗ X₂)` with both groups acting through
inverses, and Howe's conjecture), and III.5, p. 48 (the conjecture with multiplicities).

**The splitting** (over a nonarchimedean local field `F` with `⅟2`):

- `typeIIPairing F m n`, `(x, y) ↦ tr(x y)` on `M_{n×m}(F) × M_{m×n}(F)`; its polarized form is the
  symplectic form of `𝕎 = 𝕏 ⊕ 𝕏^*` with `𝕏 = W ⊗ V = M_{n×m}(F)` (p. 549) and `𝕏^*` identified
  with `M_{m×n}(F)` by the trace pairing.
- `typeIILevi F m n : GL_m(F) × GL_n(F) →* siegelLeviGroup (typeIIPairing F m n)`: `(g, h)` acts by
  `x ↦ h x g⁻¹` on `M_{n×m}(F)` and `y ↦ g y h⁻¹` on `M_{m×n}(F)` (the book's
  `(g ⊗ h)(w v) = A_g (w v) B_h⁻¹` with `(A_g, B_h) = (h, g)`, p. 549).
- `typeIISplitting hψ m n`: the splitting `siegelLeviSplitting` of the Siegel Levi (GKT Lemma 2.16
  for `m(a)`) composed with `typeIILevi`, in the Schrödinger model on `S(M_{n×m}(F))`;
  `weil_typeIISplitting`: its Weil representation is `typeIIWeil F m n` (the determinant of
  `x ↦ h x g⁻¹` is `det(h)^m det(g)^{-n}`, `TypeII.Internal.det_leftRight`).

The book defines its splitting `s_ψ` (Proposition 12.21) in the model `C_c^∞(𝕏^*)`, where the pair
lies in the Siegel parabolic `P(𝕏)`, and obtains the matrix formula of `typeIIWeil` on `C_c^∞(𝕏)`
by the Fourier transform `C_c^∞(𝕏) → C_c^∞(𝕏^*)` (p. 549). Here the model is `C_c^∞(𝕏)` from the
start and the splitting is that of the Siegel Levi of the other Lagrangian `𝕏^*` (the Levi is the
same group); the Fourier transform carries `typeIISplitting` to the book's `s_ψ` (it carries
`φ ↦ |det a|^{-1/2} φ(a⁻¹ ·)` on `𝕏` to `φ̂ ↦ |det a|^{1/2} φ̂(a^* ·)` on `𝕏^*`), but the Fourier
transform as an isomorphism of Schrödinger models is not formalized yet.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`, under
`src/Development/AbelianVarietyTheory/`: `Definitions/Foundations/MatrixMeasurableSpace.lean`,
lines 40–45 (`SplitWeil.om`). The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- `om μ g h` (an operator on all functions, with a character `μ` of `Fˣ`, used with `μ = 1`) →
  the representation `typeIIWeil F m n` (bundled, on Schwartz–Bruhat functions, without the
  character). The source's relation `Φ' = om 1 g h Φ → f Φ' = …` becomes the Library's
  `Representation.IntertwiningMap`.
- `nabs` → `distribHaarChar` (`ℝ≥0`-valued powers); `GL (Fin n) k` → `GeneralLinear n F`;
  `SB` → `SchwartzBruhat`.
- `typeIIWeil` is defined for every locally compact topological field.

## Declarations

- `Langlands.Theta.typeIIWeil`, `Langlands.Theta.typeIIWeil_apply`
- `Langlands.Theta.typeIIPairing`, `typeIIPairing_apply`, `continuous_typeIIPairing_left`,
  `typeIILevi`, `typeIISplitting`, `weil_typeIISplitting`; internal: `TypeII.Internal.leftRight`,
  `leftRight_apply`, `leftRight_symm_apply`, `det_leftRight`.

## Dependencies

`Langlands.HarmonicAnalysis.Basic`, `Langlands.Group.GL.Basic`,
`Langlands.Representation.Smooth.Definitions`, `Langlands.Theta.Metaplectic.SiegelLevi`; Mathlib: `MeasureTheory.Measure.Haar.DistribChar`,
`Topology.Instances.Matrix`.
