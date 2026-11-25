# The splitting of the Siegel Levi subgroup

**GKT §2.3.2** (the Siegel parabolic `P(X)` and its Levi `M(X) = {m(a)}`, p. 57; **Lemma 2.16**,
p. 58: `r(m(a)n(b)) φ(y) = ψ(½⟨a^*y, −b a^*y⟩) |det a|^{1/2} φ(a^*y)`, here for `b = 0`), on the
metaplectic group of pairs of §2.1.2 (relation (2.2), p. 47; `Mp(W)^{ℂ¹}`, p. 49).

The module `Langlands.Theta.Metaplectic.SiegelLevi` defines the Siegel Levi subgroup of a
polarization and its splitting in the metaplectic group of pairs of the Schrödinger model:
`m ↦ (m, φ ↦ |det a|^{-1/2} φ(a⁻¹ ·))`.

## Content

For a pairing `β : X →ₗ[R] Y →ₗ[R] R`, `W = X × Y` with `polarizedForm β` is polarized by `X × 0`
and `0 × Y`, and the Schrödinger model `HeisenbergGroup.schrodingerSB` lives on functions on `X`.
In the book's notation the functions live on `Y` and the parabolic stabilizes `X`: the file's
`(X, Y)` is the book's `(Y, X)`.

- `siegelLeviGroup β : Subgroup ((X ≃ₗ[R] X) × (Y ≃ₗ[R] Y))`: the pairs `(a, a')` with
  `β (a x) (a' y) = β x y` (`mem_siegelLeviGroup`), the Levi of the Siegel parabolic of the
  Lagrangian `0 × Y`; `siegelLeviGroup.toIsometry β`, `(a, a') ↦ a × a'`, into
  `isometryGroup (polarizedForm β)` (`siegelLeviGroup.toIsometry_apply`).
- `dualSiegelLevi R V : (V ≃ₗ[R] V) →* siegelLeviGroup LinearMap.id`, `a ↦ ((a⁻¹)^*, a)`: for the
  polarization `V^* × V` with the canonical pairing, the book's `a ↦ m(a)`, `a ∈ GL(V)`, with
  `a^∨ = (a^*)⁻¹` acting on `V^*` (`dualSiegelLevi_apply`).
- Over a nonarchimedean local field `F` with `X` finite-dimensional with its module topology:
  `siegelLeviScalar F a = |det a|^{-1/2}`, `|·| = distribHaarChar F`, multiplicative
  (`siegelLeviScalar_mul`, `siegelLeviScalar_one`); `siegelLeviWeil β`, the representation of
  `siegelLeviGroup β` on `S(X)` by `φ ↦ |det a|^{-1/2} φ(a⁻¹ ·)` (`siegelLeviWeil_apply`).
- `siegelLeviWeil_normalizes`: it normalizes `schrodingerSB` along `toIsometry` (relation (2.2):
  `β(x, a' y) = β(a⁻¹ x, y)`); `siegelLeviSplitting hψ hβ`, the splitting, with
  `weil_siegelLeviSplitting`.
- `siegelLeviWeil_lintegral_enorm_sq`: `∫⁻ ‖ω(m) φ‖ₑ² = ∫⁻ ‖φ‖ₑ²` for every Haar measure, since
  `x ↦ a⁻¹ x` multiplies Haar measure by `|det a|` (`HarmonicAnalysis.map_linearEquiv_addHaar`);
  this is what fixes the factor `|det a|^{1/2}` of Lemma 2.16. `siegelLeviSplitting_mem_unitary`:
  the splitting lands in `Mp(W)^{ℂ¹}`.
- `siegelLeviWeil_dualSiegelLevi_apply`: **Lemma 2.16 for `m(a)` in the book's form**: for the
  polarization `V^* × V`, `m(a)` acts by `φ ↦ |det a|^{1/2} φ(a^* ·)`, `a^* f = f ∘ a`
  (`det (a⁻¹)^* = det a⁻¹`, `LinearMap.det_dualMap`).

The Siegel unipotent radical `n(b)` and the operators `r(g)` of Proposition 2.13 on the other cells
are not formalized here.

## Declarations

- `Langlands.Theta.siegelLeviGroup`, `mem_siegelLeviGroup`, `siegelLeviGroup.toIsometry`,
  `siegelLeviGroup.toIsometry_apply`, `dualSiegelLevi`, `dualSiegelLevi_apply`.
- `Langlands.Theta.siegelLeviScalar`, `siegelLeviScalar_mul`, `siegelLeviScalar_one`,
  `siegelLeviWeil`, `siegelLeviWeil_apply`, `siegelLeviWeil_normalizes`, `siegelLeviSplitting`,
  `weil_siegelLeviSplitting`, `siegelLeviWeil_lintegral_enorm_sq`,
  `siegelLeviSplitting_mem_unitary`, `siegelLeviWeil_dualSiegelLevi_apply`.

## Dependencies

`Langlands.Theta.Metaplectic.Defs`, `Langlands.Theta.Heisenberg.SchrodingerUnitary`,
`Langlands.HarmonicAnalysis.LinearHaarScaling` (`map_linearEquiv_addHaar`).
