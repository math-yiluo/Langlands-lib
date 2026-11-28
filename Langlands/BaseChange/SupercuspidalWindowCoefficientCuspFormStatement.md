# Cut-off coefficients of supercuspidal representations are cusp forms

The module `Langlands.BaseChange.SupercuspidalWindowCoefficientCuspFormStatement` states, as the
proposition `SupercuspidalWindowCoefficientCuspFormStatement.{u, v, uW}`, that a coefficient of
the contragredient of a supercuspidal representation of `GL_n(E)`, cut off by a determinant
window and multiplied by a locally constant function of the determinant, is a
Schwartz–Bruhat function with vanishing constant terms. The module states the proposition and
does not prove it.

## Notation (Library and Mathlib)

- `GeneralLinear n E` is `GL_n(E)`, with the topology of units of matrices;
  `GeneralLinear.determinant : GL_n(E) →* Eˣ`.
- `determinantWindow F m` (module `Langlands.BaseChange.DeterminantWindow`): the indicator of
  `0 ≤ ord_F N_{E/F}(det x) < m`.
- `GeneralLinear.IsSupercuspidal τ` (module `Langlands.Representation.Classification.Supercuspidal`):
  `τ` is admissible and its Jacquet coinvariants vanish for every proper block parabolic and
  every conjugate of it. Irreducibility is not assumed.
- `SmoothDual τ` (module `Langlands.Representation.Smooth.Contragredient.Definitions`): the
  smooth linear forms on `W`; `(ℓ : Module.Dual ℂ W)` is the underlying linear form.
- `SchwartzBruhat X` (module `Langlands.HarmonicAnalysis.Basic`): locally constant, compactly
  supported complex functions.
- `HasVanishingConstantTerms f` (module `Langlands.BaseChange.CuspForm`): for every standard
  block shape with at least two blocks and every Haar measure on its unipotent radical `U`,
  `u ↦ f(x u y)` is integrable on `U` and `∫_U f(x u y) du = 0` for all `x, y`.

## Statement

`SupercuspidalWindowCoefficientCuspFormStatement.{u, v, uW}` quantifies over a field
`F : Type u` with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, a
field `E : Type v` with `[Algebra F E] [Module.Finite F E] [TopologicalSpace E]
[IsTopologicalRing E] [IsModuleTopology F E]`, and `n : ℕ` with `0 < n`. For every
representation `τ : Representation ℂ (GeneralLinear n E) W` (`W : Type uW`) with
`GeneralLinear.IsSupercuspidal τ`, every `m : ℕ`, every `ψ : Eˣ → ℂ` with
`IsLocallyConstant ψ` (for the topology of units of `E`), every `v : W` and every
`ℓ : SmoothDual τ`, there is `φ : SchwartzBruhat (GeneralLinear n E)` with

1. `φ x = determinantWindow F m x * ψ (det x) * ℓ (τ x⁻¹ v)` for every `x`;
2. `HasVanishingConstantTerms φ`.

The case `E = F` (with `Algebra.id`, its own topology and `[E : F] = 1`) is included.

## Why it is true

Write `c(x) = λ(τ(x)⁻¹ v)` and `b = determinantWindow F m`.

- *Local constancy.* `c` is right invariant under the open stabilizer of the smooth form `λ`
  (`c(x k) = (τ̌(k)λ)(τ(x)⁻¹ v)`), `b` is locally constant
  (`isLocallyConstant_determinantWindow`), and `ψ ∘ det` is locally constant since `det` is
  continuous.
- *Compact support.* The coefficients of a supercuspidal representation are compactly
  supported modulo the centre `Z = E^×` (Renard 2026, VI.2.1, Théorème, printed
  pp. 137–138; in the Library, compact support of supercuspidal coefficients on the subgroup
  `|det| = 1` is `Langlands.AllField.GodementJacquet.hasCompactSupport_determinantUnit_coefficient`,
  for local fields given by `LocalFieldData`). The window bounds `ord_F N_{E/F}(det x)`, so it
  meets finitely many cosets of the subgroup `{|det x|_E = 1}`, and on each such coset `x₀ G¹`
  the function is a coefficient of `τ` restricted to `G¹` translated by `x₀`. Hence `b · c` has
  compact support, and so has `φ`.
- *Vanishing constant terms.* `det(x u y) = det(x y)` for `u` unipotent, so
  `φ(x u y) = b(x y) ψ(det(x y)) c(x u y)`. If `b(x y) ψ(det (x y)) = 0` the integral over `U`
  vanishes trivially. Otherwise the scalar function `u ↦ c(x u y)` is compactly supported on
  `U` (because `φ` is and `u ↦ x u y` is a closed embedding), and it is the integral of this
  scalar function that has to vanish. Write `v_x = τ(x)⁻¹ v` and `λ_y = λ ∘ τ(y)⁻¹`, so that
  `c(x u y) = λ_y(τ(u)⁻¹ v_x)`. By supercuspidality `v_x` lies in the kernel of the Jacquet
  coinvariants for `U`, so by Renard 2026, III.2.9 (printed p. 79) there is a compact open
  subgroup `U₀` of `U` with `∫_{U₀} τ(u) v_x du = 0`. The radical `U` is the union of an
  increasing sequence of compact open subgroups, so there is a compact open subgroup `U₁ ⊇ U₀`
  that contains the support of `u ↦ c(x u y)`. Then `∫_U c(x u y) du = ∫_{U₁} c(x u y) du =
  λ_y(∫_{U₁} τ(u)⁻¹ v_x du)`, where the last integral is a finite sum because `v_x` is smooth and
  `U₁` is compact; decomposing `U₁` into cosets of `U₀` (and using that `u ↦ u⁻¹` preserves the
  Haar measure of the unipotent group `U₁`) shows that it is zero. No integral of a vector over
  the whole radical occurs.

## Sources and provenance

The proposition is formulated for this Library (derived). It is the first step of the proof
sketch of `Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement`, where cut-off
coefficients of contragredients are used as test functions, after Henniart–Lemaire 2011
(*Changement de base et induction automorphe pour `GL_n` en caractéristique non nulle*, Mém.
SMF 124), II.6.3–II.6.4, printed pp. 119–121 (matrix coefficients of cuspidal representations
as test functions at an auxiliary place). The compact support modulo the centre is Renard,
*Représentations des groupes réductifs p-adiques* (2026 version), VI.2.1, Théorème, printed
pp. 137–138. The factor `ψ ∘ det` lets the statement cover, with `E = F`, the cut-off by the
indicator of the norm subgroup `N_{E'/F}(E'^×)` of a cyclic extension `E'/F`, which is open in
`F^×` (`IsCyclicAlgebra.normRange_isOpen_finiteIndex`).
