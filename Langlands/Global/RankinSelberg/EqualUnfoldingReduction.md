# A conditional reduction of the equal-rank unfolding statement

`Langlands.Global.RankinSelbergGlobal.EqualUnfoldingReductionStatement` is the Prop-valued
statement that four explicitly stated premises imply the Library statement
`Langlands.Global.RankinSelbergGlobal.EqualUnfoldingStatement`, provided the premises hold for
every equal-rank pair of cuspidal realizations. The target is Cogdell, *Analytic theory of
L-functions for GL_n* (2004), §2.3, printed pp.210–211 (PDF pp.213–214), source
`cogdell-2004-analytic-theory-gln`. The module also proves the reduction:
`equalUnfoldingReduction : EqualUnfoldingReductionStatement`. The premises remain open, so
this is a conditional result and not a proof of `EqualUnfoldingStatement`.

Provenance: derived. The conclusion is the existing Library statement. Two premises are
existing Library predicates. The other two are the absolute-convergence inputs of Cogdell's
argument, stated for the Library's actual objects.

## The statement

`EqualUnfoldingReductionStatement.{u}` is

`(∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
   (T T' : CuspidalOperatorRealization F r), EqualUnfoldingPremises F T T')
 → EqualUnfoldingStatement.{u}`.

`EqualUnfoldingPremises F T T'` is the conjunction of the four premises below. Notation:
`n = r + 1`, `φ = cuspFunction F T v`, `φ' = cuspFunction F T' v'`, `W = cuspWhittaker F T ψ v`,
`W' = cuspWhittaker F T' ψ⁻¹ v'`. A tilde denotes the Library's `dualFunction F n`
(`f̃(g) = f(w ᵗg⁻¹)`). `Φ̂ = fourierTransform F n ψ Φ`, `e_n g = lastRow F r g`, and
`|det g|^s = detPower F n g s`. `N_n(F) \ GL_n(𝔸)` carries the Library's
`LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F n) _` (ambient Haar measure and
counting measure), and functions on it are evaluated at quotient representatives `q.out`.
"Standard" means `IsStandardAdditiveCharacter`.

1. **E, `CuspidalWhittakerExpansion F T`** (Library, module `ProjectionExpansion`): for every
   standard `ψ`, every `v` and every `g ∈ GL_n(𝔸)`, the family `γ ↦ W(diag(γ, 1) g)` over
   `N_r(F) \ GL_r(F)` is absolutely summable with sum `φ(g)`. This is Cogdell's Theorem 1.1, the
   Fourier expansion that p.210 substitutes: "replace φ by its Fourier expansion and unfold as
   before". For all realizations at once it is the Library's
   `CuspidalWhittakerExpansionStatement` (module `ProjectionExpansionReduction`).
2. **Ẽ, `DualCuspidalWhittakerExpansion F T`** (Library, module
   `DualWhittakerExpansionStatement`): the same expansion `φ̃(g) = Σ_γ W̃(diag(γ, 1) g)` for the
   dual cusp form, with absolute convergence that is uniform on compact sets. Only the pointwise
   `HasSum` part is used.
3. **G, `EqualWhittakerGaugeIntegrable F T T'`**: there is `C ≥ 0` such that, for every
   standard `ψ`, all `v`, `v'`, every Schwartz–Bruhat `Φ` and every `s` with `Re s > C`, the
   function `g ↦ W(g) φ'(g) Φ(e_n g) |det g|^s` is integrable on `N_n(F) \ GL_n(𝔸)`. This is
   the absolute convergence that the Fourier-expansion step needs. Cogdell p.210: "This
   expression converges for Re(s) » 0". In the source it comes from the gauge estimates of `W`
   together with the boundedness of the cusp form `φ'`.
4. **G̃, `DualEqualWhittakerGaugeIntegrable F T T'`**: there is `C ≥ 0` such that, for every
   standard `ψ`, all `v`, `v'`, every Schwartz–Bruhat `Φ` and every `s` with `Re s > C`, the
   function `g ↦ W̃(g) φ̃'(g) Φ̂(e_n g) |det g|^s` is integrable on `N_n(F) \ GL_n(𝔸)`. This is the
   same input for the contragredient data. `W̃` is a `ψ⁻¹`-Whittaker function of `φ̃`. Cogdell
   p.211 remarks that the right-hand side of the functional equation "also unfolds", "with
   convergence for Re(s) « 0".

In G and G̃ the bound `C` is uniform over standard characters, vectors and Schwartz–Bruhat
functions, as the target statement requires. The premises are stated with Library definitions
only. The helper `equalKernel` is not used in them.

## Results

All results are in this module.

- `EqualUnfolding.ideleMeasure_ideleDomain_slab`: every band `{c < |a| ≤ e c}` of the chosen
  fundamental domain of `F^×` in `𝔸^×` has `ideleMeasure`-mass one. This is the Library's
  `ideleMeasure_fundamentalDomain_Ioc` (module `EqualUnfoldingIdele`), and it discharges the
  hypothesis `hslab` of `eisenstein_unfolding`.
- `EqualUnfolding.integrable_cuspWhittakerIntegrand` and
  `EqualUnfolding.integrable_dualCuspWhittakerIntegrand`: the integrability in G (resp. G̃) at
  one `s` gives integrability of `equalWhittakerIntegrand F W W' Φ s` (resp. of
  `equalWhittakerIntegrand F W̃ W̃' Φ̂ s`) for `whittakerQuotientMeasure`. These are
  `integrable_equalWhittakerIntegrand_of_kernel` (`EqualUnfoldingWhittaker.md`) with
  `ψ₀ = ψ` (resp. `ψ₀ = ψ⁻¹`).
- `integrable_equalWhittakerIntegrand_of_gauge` and
  `integrable_dualEqualWhittakerIntegrand_of_gauge`: G alone (resp. G̃ alone) gives a bound
  `C ≥ 0`, uniform as above, beyond which the Whittaker-side integrand of
  `EqualUnfoldingStatement` (resp. its dual) is integrable. No Whittaker expansion is used.
- `EqualUnfolding.equal_unfolding_primal`: let `T`, `T'` have central characters `ω`, `ω'`.
  Under E, and under the integrability of G at one point `s`, the integrand
  `equalIntegrand F (ω ω') φ φ' Φ s` is integrable for `centralQuotientMeasure`, the Whittaker
  integrand is integrable, and `equalIntegral F (ω ω') φ φ' Φ s = equalWhittakerIntegral F W W' Φ s`.
- `EqualUnfolding.equal_unfolding_dual`: the same for `(ω ω')⁻¹`, `φ̃`, `φ̃'`, `W̃`, `W̃'`, `Φ̂`,
  under Ẽ and the integrability of G̃ at `s`.
- `equalUnfoldingReduction : EqualUnfoldingReductionStatement.{u}`.

## Proof

`equalUnfoldingReduction` takes the bounds `C₁` and `C₂` of G and G̃ and sets `C = max C₁ C₂`.
For `Re s > C` it applies `equal_unfolding_primal` at `s`. For `Re s < -C` it applies
`equal_unfolding_dual` at `1 - s`, since `Re(1 - s) > 1 + C ≥ C₂`.

Both one-point theorems follow Cogdell's unfolding on p.210 in three steps.

- **Step I** (`eisenstein_unfolding`, `EqualUnfoldingEisenstein.md`): "replace the Eisenstein
  series by its definition, and unfold". The Library integral over `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` of
  `φ φ' E(·, Φ; s, ω ω')` becomes the integral of `φ φ' Φ(e_n ·) |det|^s` over
  `P_n(F) \ GL_n(𝔸)`. The central characters cancel (`cuspFunction_mul_scalarPoint_mul`,
  `EqualUnfoldingCusp.md`), and the slab normalization of `centralQuotientMeasure` is absorbed
  by the fiber computation (`EqualUnfoldingFiber.md`, `EqualUnfoldingCount.md`) and the band
  masses above.
- **Step II** (`mirabolic_unfolding`, `EqualUnfoldingWhittaker.md`): substitute the expansion E
  and unfold the sum over `N_r(F) \ GL_r(F)` against `P_n(F) \ GL_n(𝔸)`, giving an integral over
  `N_n(F) \ GL_n(𝔸)`. The integrability in G licenses the exchange of sum and integral.
- **Step III** (same theorem): average over `N_n(F) \ N_n(𝔸)`, which turns `φ'` into its
  `ψ⁻¹`-Whittaker function `W'` (`cuspWhittaker_inv_eq_setIntegral`). The Library's mass
  normalizations cancel exactly. Then pass to `N_n(𝔸) \ GL_n(𝔸)` with
  `whittakerQuotientMeasure`.

The step-I hypotheses about `φ`, `φ'` and `Φ` (measurability, left `GL_n(F)`-invariance,
central characters) are proved in `EqualUnfoldingCusp`, or taken from the Library's
`UnfoldingGL` and `UnfoldingDual`. They are not premises. In the dual case the same theorems
run with the character `ψ⁻¹`. The `θ`-equivariance of `W̃` and `W̃'` and the coefficient formula
for `W̃'` come from the Library's `dualCuspWhittaker_unipotent_mul` and
`dualCuspWhittaker_eq_setIntegral` (module `UnfoldingDual`).

Supporting modules, in dependency order: `EqualUnfoldingKernel`, `EqualUnfoldingWhittaker`,
`EqualUnfoldingScalar`, `EqualUnfoldingSection`, `EqualUnfoldingFiber`, `EqualUnfoldingCount`,
`EqualUnfoldingEisenstein` and `EqualUnfoldingCusp`.

## What remains for the unconditional statement

Discharging the premises would prove `EqualUnfoldingStatement`. E and Ẽ for all realizations
are the open Library statements `CuspidalWhittakerExpansionStatement` and
`DualCuspidalWhittakerExpansionStatement`. G and G̃ for all equal-rank pairs need the gauge
estimates for cuspidal Whittaker functions (Jacquet–Shalika) and the boundedness of cusp forms.
