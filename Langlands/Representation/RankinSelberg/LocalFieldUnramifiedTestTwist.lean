import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof
import Langlands.Representation.RankinSelberg.GeneralPairGamma
import Langlands.Representation.RankinSelberg.HighlyRamified.UnitaryGamma
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries

/-!
# Unramified twists of gamma factors over every nonarchimedean local field

Let `F` be a nonarchimedean local field, `ϖ` a uniformizer, `q` the residue cardinality,
and `abv` the normalized absolute value (`abv ϖ = q⁻¹`, `abv = 1` on valuation units).
For `z : ℂˣ` let `χ_z = Conductor.UnramifiedPrincipalSeries.character hϖ z` be the
unramified character with `χ_z(ϖ) = z`. Twisting by `χ_z ∘ det` replaces `s` by `s + u`
with `q^(-u) = z`, so it rescales a gamma factor `G(X)`, `X = q^(-s)`, to `G(zX)`. This
module records that rescaling for the general-field gamma relations, from the published
field-generic transport `UnramifiedGammaTwist.pair_both`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open Langlands.GeneralLinear.Iwasawa

universe uF uV uW

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The normalized absolute value of a unit `a` is `q^(-ord a)`. -/
theorem abv_eq_inv_zpow_ord {q : ℕ} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) (a : Fˣ) :
    abv (a : F) = ((q : ℝ)⁻¹) ^ Conductor.UnramifiedPrincipalSeries.ord hϖ a := by
  set k := Conductor.UnramifiedPrincipalSeries.ord hϖ a
  have hv0 : ValuativeRel.valuation F (ϖ : F) ≠ 0 :=
    (valuation_pos (ValuativeRel.valuation F) ϖ).ne'
  have hb : ValuativeRel.valuation F ((a : F) * (ϖ : F) ^ (-k)) = 1 := by
    rw [map_mul, map_zpow₀, Conductor.UnramifiedPrincipalSeries.valuation_eq_pow_ord hϖ a,
      ← zpow_add₀ hv0, add_neg_cancel, zpow_zero]
  have h1 := hunit _ hb
  rw [map_mul, map_zpow₀, habv] at h1
  have hqi : ((q : ℝ)⁻¹) ≠ 0 := by
    rw [← habv]
    exact (abv.pos (Units.ne_zero ϖ)).ne'
  calc abv (a : F) = abv (a : F) * ((q : ℝ)⁻¹) ^ (-k) * ((q : ℝ)⁻¹) ^ k := by
        rw [mul_assoc, ← zpow_add₀ hqi, neg_add_cancel, zpow_zero, mul_one]
    _ = ((q : ℝ)⁻¹) ^ k := by rw [h1, one_mul]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The unramified character `χ_z` is the absolute-value power `|·|^u` for any `u`
with `q^(-u) = z`. -/
theorem unramifiedCharacter_eq_abv_cpow {q : ℕ} (hq : 1 < q) {abv : AbsoluteValue F ℝ}
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
    {z : ℂˣ} {u : ℂ} (hu : spectralShiftUnit q hq u = z) (a : Fˣ) :
    (Conductor.UnramifiedPrincipalSeries.character hϖ z a : ℂ) =
      (abv (a : F) : ℂ) ^ u := by
  set k := Conductor.UnramifiedPrincipalSeries.ord hϖ a
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  rw [Conductor.UnramifiedPrincipalSeries.character_apply, abv_eq_inv_zpow_ord hϖ habv hunit a,
    ← hu, Units.val_zpow_eq_zpow_val, coe_spectralShiftUnit, spectralPoint]
  rw [inv_zpow', ← Real.rpow_intCast, Complex.ofReal_cpow hq0.le, Complex.ofReal_natCast,
    ← Complex.cpow_mul, ← Complex.cpow_int_mul]
  · congr 1
    push_cast
    ring
  · have him : ((Complex.log (q : ℂ)) * (((-k : ℤ) : ℝ) : ℂ)).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq0.le, ← Complex.ofReal_mul,
        Complex.ofReal_im]
    rw [him]
    exact neg_lt_zero.mpr Real.pi_pos
  · have him : ((Complex.log (q : ℂ)) * (((-k : ℤ) : ℝ) : ℂ)).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq0.le, ← Complex.ofReal_mul,
        Complex.ofReal_im]
    rw [him]
    exact Real.pi_pos.le

/-- The twist `σ ⊗ (χ_z ∘ det)` of a representation `σ` of `GL(n+1, F)` by the unramified
character `χ_z = Conductor.UnramifiedPrincipalSeries.character hϖ z`, the character of `Fˣ`
trivial on valuation units with `χ_z(ϖ) = z`. -/
def unramifiedDetTwist {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (z : ℂˣ) {m : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
    (σ : Representation ℂ (Langlands.GeneralLinear m F) U) :
    Representation ℂ (Langlands.GeneralLinear m F) U :=
  Langlands.twist ((Conductor.UnramifiedPrincipalSeries.character hϖ z).comp determinant) σ

variable {q : ℕ} (hq : 1 < q) {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : letI := borel F; AdditiveHaarMeasure F} {ϖ : Fˣ}
  (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
  (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

include hq hϖ habv hunit in
/-- Twisting either representation of a general-field pair by `χ_z ∘ det` rescales its
gamma factor `G(X)` to `G(zX)`. -/
theorem isGeneralPairGammaFactor_unramifiedTwist (z : ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsGeneralPairGammaFactor q ψ abv ν π σ G) :
    IsGeneralPairGammaFactor q ψ abv ν π
        (unramifiedDetTwist hϖ z σ) (rationalRescale z G) ∧
      IsGeneralPairGammaFactor q ψ abv ν
        (unramifiedDetTwist hϖ z π) σ (rationalRescale z G) := by
  obtain ⟨u, hu⟩ := HighlyRamified.exists_spectralShiftUnit_eq hq z
  have hχ := unramifiedCharacter_eq_abv_cpow hq hϖ habv hunit hu
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  have h' := UnramifiedGammaTwist.pair_both q hq ψ abv ν u
    (Conductor.UnramifiedPrincipalSeries.character hϖ z) hχ π σ h
  rw [hu] at h'
  exact h'

include hq hϖ habv hunit in
/-- The larger-rank-first relation under the same twists: `G(X)` becomes `G(zX)`. -/
theorem isGeneralSymmetricGammaFactor_unramifiedTwist (z : ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {G : RationalFunctions} (h : IsGeneralSymmetricGammaFactor q ψ abv ν π σ G) :
    IsGeneralSymmetricGammaFactor q ψ abv ν π
        (unramifiedDetTwist hϖ z σ) (rationalRescale z G) ∧
      IsGeneralSymmetricGammaFactor q ψ abv ν
        (unramifiedDetTwist hϖ z π) σ (rationalRescale z G) := by
  unfold IsGeneralSymmetricGammaFactor at h ⊢
  split_ifs at h ⊢
  · exact isGeneralPairGammaFactor_unramifiedTwist hq hϖ habv hunit z π σ h
  · exact (isGeneralPairGammaFactor_unramifiedTwist hq hϖ habv hunit z σ π h).symm

include hq hϖ habv hunit in
/-- The unramified test: a gamma factor `G` of `(π, 1)` gives the gamma factor `G(zX)`
of `(π, χ_z)`, in the larger-rank-first relation. -/
theorem isGeneralSymmetricGammaFactor_unramifiedTest (z : ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V) {G : RationalFunctions}
    (h : IsGeneralSymmetricGammaFactor q ψ abv ν π (rankOneCharacter (1 : Fˣ →* ℂˣ)) G) :
    IsGeneralSymmetricGammaFactor q ψ abv ν π
      (rankOneCharacter (Conductor.UnramifiedPrincipalSeries.character hϖ z))
      (rationalRescale z G) := by
  have h' := (isGeneralSymmetricGammaFactor_unramifiedTwist hq hϖ habv hunit z π _ h).1
  rwa [unramifiedDetTwist, HighlyRamified.twist_rankOneCharacter_one] at h'

include hq hϖ habv hunit in
/-- The unramified test for the pair relation, which for the rank-one test is the
larger-rank-first relation. -/
theorem isGeneralPairGammaFactor_unramifiedTest (z : ℂˣ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V) {G : RationalFunctions}
    (h : IsGeneralPairGammaFactor q ψ abv ν π (rankOneCharacter (1 : Fˣ →* ℂˣ)) G) :
    IsGeneralPairGammaFactor q ψ abv ν π
      (rankOneCharacter (Conductor.UnramifiedPrincipalSeries.character hϖ z))
      (rationalRescale z G) := by
  have h' := (isGeneralPairGammaFactor_unramifiedTwist hq hϖ habv hunit z π _ h).1
  rwa [unramifiedDetTwist, HighlyRamified.twist_rankOneCharacter_one] at h'

end LocalField

end Langlands.RankinSelberg
