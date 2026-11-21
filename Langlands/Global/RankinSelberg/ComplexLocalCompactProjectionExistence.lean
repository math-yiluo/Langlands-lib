import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar

/-! # Compact projections of translated complex inducing vectors -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open scoped BigOperators Manifold ContDiff Matrix.Norms.Operator
open scoped Langlands.Archimedean.ComplexDuality

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ComplexPrincipalSeriesExtension ComplexGramFormula

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ

private def unitaryInCompact : U →* Kc :=
  Unitary.toUnits.codRestrict (unitaryCompact ℂ n) (fun k => k.2)

private theorem unitaryInCompact_val (x : U) : (unitaryInCompact x).val = Unitary.toUnits x :=
  rfl

private theorem continuous_toUnits_compact :
    Continuous (Unitary.toUnits : U → G) :=
  continuous_unitary_toUnits

variable (n) in
/-- The compact convolutions of all right translates of an inducing vector are
the restrictions of K-finite vectors of the same complex principal series. -/
def ComplexLocalCompactProjectionExistsStatement : Prop :=
  ∀ (ds : List ComplexCharacterData) (μ : Measure Kc), μ.IsHaarMeasure →
  ∀ (κ : Kc → ℂ), Continuous κ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : Kc => fun k => κ (h⁻¹ * k))) →
  ∀ (f : complexStandardKFinite n ds),
    ∃ p : G → complexStandardKFinite n ds, ∀ (g : G) (x : Kc),
      (p g : G → ℂ) x.val = ∫ k, κ k * (f : G → ℂ) (x.val * k.val * g) ∂μ

set_option backward.isDefEq.respectTransparency false in
theorem complexLocalCompactProjectionExists : ComplexLocalCompactProjectionExistsStatement n := by
  intro ds μ hμ κ hκ hκfin f
  let : μ.IsHaarMeasure := hμ
  obtain ⟨m, α, β, hβ, hExp⟩ := hasFiniteCompactConvolutionKernel_of_finite_translates κ hκ hκfin
  let F : G → ℂ := f
  let χ := complexPositionCharacter ds
  have hf := (mem_principalSeries_iff ℂ n χ F).mp f.2.1
  have hFc : Continuous F := hf.1.continuous
  have hex (g : G) : ∃ v : complexStandardKFinite n ds, ∀ x : Kc,
      (v : G → ℂ) x.val = ∫ k, κ k * F (x.val * k.val * g) ∂μ := by
    let φ (x : U) := ∫ k : Kc, κ k * F (Unitary.toUnits x * k.val * g) ∂μ
    have hφc : Continuous φ := by
      have hpart : Continuous (fun p : U × Kc => κ p.2 * F (Unitary.toUnits p.1 * p.2.val * g)) :=
        (hκ.comp continuous_snd).mul (hFc.comp
          (((continuous_toUnits_compact.comp continuous_fst).mul
            (continuous_subtype_val.comp continuous_snd)).mul continuous_const))
      simpa only [Measure.restrict_univ, φ] using
        (continuous_parametric_integral_of_continuous (μ := μ) hpart isCompact_univ)
    let φb (j : Fin m) (x : U) := ∫ k : Kc, β j k * F (Unitary.toUnits x * k.val * g) ∂μ
    have hShift (h x : U) : φ (x * h) =
        ∫ k : Kc, κ ((unitaryInCompact h)⁻¹ * k) * F (Unitary.toUnits x * k.val * g) ∂μ := by
      let T (k : Kc) := κ ((unitaryInCompact h)⁻¹ * k) * F (Unitary.toUnits x * k.val * g)
      rw [← integral_mul_left_eq_self T (unitaryInCompact h)]
      simp only [T, φ, inv_mul_cancel_left, map_mul, Subgroup.coe_mul, unitaryInCompact_val, mul_assoc]
    have hφfin : FiniteDimensional ℂ
        (Submodule.span ℂ (Set.range fun h : U => fun x => φ (x * h))) := by
      let : FiniteDimensional ℂ (Submodule.span ℂ (Set.range φb)) :=
        FiniteDimensional.span_of_finite ℂ (Set.finite_range φb)
      apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range φb))
      apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      have heq : (fun x => φ (x * h)) = ∑ j, α j (unitaryInCompact h) • φb j := by
        funext x
        rw [hShift]
        simp_rw [hExp, Finset.sum_mul]
        rw [integral_finsetSum]
        · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, φb]
          exact Finset.sum_congr rfl fun j _ => by simp only [mul_assoc, integral_const_mul]
        · intro j _
          exact ((continuous_const.mul (hβ j)).mul (hFc.comp
            ((continuous_const.mul continuous_subtype_val).mul continuous_const))).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
      change (fun x : U => φ (x * h)) ∈ Submodule.span ℂ (Set.range φb)
      rw [heq]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hφM (a : Fin n → ℂˣ) (x : U) :
        φ (phaseMatrix a * x) =
          principalSeriesCharacter ℂ n χ (fun i => phaseUnit (a i)) * φ x := by
      let b := fun i => phaseUnit (a i)
      have hdiag : Unitary.toUnits (phaseMatrix a) =
          (GeneralLinear.Iwasawa.diagonalUnits b : G) := Units.ext rfl
      have hF (y : G) : F ((GeneralLinear.Iwasawa.diagonalUnits b : G) * y) =
          principalSeriesCharacter ℂ n χ b * F y := by
        simpa only [OneMemClass.coe_one, mul_one] using hf.2 b 1 y
      simp only [φ, map_mul, hdiag, mul_assoc, hF]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => mul_left_comm _ _ _
    obtain ⟨v, hv, hvφ⟩ := complexPrincipalSeriesExtension n ds φ hφc hφfin hφM
    refine ⟨⟨v, hv⟩, fun x => ?_⟩
    let xU : U := ⟨x.val.val, x.2⟩
    have hx : Unitary.toUnits xU = x.val := Units.ext rfl
    change v x.val = _
    calc
      v x.val = φ xU := hx ▸ hvφ xU
      _ = _ := by simp only [φ, hx]
  choose p hp using hex
  exact ⟨p, hp⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
