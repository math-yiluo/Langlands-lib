import Langlands.Global.AdelicIwasawaCuspidalRestriction
import Langlands.Global.AdelicHarishChandraDirectionalGrowth
import Langlands.Global.AdelicLocalFinitenessBoundaryLogBounds
import Langlands.Global.AdelicLocalFinitenessChamberWeights

/-! # Compact Harish-Chandra restrictions on polynomial boundary slabs -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj NNReal ENNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.Analysis.OperatorIdeals Langlands.GroupScheme AdelicGroupPoints
  AdelicSiegelFactors PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ 𝓕.T)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))
  (hcalc : AdelicDifferentialCommutator F G hG) (hN : 0 < N) (hrho : IsClosedSubgroup rho)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "P₀" => Standard.parabolicScheme 𝓕.i 𝓕.ν ∅
local notation "p₀" => Standard.parabolicHom 𝓕.i 𝓕.ν ∅
local notation "t₀" => torusToStandardParabolic F G 𝓕.T 𝓕.i 𝓕.ν
local notation "Z" => WeightedSiegel.DomainQuotient F p₀
local notation "V" => RealCharacterDual F 𝓕.T.toGrp
local notation "H₀" => RealCharacterDual F P₀
local notation "Growth[" R "," L "]" => UniformGrowthFrechetSpace F G rho hG hcalc hN hrho R L
local notation "value[" R "," L "]" => UniformGrowthFrechetSpace.toFun F G rho hG hcalc hN hrho R L

private instance : IsClosedImmersion (p₀).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom 𝓕.i 𝓕.ν ∅

private instance : IsAffine (P₀).X.left := isAffine_of_isAffineHom (p₀).hom.hom.left

/-- With the given Iwasawa compact and sufficiently large root and central
rates, a smooth Fréchet family has compact Harish-Chandra restrictions on
any measurable subset of the corresponding boundary slab. -/
def AdelicHarishChandraBoundaryCompactStatement [Fintype Δ] {r : ℕ}
    (dT : V ≃L[ℝ] H₀) (e : H₀ ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ))) (step : Δ → ℝ) : Prop :=
  IsConnectedReductive G → IsSiegelAlgebraicSetup F G 𝓕.T 𝓕.i 𝓕.ν T₀ j →
  (∀ h, dT h = realCharacterDualMap F 𝓕.T.toGrp P₀ t₀ h) →
  (∀ α, 0 < step α) →
  (∀ (h : V) (α : Δ), (e (dT h)).1 α = h α.val / step α) →
  (∀ h : V, (e (dT h)).2 = 0 → realCharacterDualMap F 𝓕.T.toGrp G 𝓕.i h = 0) →
  ∀ (K : Subgroup A) (hK : IsIwasawaCompact p₀ K), ∃ c : ℝ, 0 < c ∧
  ∀ (aRoot : Δ → ℝ) (aCent : Fin r → ℝ), (∀ α, c ≤ aRoot α) → (∀ k, c ≤ aCent k) →
  ∀ (P : Finset (characterLattice 𝓕.T)) (τ κ : Δ → ℝ) (m : Fin r → ℝ),
  ∀ (S : Set Z), MeasurableSet S →
    (∀ z ∈ S, let x := e (WeightedSiegel.domainHeight F p₀ hK z)
      (∀ α : Δ, τ α ≤ x.1 α) ∧ (∀ α : Δ, α.val ∉ P → x.1 α ≤ κ α) ∧
        (∀ k, |x.2 k| ≤ m k)) →
  ∀ (R : ℝ), 0 ≤ R → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (smooth : E →L[ℂ] Growth[R,L]),
    let ell := localFinitenessLogWeight aRoot aCent ∘ e
    let measure := WeightedSiegel.domainMeasure F p₀ hK ell S
    ∃ T : E →L[ℂ] Lp ℂ 2 measure, IsHilbertSchmidt T ∧ IsCompactOperator T ∧
      ∀ q, (T q : Z → ℂ) =ᵐ[measure] fun z => 𝓕.hcComponent P (value[R,L] (smooth q)) (Quotient.out z)

theorem adelicHarishChandraBoundaryCompact [Fintype Δ] {r : ℕ}
    (dT : V ≃L[ℝ] H₀) (e : H₀ ≃L[ℝ] ((Δ → ℝ) × (Fin r → ℝ))) (step : Δ → ℝ) :
    AdelicHarishChandraBoundaryCompactStatement.{u, v} 𝓕 j hG rho hcalc hN hrho dT e step := by
  intro hRed hsetup hd hstep hRoot hCen K hK
  obtain ⟨I, hI, ⟨eI⟩⟩ := hsetup.1.isSplitSubtorus.1
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨a, c, -, hc, hlog, hCompact⟩ := adelicIwasawaCuspidalRestriction 𝓕 j I eI hG rho hsetup hN K hK
  let f := dT.trans e
  obtain ⟨Zχ, -, hSpan, hBounds⟩ := adelicLocalFinitenessBoundaryLogBounds F 𝓕.i 𝓕.ν f step
    hRed hsetup.1 hsetup.2.1 hstep hRoot hCen
  let J : ((Δ → ℝ) × (Fin r → ℝ)) →L[ℝ] (I → ℝ) :=
    (e.symm.trans (dT.symm.trans (dualCoordinatesContinuousEquiv F 𝓕.T I eI))).toContinuousLinearMap
  have hdlog (H : H₀) : dT (characterLog F 𝓕.T.toGrp (a H).val) = H := by
    rw [hd, ← characterLog_map]
    exact hlog H
  have hJ (H : H₀) : positiveLogCoordinates F I eI (a H) = J (e H) := by
    change dualCoordinatesContinuousEquiv F 𝓕.T I eI (characterLog F 𝓕.T.toGrp (a H).val) =
      dualCoordinatesContinuousEquiv F 𝓕.T I eI (dT.symm (e.symm (e H)))
    rw [e.symm_apply_apply, ← dT.symm_apply_apply (characterLog F 𝓕.T.toGrp (a H).val), hdlog]
  let rate := max 1 (c * ‖J‖)
  refine ⟨rate, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro ar ac har hac P τ κ m S hS hSlab R hR L hL E _ _ _ smooth
  let ell := localFinitenessLogWeight ar ac ∘ e
  let H := WeightedSiegel.domainHeight F p₀ hK
  let D : ℝ := ∑ α, 2 * ar α * |τ α|
  have hWeight (z : Z) (hz : z ∈ S) :
      c * ‖positiveLogCoordinates F I eI (a (H z))‖ ≤ 2 * ell (H z) + 2 * D := by
    have h₁ := J.le_opNorm (e (H z))
    have h₂ := localFinitenessLogWeight_norm_le ar τ ac
      (mul_nonneg hc.le (norm_nonneg J)) (fun α => (le_max_right _ _).trans (har α))
      (fun k => (le_max_right _ _).trans (hac k)) (e (H z)) (hSlab z hz).1
    have h : c * ‖positiveLogCoordinates F I eI (a (H z))‖ ≤ ell (H z) + D := by
      rw [hJ]
      exact (mul_le_mul_of_nonneg_left h₁ hc.le).trans (by rwa [← mul_assoc])
    have h₀ : 0 ≤ c * ‖positiveLogCoordinates F I eI (a (H z))‖ := mul_nonneg hc.le (norm_nonneg _)
    linarith
  obtain ⟨bLog, B, hB, hBounds⟩ := hBounds (𝓕.finsetIndex P).val τ κ m
  let b₀ : ℝ≥0 := ⟨Real.exp bLog, (Real.exp_pos _).le⟩
  let b := Units.mk0 b₀ (fun hb => Real.exp_ne_zero bLog (congrArg (fun x : ℝ≥0 => (x : ℝ)) hb))
  have hBoundary (z : Z) (hz : z ∈ S) :
      let a₀ := a (H z)
      (∀ α ∈ Δ, b ≤ normCharacter F 𝓕.T α a₀) ∧
      (∀ χ ∈ Zχ, |logNormHom F 𝓕.T a₀.val χ| ≤ B) ∧
      (∀ α ∈ Δ \ (𝓕.finsetIndex P).val, |logNormHom F 𝓕.T a₀.val α| ≤ B) := by
    let a₀ := a (H z)
    let h := characterLog F 𝓕.T.toGrp a₀.val
    have he : e (H z) = f h := by change e (H z) = e (dT h); rw [hdlog]
    have hSl := hSlab z hz
    have hUpper (α : Δ) (hα : α.val ∉ (𝓕.finsetIndex P).val) : (e (H z)).1 α ≤ κ α :=
      hSl.2.1 α (fun hmem => hα ⟨hmem, α.property⟩)
    obtain ⟨hLo, hAux, hOther⟩ := hBounds h (e (H z)) he hSl.1 hUpper hSl.2.2
    refine ⟨?_, hAux, hOther⟩
    intro α hα
    apply NNReal.coe_le_coe.mp
    change Real.exp bLog ≤ ((normCharacter F 𝓕.T α a₀ : ℝ≥0) : ℝ)
    have hp : 0 < ((normCharacter F 𝓕.T α a₀ : ℝ≥0) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (normCharacter F 𝓕.T α a₀).ne_zero)
    have hl : h α = Real.log ((normCharacter F 𝓕.T α a₀ : ℝ≥0) : ℝ) := rfl
    simpa only [hl, Real.exp_log hp] using Real.exp_le_exp.mpr (hLo α hα)
  obtain ⟨ev, hev, hcont, hsm, hrat, hU, hRight, hCusp, hGrow⟩ :=
    adelicHarishChandraDirectionalGrowth 𝓕 hG rho hcalc hN hrho R L hR hL E smooth P
  obtain ⟨T, hHS, hT, hTae⟩ := hCompact (𝓕.finsetIndex P) Zχ hSpan b B hB ell S hS (2 * D)
    hWeight hBoundary L hL E ev hcont hsm hrat hU hRight hCusp R hR hGrow
  refine ⟨T, hHS, hT, fun q => (hTae q).trans (ae_of_all _ fun z => ?_)⟩
  exact congrFun (hev q) (Quotient.out z)

end Langlands.Global.StandardParabolicFamily
