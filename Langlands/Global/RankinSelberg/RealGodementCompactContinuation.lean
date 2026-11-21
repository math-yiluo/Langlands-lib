import Langlands.Global.RankinSelberg.RealGodementCompactFrame
import Langlands.Global.RankinSelberg.RealGodementHolomorphicForms
import Langlands.Global.RankinSelberg.RealGodementSectionAnalytic
import Langlands.Global.RankinSelberg.RealGodementSmoothLeading
import Mathlib.LinearAlgebra.Determinant

/-! # Entire continuation of the real Jacquet coefficient on a fixed compact space -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula PartialJacquet PrincipalSeriesExtension RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "K" => unitaryCompact ℝ (t + 2)
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "P(" t "," p "," ds "," z ")" =>
  principalSeries ℝ (t + 2) (realPositionCharacter (RealBlock.character (charData p z) :: ds))

private theorem differentiable_compact_coordinates {B : Type*} {n : ℕ} (E : Submodule ℂ (B → ℂ))
    [FiniteDimensional ℂ E] (e : E →ₗ[ℂ] (Fin n → ℂ)) (f : ℂ → E)
    (hf : ∀ b : B, Differentiable ℂ (fun z => (f z).val b)) (j : Fin n) :
    Differentiable ℂ (fun z => e (f z) j) := by
  obtain ⟨S, _, hS⟩ := FiniteFunctionSpaces.exists_finset_eval_injective (Module.finrank ℂ E) E rfl
  let T : E →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun s => (LinearMap.proj s.val).comp E.subtype
  have hT : T.ker = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun x hx => ?_
    apply Subtype.ext
    exact hS x.val x.property fun b hb => congrFun hx ⟨b, hb⟩
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  let C := ((LinearMap.proj j).comp (e.comp L)).toContinuousLinearMap
  have hDiff : Differentiable ℂ (fun z => T (f z)) := differentiable_pi.mpr (fun s => hf s.val)
  have hEq : (fun z => C (T (f z))) = fun z => e (f z) j :=
    funext fun z => congrArg (fun q : E => e q j) (LinearMap.congr_fun hL (f z))
  rw [← hEq]
  exact C.differentiable.comp hDiff

private theorem exists_det_ne_zero_of_spanning {E ι : Type*} {n : ℕ} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (e : E ≃ₗ[ℂ] (Fin n → ℂ)) (v : ι → E)
    (hv : Submodule.span ℂ (Set.range v) = ⊤) :
    ∃ b : Fin n → ι, (Matrix.of fun i j => e (v (b j)) i).det ≠ 0 := by
  classical
  let S : Set E := (linearIndepOn_empty ℂ (id : E → E)).extend (empty_subset (Set.range v))
  let B : Module.Basis S ℂ E := Module.Basis.ofSpan hv.ge
  let : Finite S := Module.Finite.finite_basis B
  let : Fintype S := Fintype.ofFinite S
  have hCard := Module.finrank_eq_card_basis B
  have hn : Module.finrank ℂ E = n := e.finrank_eq.trans (Module.finrank_fin_fun ℂ)
  let η : S ≃ Fin n := Fintype.equivOfCardEq (hCard.symm.trans (hn.trans (Fintype.card_fin n).symm))
  let Q := B.reindex η
  have hRange (i : Fin n) : ∃ x : ι, v x = Q i := by
    change (B.reindex η) i ∈ Set.range v
    rw [Module.Basis.reindex_apply]
    exact Module.Basis.ofSpan_subset hv.ge (Set.mem_range_self (η.symm i))
  choose b hb using hRange
  refine ⟨b, ?_⟩
  have hMatrix : (Matrix.of fun i j => e (v (b j)) i) = LinearMap.toMatrix Q (Pi.basisFun ℂ (Fin n)) e.toLinearMap := by
    ext i j
    simp only [Matrix.of_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, Pi.basisFun_repr, hb]
  rw [hMatrix]
  exact (e.isUnit_det Q (Pi.basisFun ℂ (Fin n))).ne_zero

private def compactFrameLift (p : Fin 2) (ds : List RealBlock) (W : Submodule ℂ (K → ℂ)) (z : ℂ) :
    compactFrameSpace p ds W →ₗ[ℂ] P(t, p, ds, z) := by
  let R : compactFrameSpace p ds W →ₗ[ℂ] (Matrix.unitaryGroup (Fin (t + 2)) ℝ → ℂ) :=
    LinearMap.pi fun k => (LinearMap.proj (⟨Unitary.toUnits k, k.property⟩ : K)).comp
      (compactFrameSpace p ds W).subtype
  let s := shiftedExponent (t + 2) (realPositionExponent (.character (charData p z) :: ds))
  refine ((extensionLinear s).comp R).codRestrict _ fun x => ?_
  obtain ⟨_, F, hF, hEq⟩ := (mem_compactFrameSpace_iff z).mp x.property
  have he : R x = fun k => F (Unitary.toUnits k) :=
    funext fun k => (congrFun hEq (⟨Unitary.toUnits k, k.property⟩ : K)).symm
  change extension s (R x) ∈ _
  rw [he]
  exact compactPictureExtension_mem_principalSeries hF (fun _ _ => rfl)

private theorem compactSectionRestriction_lift (p : Fin 2) (ds : List RealBlock)
    (W : Submodule ℂ (K → ℂ)) (z : ℂ) (x : compactFrameSpace p ds W) :
    compactSectionRestriction ((compactFrameLift p ds W z x).val) = x.val := by
  funext k
  let κ : Matrix.unitaryGroup (Fin (t + 2)) ℝ := ⟨k.val.val, k.property⟩
  have hk : Unitary.toUnits κ = k.val := Units.ext rfl
  change extension _ _ k.val = x.val k
  rw [← hk, extension_unitary]
  exact congrArg x.val (Subtype.ext hk)

/-- Regard the smooth full-row-rank test of a compact family as a Schwartz map. -/
def CompactSectionFamily.schwartzTest {D : RealQuotientMeasureData t} {p : Fin 2} {ds : List RealBlock}
    {W : Submodule ℂ (K → ℂ)} (C : CompactSectionFamily D.groupHaar p ds W) : 𝓢(X, ℂ) := by
  have hSupport : HasCompactSupport C.test :=
    C.support_compact.of_isClosed_subset isClosed_closure
      (closure_minimal (fun _ hx => by_contra fun h => hx (C.test_zero _ h)) C.support_compact.isClosed)
  exact hSupport.toSchwartzMap C.test_smooth

/-- The Jacquet coefficient has entire linear forms on the fixed compact spaces.
They give the full set of compact-column values and reproduce the open-cell
integral in the dominant half-plane. -/
def RealGodementCompactContinuationStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (ds : List RealBlock),
    IsStrictlyDominant (realPositionExponent ds) t →
    ∀ (W : Submodule ℂ (unitaryCompact ℝ (t + 2) → ℂ)) [FiniteDimensional ℂ W],
    (∀ f ∈ W, ∀ q : unitaryCompact ℝ (t + 2), (fun k : unitaryCompact ℝ (t + 2) => f (q * k)) ∈ W) →
    ∀ (g : Langlands.GeneralLinear (t + 2) ℝ),
    ∃ L : ℂ → Module.Dual ℂ (compactFrameSpace p ds W),
      (∀ x, Differentiable ℂ (fun z => L z x)) ∧
      (∀ (C : CompactSectionFamily D.groupHaar p ds W) (z : ℂ) (x : compactFrameSpace p ds W),
        x.val = C.column D.groupHaar z →
        L z x = godementLeadingFamily D a C.schwartzTest (additiveJacquetIntegral a C.lower) p g z) ∧
      ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
      ∀ (F : principalSeries ℝ (t + 2) (realPositionCharacter (.character (charData p z) :: ds)))
        (x : compactFrameSpace p ds W),
        x.val = compactSectionRestriction F.val → L z x = additiveJacquetIntegral a F.val g

theorem realGodementCompactContinuation : RealGodementCompactContinuationStatement := by
  intro t D a p ds hDom W _ hW g
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let E := compactFrameSpace p ds W
  let : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  let n := Module.finrank ℂ E
  let e : E ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ E).equivFun
  let ι := CompactSectionFamily μ p ds W
  have hSpan (z : ℂ) : Submodule.span ℂ (Set.range fun C : ι => C.column μ z) = E :=
    realGodementCompactFrame (t + 1) μ p ds W hW z
  have hMem (C : ι) (z : ℂ) : C.column μ z ∈ E :=
    hSpan z ▸ Submodule.subset_span ⟨C, rfl⟩
  let v (C : ι) (z : ℂ) : E := ⟨C.column μ z, hMem C z⟩
  let column (C : ι) (z : ℂ) := e (v C z)
  have hBasis (z : ℂ) : ∃ b : Fin n → ι, (Matrix.of fun i j => column (b j) z i).det ≠ 0 :=
    exists_det_ne_zero_of_spanning e (fun C => v C z)
      ((Submodule.span_range_subtype_eq_top_iff E (fun C => hMem C z)).mpr (hSpan z))
  have hColumn (C : ι) (j : Fin n) : Differentiable ℂ (fun z => column C z j) := by
    apply differentiable_compact_coordinates E e.toLinearMap (v C) _ j
    intro k
    exact realGodementSectionAnalytic (t + 1) μ p C.lower C.lower_mem.1.continuous C.support
      C.support_compact C.support_fullRank C.test C.test_smooth.continuous C.test_zero k.val
  let value (C : ι) := godementLeadingFamily D a C.schwartzTest (additiveJacquetIntegral a C.lower) p g
  have hValue (C : ι) : Differentiable ℂ (value C) ∧
      ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
        value C z = additiveJacquetIntegral a (sectionValue μ (charData p z) C.lower C.test) g := by
    exact realGodementSmoothLeading t D a p ds ⟨C.lower, C.lower_mem⟩ hDom
      C.support C.support_compact C.support_fullRank C.schwartzTest C.test_zero g
  have hDominance (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) :
      IsStrictlyDominant (realPositionExponent (.character (charData p z) :: ds)) (t + 1) := by
    intro j hj
    cases j with
    | zero => exact hz
    | succ j => exact hDom j (Nat.lt_of_succ_lt_succ hj)
  let chamberForm (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) : Module.Dual ℂ E :=
    (LinearMap.proj g).comp ((additiveJacquetLinear a (RealStrictCharacterLanglandsQuotient.isSignedPower _)
      (hDominance z hz)).comp (compactFrameLift p ds W z))
  have hLift (z : ℂ) (x : E) (F : P(t, p, ds, z)) (hx : x.val = compactSectionRestriction F.val) :
      compactFrameLift p ds W z x = F := by
    apply Subtype.ext
    apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries
      (compactFrameLift p ds W z x).property F.property
    exact fun k hk => congrFun ((compactSectionRestriction_lift p ds W z x).trans hx) ⟨k, hk⟩
  have hAgree (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) (C : ι) :
      chamberForm z hz (v C z) = value C z := by
    rw [(hValue C).2 z hz]
    have hSource : sectionValue μ (charData p z) C.lower C.test ∈ P(t, p, ds, z) :=
      realGodementSection (t + 1) μ (charData p z) ds C.lower C.lower_mem C.support C.support_compact
        C.support_fullRank C.test C.test_smooth C.test_zero
    change additiveJacquetIntegral a (compactFrameLift p ds W z (v C z)).val g = _
    rw [hLift z (v C z) ⟨_, hSource⟩ rfl]
  let z₀ : ℂ := ((realPositionExponent ds 0).re + 1 : ℝ)
  have hz₀ : (realPositionExponent ds 0).re < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith
  have hNear : ∀ᶠ z in 𝓝 z₀,
      ∃ L : (Fin n → ℂ) →ₗ[ℂ] ℂ, ∀ C, L (column C z) = value C z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
    exact ⟨(chamberForm z hz).comp e.symm.toLinearMap,
      fun C => by simpa only [column, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply] using hAgree z hz C⟩
  obtain ⟨L, hL, hAnalytic⟩ := realGodementHolomorphicForms n ι column value hColumn
    (fun C => (hValue C).1) hBasis z₀ hNear
  let J := fun z => (L z).comp e.toLinearMap
  refine ⟨J, fun x => hAnalytic (e x), ?_, ?_⟩
  · intro C z x hx
    have he : x = v C z := Subtype.ext hx
    rw [he]
    exact hL z C
  · intro z hz F x hx
    have hAll : J z = chamberForm z hz := by
      have hSpan' : Submodule.span ℂ (Set.range fun C : ι => v C z) = ⊤ :=
        (Submodule.span_range_subtype_eq_top_iff E (fun C => hMem C z)).mpr (hSpan z)
      apply LinearMap.ext_on hSpan'
      rintro _ ⟨C, rfl⟩
      exact (hL z C).trans (hAgree z hz C).symm
    rw [hAll]
    change additiveJacquetIntegral a (compactFrameLift p ds W z x).val g = _
    rw [hLift z x F hx]

/-- A fixed-compact K-finite vector has a unique entire leading-exponent
continuation of each dominant-chamber Jacquet coefficient. -/
theorem existsUnique_leadingJacquetContinuation (t : ℕ) (D : RealQuotientMeasureData t)
    (a : ℝˣ) (p : Fin 2) (ds : List RealBlock) (hDom : IsStrictlyDominant (realPositionExponent ds) t)
    (w : ℂ) (F : Langlands.GeneralLinear (t + 2) ℝ → ℂ)
    (hF : F ∈ kFiniteFunctions P(t, p, ds, w) (unitaryCompact ℝ (t + 2))) (g : Langlands.GeneralLinear (t + 2) ℝ) :
    ∃! A : ℂ → ℂ, Differentiable ℂ A ∧ ∀ z : ℂ, (realPositionExponent ds 0).re < z.re →
      A z = additiveJacquetIntegral a (leadingCompactVector p ds F z) g := by
  obtain ⟨W, _, hFW, hW⟩ := exists_finite_leftStable_of_kFinite hF.2
  obtain ⟨L, hA, _, hChamber⟩ := realGodementCompactContinuation t D a p ds hDom W hW g
  let x : compactFrameSpace p ds W :=
    ⟨compactSectionRestriction F, (mem_compactFrameSpace_iff w).mpr ⟨hFW, F, hF.1, rfl⟩⟩
  let A := fun z => L z x
  have he (z : ℂ) : x.val = compactSectionRestriction (leadingCompactVector p ds F z) :=
    funext fun k => (compactPictureExtension_eqOn _ F k.property).symm
  have hAeq (z : ℂ) (hz : (realPositionExponent ds 0).re < z.re) :
      A z = additiveJacquetIntegral a (leadingCompactVector p ds F z) g :=
    hChamber z hz ⟨_, leadingCompactVector_mem_principalSeries p ds hF.1 z⟩ x (he z)
  refine ⟨A, ⟨hA x, hAeq⟩, fun B hB => ?_⟩
  let z₀ : ℂ := ((realPositionExponent ds 0).re + 1 : ℝ)
  have hz₀ : (realPositionExponent ds 0).re < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith
  have hEq : B =ᶠ[𝓝 z₀] A := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
    exact (hB.2 z hz).trans (hAeq z hz).symm
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hB.1.analyticAt z)
    (fun z _ => (hA x).analyticAt z) hEq

end Langlands.Global.RankinSelbergGlobal.RealGodement
