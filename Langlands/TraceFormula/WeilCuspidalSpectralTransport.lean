import Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneProof
import Langlands.Automorphic.GeneralLinearFullAEL2CuspidalCompactnessProof
import Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport

/-! # Compactness and multiplicity one for the Weil cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj CompactlySupported NNReal ENNReal

namespace Langlands.TraceFormula

open Langlands.Global AdelicGroupPoints AdelicWeilRestriction PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis
open Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport
open WeilGeneralLinearCuspidalTransport AdelicGroupAutomorphism

private theorem compact_of_haar_intertwining
    {A B X Y : Type*}
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (a : B ≃ₜ* A) (U : X ≃L[ℂ] Y)
    (ρ : A → X →L[ℂ] X) (π : B → Y →L[ℂ] Y)
    (hU : ∀ b x, U (ρ (a b) x) = π b (U x))
    (mA : Measure A) [mA.IsHaarMeasure] [mA.Regular]
    (mB : Measure B) [mB.IsHaarMeasure] [mB.Regular]
    (f : B → ℂ) (R : X →L[ℂ] X) (T : Y →L[ℂ] Y)
    (hR : ∀ x, R x = ∫ t, f (a.symm t) • ρ t x ∂mA)
    (hT : ∀ y, T y = ∫ t, f t • π t y ∂mB)
    (hCompact : IsCompactOperator R) : IsCompactOperator T := by
  let : (Measure.map a mB).IsHaarMeasure := a.isHaarMeasure_map mB
  let : (Measure.map a mB).Regular := Measure.Regular.map a.toHomeomorph
  let c : ℝ≥0∞ := haarScalarFactor (Measure.map a mB) mA
  have hm : MeasurePreserving a mB (c • mA) :=
    ⟨a.continuous.measurable, isMulLeftInvariant_eq_smul_of_regular (Measure.map a mB) mA⟩
  have hEq : T = c.toReal •
      (U.toContinuousLinearMap ∘L R ∘L U.symm.toContinuousLinearMap) := by
    ext y : 1
    obtain ⟨x, rfl⟩ := U.surjective y
    change T (U x) = c.toReal • U (R (U.symm (U x)))
    rw [U.symm_apply_apply, hT, hR]
    calc
      (∫ b, f b • π b (U x) ∂mB) =
          ∫ b, U (f (a.symm (a b)) • ρ (a b) x) ∂mB := by
        apply integral_congr_ae
        filter_upwards with b
        rw [map_smul, a.symm_apply_apply, hU]
      _ = ∫ t, U (f (a.symm t) • ρ t x) ∂c • mA :=
        hm.integral_comp a.toHomeomorph.toMeasurableEquiv.measurableEmbedding
          (fun t : A => U (f (a.symm t) • ρ t x))
      _ = c.toReal • U (∫ t, f (a.symm t) • ρ t x ∂mA) := by
        rw [integral_smul_measure, U.integral_comp_comm]
  rw [hEq]
  exact ((hCompact.comp_clm U.symm.toContinuousLinearMap).clm_comp U.toContinuousLinearMap).smul _

private def hasMultiplicityOne {A X : Type*} [Monoid A] [NormedAddCommGroup X] [NormedSpace ℂ X]
    (ρ : A →* (X →L[ℂ] X)) : Prop :=
  ∀ P Q : Submodule ℂ X, IsIrreducibleClosedSummand ρ P →
    IsIrreducibleClosedSummand ρ Q →
    ∀ (hPi : ∀ g x, x ∈ P → ρ g x ∈ P) (V : P ≃ₗᵢ[ℂ] Q),
      (∀ g (x : P), (V ⟨ρ g x, hPi g x x.2⟩ : X) = ρ g (V x)) → P = Q

private theorem multiplicityOne_of_intertwining
    {A B X Y : Type*} [Monoid A] [Monoid B]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (ρ : A →* (X →L[ℂ] X)) (τ : B →* (Y →L[ℂ] Y))
    (a : B ≃ A) (U : X ≃L[ℂ] Y)
    (hU : ∀ b x, U (ρ (a b) x) = τ b (U x))
    {d : ℝ} (hd : d ≠ 0) (hNorm : ∀ x, ‖U x‖ = d * ‖x‖)
    (hOne : hasMultiplicityOne ρ) : hasMultiplicityOne τ := by
  intro P Q hP hQ hPi V hV
  have hForward (g : A) (x : X) : U (ρ g x) = τ (a.symm g) (U x) := by
    simpa only [a.apply_symm_apply] using hU (a.symm g) x
  have hBack (g : A) (y : Y) : U.symm (τ (a.symm g) y) = ρ g (U.symm y) := by
    apply U.injective
    rw [U.apply_symm_apply, hForward, U.apply_symm_apply]
  let P' := P.comap U.toLinearMap
  let Q' := Q.comap U.toLinearMap
  have hP' : IsIrreducibleClosedSummand ρ P' :=
    hP.comap_symm_of_intertwining U.symm a.symm a.symm.surjective hBack
  have hQ' : IsIrreducibleClosedSummand ρ Q' :=
    hQ.comap_symm_of_intertwining U.symm a.symm a.symm.surjective hBack
  let uP : P' ≃ₗ[ℂ] P := U.toLinearEquiv.ofSubmodule' P
  let uQ : Q' ≃ₗ[ℂ] Q := U.toLinearEquiv.ofSubmodule' Q
  let V' : P' ≃ₗᵢ[ℂ] Q' :=
    { toLinearEquiv := uP.trans (V.toLinearEquiv.trans uQ.symm)
      norm_map' := fun x => by
        apply mul_left_cancel₀ hd
        change d * ‖U.symm (V (uP x) : Y)‖ = d * ‖(x : X)‖
        rw [← hNorm, ← hNorm]
        rw [U.apply_symm_apply]
        exact V.norm_map (uP x) }
  have hImage (x : P') : U (V' x : X) = (V (uP x) : Y) :=
    U.apply_symm_apply _
  apply Submodule.comap_injective_of_surjective (f := U.toLinearMap) U.surjective
  apply hOne P' Q' hP' hQ' hP'.2.2.1 V'
  intro g x
  apply U.injective
  rw [hImage, hForward, hImage]
  have hArg : uP ⟨ρ g x, hP'.2.2.1 g x x.2⟩ =
      ⟨τ (a.symm g) (uP x), hPi (a.symm g) (uP x) (uP x).2⟩ :=
    Subtype.ext (hForward g x)
  rw [hArg]
  exact hV (a.symm g) (uP x)

private theorem norm_L2_of_ae_pullback
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mX : Measure X} {mY : Measure Y} {c : ℝ≥0∞}
    (a : X → Y) (ha : MeasurePreserving a mX (c • mY)) (hc : c ≠ ∞)
    (x : Lp ℂ 2 mX) (y : Lp ℂ 2 mY) (h : x =ᵐ[mX] y ∘ a) :
    ‖x‖ = c.toReal ^ (2 : ℝ≥0∞).toReal⁻¹ * ‖y‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae h,
    eLpNorm_comp_measurePreserving ((Lp.memLp y).smul_measure hc).aestronglyMeasurable ha,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num) c,
    Lp.norm_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    one_div, ENNReal.toReal_inv]

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

set_option hygiene false in
local notation "GLL" => GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L)

set_option hygiene false in
local notation "W" => weilGroup K L (GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K))

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

section Transport

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of L))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {H : GroupScheme (Spec (CommRingCat.of K))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (w : H ≅ AffineWeil.groupScheme K L G)
  {T : CommGroupScheme (Spec (CommRingCat.of K))} {i : T.toGrp ⟶ H}
  {Z : CommGroupScheme (Spec (CommRingCat.of L))} {j : Z.toGrp ⟶ G}
  (hw : (imageSubgroup K T H i).map (ambientEquiv K L w).toMonoidHom = imageSubgroup L Z G j)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
  (hj : Function.Injective (characterRestrict j)) [(characterRestrict j).range.FiniteIndex]
  (J : Type u) [Fintype J] (ez : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of L)) J) (hz : IsCentral j)
  (hPD : ParabolicDynamicStatement.{u}) (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
  [(Measure.haar : Measure (normOneSubgroup K H)).IsMulRightInvariant]
  [(Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant]

local notation "SK" => fullAEL2CuspidalSubmodule K H hPD hH T i hi I e hc
local notation "SL" => fullAEL2CuspidalSubmodule L G hPD hG Z j hj J ez hz
local notation "πK" => fullAEL2CuspidalBoundedRightAction K H hPD hH T i hi I e hc
local notation "πL" => fullAEL2CuspidalBoundedRightAction L G hPD hG Z j hj J ez hz
local notation "RK" => fullAEL2CuspidalIntegratedAction K H hPD hH T i hi I e hc Measure.haar
local notation "RL" => fullAEL2CuspidalIntegratedAction L G hPD hG Z j hj J ez hz Measure.haar

include hw in
private theorem compactness_transport
    (hCompact : ∀ (g : C_c(AdelicGroupPoints L G, ℂ)) (hg : Integrable g Measure.haar),
      IsCompactOperator (RL g hg))
    (f : C_c(AdelicGroupPoints K H, ℂ)) (hf : Integrable f Measure.haar) :
    IsCompactOperator (RK f hf) := by
  let a := ambientEquiv K L w
  let U := cuspidalEquiv K L w hw hi I e hc hj J ez hz hPD hH hG
  let g : C_c(AdelicGroupPoints L G, ℂ) :=
    ⟨⟨f ∘ a.symm, f.continuous.comp a.symm.continuous⟩,
      f.hasCompactSupport.comp_homeomorph a.toHomeomorph.symm⟩
  have hg : Integrable g Measure.haar :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  exact compact_of_haar_intertwining a U (⇑(πL)) (⇑(πK))
    (cuspidalEquiv_rightAction K L w hw hi I e hc hj J ez hz hPD hH hG)
    Measure.haar Measure.haar (⇑f) (RL g hg) (RK f hf)
    (fun _ => rfl) (fun _ => rfl) (hCompact g hg)

include hw in
private theorem multiplicityOne_transport
    (hOne : hasMultiplicityOne (πL)) : hasMultiplicityOne (πK) := by
  let U := cuspidalEquiv K L w hw hi I e hc hj J ez hz hPD hH hG
  let c : ℝ≥0∞ := normOneHaarFactor K L w
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hc0 : c ≠ 0 := ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne'
  let d := c.toReal ^ (2 : ℝ≥0∞).toReal⁻¹
  have hd : d ≠ 0 := (Real.rpow_pos_of_pos (ENNReal.toReal_pos hc0 hct) _).ne'
  have hNorm (x : SL) : ‖U x‖ = d * ‖x‖ := by
    change ‖(U x).val‖ = d * ‖x.val‖
    exact norm_L2_of_ae_pullback _
      ⟨(quotientMeasurableEquiv K L w hw hi I e hc hj J ez hz).measurable,
        map_positiveQuotientHaar K L w hi e hj ez hw hc hz⟩ hct _ _
      (coeFn_cuspidalEquiv K L w hw hi I e hc hj J ez hz hPD hH hG x)
  exact multiplicityOne_of_intertwining (πL) (πK) (ambientEquiv K L w).toEquiv U
    (cuspidalEquiv_rightAction K L w hw hi I e hc hj J ez hz hPD hH hG) hd hNorm hOne

end Transport

set_option linter.unusedVariables false in
/-- Compactness and multiplicity one on the actual cuspidal Hilbert space of the
Weil restriction of `GL_{r+1}` with the given positive rational quotient. -/
def WeilCuspidalSpectralTransportStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive W)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ W)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex] (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K W)).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule K W hPD hW T i hi I e hc
    let π : AdelicGroupPoints K W →* (S →L[ℂ] S) :=
      fullAEL2CuspidalBoundedRightAction K W hPD hW T i hi I e hc
    (∀ (f : C_c(AdelicGroupPoints K W, ℂ)) (hf : Integrable f Measure.haar),
      IsCompactOperator (fullAEL2CuspidalIntegratedAction K W hPD hW T i hi I e hc
        Measure.haar f hf)) ∧
    hasMultiplicityOne π

set_option maxHeartbeats 6000000 in
theorem weilCuspidalSpectralTransport : WeilCuspidalSpectralTransportStatement.{u} := by
  unfold WeilCuspidalSpectralTransportStatement
  intro K fK nK L fL nL alg fin r hPD hW T i hi hIndexK I finI e hc hHaarK
  dsimp only
  let G := GLL
  let hG := isConnectedReductive_generalLinear L (Fin (r + 1))
  let Z := Gm (Spec (CommRingCat.of L))
  let z := GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of L)
  let hj := scalarCharacter_injective L r
  let hc' := scalar_isCentral L r
  let ez := splitTorus.gmIso (Spec (CommRingCat.of L))
  let : (characterRestrict z).range.FiniteIndex := scalarCharacter_finiteIndex L r
  let w := weilIso K L r
  let hw := map_positiveImage K L r T i hi I e hc
  let : (Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant :=
    normOneHaar_rightInvariant K L w
  have hCompact := generalLinearFullAEL2CuspidalCompactness L (r + 1) hPD hG Z z hj PUnit ez hc'
  constructor
  · exact compactness_transport K L w hw hi I e hc hj PUnit ez hc' hPD hW hG hCompact
  · refine multiplicityOne_transport K L w hw hi I e hc hj PUnit ez hc' hPD hW hG ?_
    exact generalLinearCuspidalMultiplicityOne L (r + 1) hPD Z z hj PUnit ez hc'

end Langlands.TraceFormula
