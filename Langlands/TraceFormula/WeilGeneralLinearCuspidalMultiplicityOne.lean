import Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneProof
import Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport

/-! # Cuspidal multiplicity one under Weil restriction of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.TraceFormula

open Langlands.Analysis Langlands.Global AdelicGroupPoints AdelicWeilRestriction PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport
open WeilGeneralLinearCuspidalTransport AdelicGroupAutomorphism

private theorem norm_l2Equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mX : Measure X} {mY : Measure Y} {c : ℝ≥0∞} (q : X ≃ᵐ Y)
    (hmap : Measure.map q mX = c • mY) (hc : c ≠ 0) (hfinite : c ≠ ∞) (f : Lp ℂ 2 mY) :
    ‖MeasureTransport.l2Equiv q hmap hc hfinite f‖ =
      c.toReal ^ (2 : ℝ≥0∞).toReal⁻¹ * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (MeasureTransport.coeFn_l2Equiv q hmap hc hfinite f),
    eLpNorm_comp_measurePreserving ((Lp.memLp f).smul_measure hfinite).aestronglyMeasurable
      (show MeasurePreserving q mX (c • mY) from ⟨q.measurable, hmap⟩),
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num) c,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_rpow, ← Lp.norm_def,
    one_div, ENNReal.toReal_inv]

private theorem multiplicityOne_of_isometricTransport
    {A B X Y : Type*} [Monoid A] [Monoid B]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {ρX : B →* (X →L[ℂ] X)} {ρY : A →* (Y →L[ℂ] Y)}
    (b : A → B) (hb : Function.Surjective b) (e : X ≃ₗᵢ[ℂ] Y)
    (he : ∀ a x, e (ρX (b a) x) = ρY a (e x))
    (hOne : ∀ P Q, IsIrreducibleClosedSummand ρY P → IsIrreducibleClosedSummand ρY Q →
      ∀ (hP : ∀ a x, x ∈ P → ρY a x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
        (∀ a (x : P), (U ⟨ρY a x, hP a x x.2⟩ : Y) = ρY a (U x)) → P = Q) :
    ∀ P Q, IsIrreducibleClosedSummand ρX P → IsIrreducibleClosedSummand ρX Q →
      ∀ (hP : ∀ a x, x ∈ P → ρX a x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
        (∀ a (x : P), (U ⟨ρX a x, hP a x x.2⟩ : X) = ρX a (U x)) → P = Q := by
  intro P Q hP hQ hPi U hU
  let image (R : Submodule ℂ X) := R.map e.toLinearEquiv.toLinearMap
  have hImage (R : Submodule ℂ X) (hR : IsIrreducibleClosedSummand ρX R) :
      IsIrreducibleClosedSummand ρY (image R) := by
    change IsIrreducibleClosedSummand ρY (R.map e.toLinearEquiv.toLinearMap)
    rw [R.map_equiv_eq_comap_symm e.toLinearEquiv]
    exact hR.comap_symm_of_intertwining e.toContinuousLinearEquiv b hb he
  let eP := e.submoduleMap P
  let eQ := e.submoduleMap Q
  let U' : image P ≃ₗᵢ[ℂ] image Q := (eP.symm.trans U).trans eQ
  have hU' (x : P) : (U' (eP x) : Y) = e (U x : X) := by
    change e (U (eP.symm (eP x)) : X) = _
    rw [eP.symm_apply_apply]
  have hPi' := (hImage P hP).2.2.1
  apply Submodule.map_injective_of_injective e.injective
  refine hOne (image P) (image Q) (hImage P hP) (hImage Q hQ) hPi' U' ?_
  intro a x
  obtain ⟨y, rfl⟩ := eP.surjective x
  have hact : (⟨ρY a (eP y : image P), hPi' a _ (eP y).2⟩ : image P) =
      eP ⟨ρX (b a) y, hPi (b a) y y.2⟩ := by
    apply Subtype.ext
    exact (he a y).symm
  rw [hact, hU', hU (b a), he, hU']

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local notation "Wᵣ(" K ", " L ", " r ")" =>
  weilGroup K L (GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
/-- Isometrically equivalent irreducible closed invariant subspaces of the full cuspidal
`L²` space for `Res_{L/K} GL_{r+1}` coincide. -/
def WeilGeneralLinearCuspidalMultiplicityOneStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hW : IsConnectedReductive Wᵣ(K, L, r))
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ(K, L, r))
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wᵣ(K, L, r))).IsMulRightInvariant],
    let S := fullAEL2CuspidalSubmodule K Wᵣ(K, L, r) hPD hW T i hi I e hc
    let π := fullAEL2CuspidalBoundedRightAction K Wᵣ(K, L, r) hPD hW T i hi I e hc
    ∀ (P Q : Submodule ℂ S),
      IsIrreducibleClosedSummand π P → IsIrreducibleClosedSummand π Q →
      ∀ (hPi : ∀ a x, x ∈ P → π a x ∈ P) (U : P ≃ₗᵢ[ℂ] Q),
        (∀ a (x : P), (U ⟨π a x, hPi a x x.2⟩ : S) = π a (U x)) → P = Q

set_option allowUnsafeReducibility true in
attribute [local irreducible] AffineWeil.groupScheme

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Haar rescaling makes the Weil pullback unitary, so upper-field cuspidal
multiplicity one applies to the transported summands. -/
theorem weilGeneralLinearCuspidalMultiplicityOne :
    WeilGeneralLinearCuspidalMultiplicityOneStatement.{u} := by
  intro K _ _ L _ _ _ _ r hPD hW T i hi _ I _ e hc _ S π
  let W := Wᵣ(K, L, r)
  let G := GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L)
  let hG := isConnectedReductive_generalLinear L (Fin (r + 1))
  let Z := Gm (Spec (CommRingCat.of L))
  let z := GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of L)
  let hj := scalarCharacter_injective L r
  let hcz := scalar_isCentral L r
  let ez := splitTorus.gmIso (Spec (CommRingCat.of L))
  let w := weilIso K L r
  let : IsAffine W.X.left := by
    let : IsAffineHom W.X.hom := hW.isAffineHom
    exact isAffine_of_isAffineHom W.X.hom
  let : LocallyOfFiniteType W.X.hom := by
    let : Smooth W.X.hom := hW.smooth
    infer_instance
  let : (characterRestrict z).range.FiniteIndex := scalarCharacter_finiteIndex L r
  let : (Measure.haar : Measure (normOneSubgroup L G)).IsMulRightInvariant :=
    normOneHaar_rightInvariant K L w
  let hw := map_positiveImage K L r T i hi I e hc
  let SL := fullAEL2CuspidalSubmodule L G hPD hG Z z hj PUnit ez hcz
  let πL := fullAEL2CuspidalBoundedRightAction L G hPD hG Z z hj PUnit ez hcz
  let C : SL ≃L[ℂ] S := cuspidalEquiv K L w hw hi I e hc hj PUnit ez hcz hPD hW hG
  let c : ℝ≥0∞ := normOneHaarFactor K L w
  let d := c.toReal ^ (2 : ℝ≥0∞).toReal⁻¹
  have hc0 : c ≠ 0 := ENNReal.coe_ne_zero.mpr (normOneHaarFactor_pos K L w).ne'
  have hd : 0 < d := Real.rpow_pos_of_pos (ENNReal.toReal_pos hc0 ENNReal.coe_ne_top) _
  have hCnorm (x : SL) : ‖C x‖ = d * ‖x‖ := by
    change ‖quotientL2Equiv K L w hw hi I e hc hj PUnit ez hcz x.val‖ = _
    exact norm_l2Equiv (quotientMeasurableEquiv K L w hw hi I e hc hj PUnit ez hcz)
      (map_positiveQuotientHaar K L w hi e hj ez hw hc hcz) hc0 ENNReal.coe_ne_top x.val
  let s : ℂ := (d⁻¹ : ℝ)
  have hs : ‖s‖ = d⁻¹ := by
    exact (Complex.norm_real _).trans (Real.norm_of_nonneg (inv_nonneg.mpr hd.le))
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (hs.trans_ne (inv_ne_zero hd.ne'))
  let E : SL ≃ₗᵢ[ℂ] S :=
    { toLinearEquiv := C.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℂ S s hs0)
      norm_map' := fun x => by
        change ‖s • C x‖ = ‖x‖
        rw [norm_smul, hs, hCnorm, ← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul] }
  let a := ambientEquiv K L w
  have hE (g : AdelicGroupPoints K W) (x : SL) :
      E (πL (a g) x) = π g (E x) := by
    change s • C (πL (a g) x) = π g (s • C x)
    rw [map_smul]
    exact congrArg (s • ·) (cuspidalEquiv_rightAction K L w hw hi I e hc hj PUnit ez hcz
      hPD hW hG g x)
  have hinv (g : AdelicGroupPoints L G) (x : S) :
      E.symm (π (a.symm g) x) = πL g (E.symm x) := by
    apply E.injective
    rw [E.apply_symm_apply]
    have key := hE (a.symm g) (E.symm x)
    rw [a.apply_symm_apply, E.apply_symm_apply] at key
    exact key.symm
  exact multiplicityOne_of_isometricTransport a.symm a.symm.surjective E.symm hinv
    (generalLinearCuspidalMultiplicityOne L (r + 1) hPD Z z hj PUnit ez hcz)

end Langlands.TraceFormula
