import Langlands.TraceFormula.GroupSchemeTwistCuspidalInvarianceProof
import Langlands.TraceFormula.IsotypicTrace.TwistCovariance
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-! # The twisting isometry of the full cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

namespace Langlands.TraceFormula

private theorem compMeasurePreserving_leftInverse {X : Type*} [MeasurableSpace X]
    {m : Measure X} {f g : X → X} (hf : MeasurePreserving f m m)
    (hg : MeasurePreserving g m m) (h : Function.LeftInverse g f) (φ : Lp ℂ 2 m) :
    Lp.compMeasurePreserving f hf (Lp.compMeasurePreserving g hg φ) = φ := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have congr (k l : X → X) (hk : MeasurePreserving k m m)
      (hl : MeasurePreserving l m m) (hkl : k = l) :
      Lp.compMeasurePreserving k hk φ = Lp.compMeasurePreserving l hl φ := by
    subst l
    rfl
  exact (congr (g ∘ f) id (hg.comp hf) (MeasurePreserving.id m) (funext h)).trans
    (Lp.compMeasurePreserving_id_apply φ)

variable (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "Γ" => positiveRationalSubgroup F G T i
local notation "Q" => PositiveRationalQuotient F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "π" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc

/-- The ambient inverse pullback restricts to a surjective linear isometry on
the full cuspidal space, with covariance for the cuspidal right action. -/
def GroupSchemeCuspidalTwistEquivStatement : Prop :=
  ∀ (α : G ≅ G) (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G),
    (∀ x, Θ x = AdelicGroupPoints.map F G G α.hom x) →
    ∀ (hΘ : ∀ x, Θ x ∈ Γ ↔ x ∈ Γ)
      (hΘμ : MeasurePreserving (quotientAutomorphism Γ Θ hΘ).symm μQ μQ),
      ∃ U : S ≃ₗᵢ[ℂ] S,
        (∀ φ : S, (U φ).val = twistOperator Γ Θ hΘ μQ hΘμ φ.val) ∧
        ∀ a φ, U (π a φ) = π (Θ a) (U φ)

/-- Restrict the pullbacks in both directions and use the ambient covariance identity. -/
theorem groupSchemeCuspidalTwistEquiv :
    GroupSchemeCuspidalTwistEquivStatement F G hPD hG T i hi I e hc := by
  intro α Θ hα hΘ hΘμ
  have hαinv (x : AdelicGroupPoints F G) :
      Θ.symm x = AdelicGroupPoints.map F G G α.inv x := by
    apply Θ.injective
    rw [Θ.apply_symm_apply, hα]
    simp only [AdelicGroupPoints.map_apply, GroupScheme.affinePointsTarget_apply,
      Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hΘinv (x : AdelicGroupPoints F G) : Θ.symm x ∈ Γ ↔ x ∈ Γ := by
    simpa only [Θ.apply_symm_apply] using (hΘ (Θ.symm x)).symm
  let q := quotientAutomorphism Γ Θ hΘ
  let qInv := quotientAutomorphism Γ Θ.symm hΘinv
  have hq (x : Q) : qInv.symm x = q x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change (quotientAutomorphism Γ Θ.symm hΘinv).symm (Quotient.mk _ x) =
        quotientAutomorphism Γ Θ hΘ (Quotient.mk _ x)
      rw [quotientAutomorphism_symm_mk, quotientAutomorphism_mk, Θ.symm_symm]
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  have hqμ : MeasurePreserving q μQ μQ :=
    MeasurePreserving.symm q.symm.toMeasurableEquiv hΘμ
  have hΘinvμ : MeasurePreserving qInv.symm μQ μQ := by
    rw [show (qInv.symm : Q → Q) = q from funext hq]
    exact hqμ
  let A := twistOperator Γ Θ hΘ μQ hΘμ
  let B := twistOperator Γ Θ.symm hΘinv μQ hΘinvμ
  have hA (φ : Lp ℂ 2 μQ) (hφ : φ ∈ S) : A φ ∈ S :=
    groupSchemeTwistCuspidalInvariance F G hPD hG T i hi I e hc α Θ hα hΘ hΘμ φ hφ
  have hB (φ : Lp ℂ 2 μQ) (hφ : φ ∈ S) : B φ ∈ S :=
    groupSchemeTwistCuspidalInvariance F G hPD hG T i hi I e hc α.symm Θ.symm hαinv
      hΘinv hΘinvμ φ hφ
  have hBA (φ : Lp ℂ 2 μQ) : B (A φ) = φ :=
    compMeasurePreserving_leftInverse hΘinvμ hΘμ
      (fun x => (congrArg q.symm (hq x)).trans (q.symm_apply_apply x)) φ
  have hAB (φ : Lp ℂ 2 μQ) : A (B φ) = φ :=
    compMeasurePreserving_leftInverse hΘμ hΘinvμ
      (fun x => (hq (q.symm x)).trans (q.apply_symm_apply x)) φ
  let U : S ≃ₗᵢ[ℂ] S :=
    { toLinearEquiv :=
        { toLinearMap := A.toLinearMap.restrict hA
          invFun := fun φ => ⟨B φ.val, hB _ φ.property⟩
          left_inv := fun φ => Subtype.ext (hBA φ.val)
          right_inv := fun φ => Subtype.ext (hAB φ.val) }
      norm_map' := fun φ => norm_twistOperator_apply Γ Θ hΘ μQ hΘμ φ.val }
  refine ⟨U, fun _ => rfl, ?_⟩
  intro a φ
  apply Subtype.ext
  exact IsotypicTrace.twistOperator_quotientL2RightTranslate F G T i μQ
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) Θ hΘ hΘμ a φ.val

end Langlands.TraceFormula
