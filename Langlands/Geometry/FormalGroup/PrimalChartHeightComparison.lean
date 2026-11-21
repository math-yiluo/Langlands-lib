import Langlands.Geometry.FormalGroup.CentralFramingHeightComparison
import Langlands.Geometry.FormalGroup.PrimalAtlasCentralChart
import Langlands.Geometry.FormalGroup.RationalHeightProof

/-! # Prime and central heights on the same split primal chart -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory TopologicalSpace BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {F K : Type v} [Field F] [Algebra O F] [IsFractionRing O F] [Field K] [Algebra C K]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} {G : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) N}
variable (I : IdempotentImageCover E.divisionProjector σ')
variable (J : IdempotentImageCover G.divisionProjector τ')
variable {h : I.atlas.opens = J.atlas.opens}
variable (hE : E.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
variable (hG : G.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
variable (B : CommAlgCat.{v} R) (b : J.atlas.opens) (hb : IsUnit (algebraMap R B b.val))
variable {p : ℕ} (z : LocalQuasiIsogeny F (p : O) M N ⊤)
variable (hz : RationalSection.IsOrderLinear E G z.val) (hπ : Irreducible (p : O)) (hpK : (p : K) ≠ 0)

variable [Finite (IsLocalRing.ResidueField O)]
variable [IsDomain C] [IsDiscreteValuationRing C] [Finite (IsLocalRing.ResidueField C)] [IsFractionRing C K]

local notation "q" => Nat.card (IsLocalRing.ResidueField C)

/-- The prime-normalized rank function of the actual local primal map, with
its exact central normalization in the evaluated global primal tensor. -/
def restrictCentralQuasiIsogeny_chartRank {ϖ : C} {e l H H' : ℕ} {u : Cˣ}
    (hpO : Nat.card (IsLocalRing.ResidueField O) = p) (hp : 1 < p) (hl : 0 < l)
    (hϖ : Irreducible ϖ) (hcal : (p : C) = (u : C) * ϖ ^ e)
    (hq : Nat.card (IsLocalRing.ResidueField C) = p ^ l)
    (hsource : ((((I.divisionOrder E).centralAtlas (I.divisionOrder_centralTangent hE)).chart
      (sourceChart (X := I.atlas) (Y := J.atlas) h b)).map
        (coefficientLift (O := C) b.val B hb)).HasPiHeight ϖ q H)
    (htarget : ((((J.divisionOrder G).centralAtlas (J.divisionOrder_centralTangent hG)).chart b).map
      (coefficientLift (O := C) b.val B hb)).HasPiHeight ϖ q H') :
    let t := z.toOrderTensor hπ hz
    let g := I.restrictCentralQuasiIsogeny J (h := h) (I.divisionOrder_centralTangent hE)
      (J.divisionOrder_centralTangent hG) t hπ hpK z.source_divisible z.target_divisible
    {k : (⊤ : Opens (PrimeSpectrum B)) → ℤ //
      RationalSection.HasHeightFunction (p : O) p
        (I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ).val k ∧
      (∀ x, (l : ℤ) ∣ k x) ∧
      RationalSection.HasHeightFunction ϖ q
        (RationalSection.ofGlobal (g.hom.onChart B b hb).val) (fun x => k x / (l : ℤ))} := by
  dsimp only
  let a := (I.centralDivisionImageOnChartIso hE B (sourceChart h b) hb).toModuleIso
  let d := (J.centralDivisionImageOnChartIso hG B b hb).toModuleIso
  let P := I.divisionImageOnChart B (sourceChart h b) hb
  let Q := J.divisionImageOnChart B b hb
  let s := P.structuralCentralTangent (structuralDivisionTangent_test hE B)
  let t := Q.structuralCentralTangent (structuralDivisionTangent_test hG B)
  let f := I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ
  let hf := I.restrictLocalQuasiIsogenyOnChart_orderLinear J (h := h) B b hb z hz hπ
  have hPC := a.symm.hasPiHeight ϖ hsource
  have hQC := d.symm.hasPiHeight ϖ htarget
  let hPD := P.order.centralModule_isPiDivisible_natCast s p f.source_divisible
  let hQD := Q.order.centralModule_isPiDivisible_natCast t p f.target_divisible
  have hP := P.order.hasPiHeight_natCast_of_centralModule s f.source_divisible
    ((hq ▸ hPC).unit_mul_pow hPD hcal)
  have hQ := Q.order.hasPiHeight_natCast_of_centralModule t f.target_divisible
    ((hq ▸ hQC).unit_mul_pow hQD hcal)
  let hk := (rationalHeightExistenceUniqueness O F B (p : O) hπ _ _ _ _ _ _
    ((congrArg (fun q₀ => ModuleLaw.HasPiHeight _ (p : O) q₀ (e * l * H)) hpO).mpr hP)
    ((congrArg (fun q₀ => ModuleLaw.HasPiHeight _ (p : O) q₀ (e * l * H')) hpO).mpr hQ) ⊤ f).exists
  let k := hk.choose
  have hheight : RationalSection.HasHeightFunction (p : O) p f.val k :=
    (congrArg (fun q₀ => RationalSection.HasHeightFunction (p : O) q₀ f.val k) hpO).mp hk.choose_spec
  have hcentral := hheight.centralScalarSection_divide (hs := s) (ht := t) f hf hπ hpK
    hp hl hϖ hcal hq hPC hQC.piDivisible
  have he := I.restrictCentralQuasiIsogeny_chart_section J (h := h) hE hG B b hb z hz hπ hpK
  have hx : RationalSection.HasHeightFunction ϖ q
      (I.centralFramingOnChart J (h := h) hE hG B b hb z hz hπ hpK) (fun x => k x / (l : ℤ)) :=
    hcentral.1.transportIso a d
  exact ⟨k, hheight, hcentral.2, he.symm ▸ hx⟩

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
