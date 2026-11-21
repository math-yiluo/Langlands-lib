import Langlands.Geometry.FormalGroup.AffineOrderTensor
import Langlands.Geometry.FormalGroup.CentralGlobalNumerator
import Langlands.Geometry.FormalGroup.CentralFramingHeightZero
import Langlands.Geometry.FormalGroup.PrimalAtlasChartFraming
import Langlands.Geometry.FormalGroup.PrimalAtlasQuasiIsogeny
import Langlands.Geometry.FormalGroup.AtlasRationalHeight
import Langlands.Geometry.FormalGroup.RationalHeightBaseChange

/-! # Central chart sections of the actual split primal atlas tensor -/

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

/-- The centrally changed section of the actual local projection, expressed in the
central atlas's chart coordinates. -/
def centralFramingOnChart :=
  let a := I.centralDivisionImageOnChartIso hE B (sourceChart h b) hb
  let d := J.centralDivisionImageOnChartIso hG B b hb
  let P := I.divisionImageOnChart B (sourceChart h b) hb
  let Q := J.divisionImageOnChart B b hb
  let f := I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ
  let hf := I.restrictLocalQuasiIsogenyOnChart_orderLinear J (h := h) B b hb z hz hπ
  RationalSection.transportIso a.toModuleIso d.toModuleIso ⊤
    (RationalSection.centralScalarSection (K := K)
      (hs := P.structuralCentralTangent (structuralDivisionTangent_test hE B))
      (ht := Q.structuralCentralTangent (structuralDivisionTangent_test hG B)) f hf hπ hpK)

section Tensor

variable [IsDomain C] [IsFractionRing C K]

/-- Evaluating the actual central tensor on a chart gives the transported centralized
section of the local projection. The same global numerator computes both maps. -/
theorem restrictCentralQuasiIsogeny_chart_section :
    let t := z.toOrderTensor hπ hz
    let q := I.restrictCentralQuasiIsogeny J (h := h) (I.divisionOrder_centralTangent hE)
      (J.divisionOrder_centralTangent hG) t hπ hpK z.source_divisible z.target_divisible
    RationalSection.ofGlobal (q.hom.onChart B b hb).val =
      I.centralFramingOnChart J (h := h) hE hG B b hb z hz hπ hpK := by
  dsimp only
  let S := I.divisionOrder_centralTangent hE
  let T := J.divisionOrder_centralTangent hG
  let t := z.toOrderTensor hπ hz
  let q := I.restrictCentralQuasiIsogeny J (h := h) S T t hπ hpK z.source_divisible z.target_divisible
  obtain ⟨n, f, hn, hq⟩ := I.restrictCentralQuasiIsogeny_forwardPresentation J (h := h) S T
    t hπ hpK z.source_divisible z.target_divisible
  let φ := IsScalarTower.toAlgHom O R B
  let I₀ : (E.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))).DivisionImage _ :=
    (I.image (sourceChart h b)).2
  let J₀ : (G.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))).DivisionImage _ := (J.image b).2
  let P := I.divisionImageOnChart B (sourceChart h b) hb
  let Q := J.divisionImageOnChart B b hb
  let fA := I.restrictDivisionHom J (h := h) f
  let fC := fA.centralScalars S T
  let fOld := fA.onChart B b hb
  let g : ModuleLaw.OrderAction.Hom P.order Q.order := ⟨fOld.val, by
    intro a
    have hf := fOld.commutes a
    have hI := I₀.overChartTest_order_action B hb a
    have hJ := J₀.overChartTest_order_action B hb a
    exact (congrArg (fOld.val.comp ·) hI.symm).trans
      (hf.trans (congrArg (·.comp fOld.val) hJ))⟩
  have h0 : (p : F) ^ n • z.val = RationalSection.ofHom f.val ⊤ := by
    have hh := congrArg (RationalSection.ofGlobalOn (F := F) (M := M) (N := N) ⊤) hn
    change RationalSection.ofGlobalOn ⊤ ((algebraMap O F (p : O)) ^ n • (z.toOrderTensor hπ hz).hom.val) = _ at hh
    rw [map_smul, LocalQuasiIsogeny.ofGlobalOn_toOrderTensor_hom, RationalSection.ofGlobalOn_ofHom,
      map_natCast] at hh
    exact hh
  let zB : RationalSection F (M.overAlgebra B) (N.overAlgebra B) ⊤ := RationalSection.baseChange φ ⊤ z.val
  have h1 : (p : F) ^ n • zB = RationalSection.ofHom (f.val.map φ) ⊤ := by
    have hh := congrArg (RationalSection.baseChange φ ⊤) h0
    rw [map_smul, RationalSection.baseChange_ofHom] at hh
    exact hh
  let z' := I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ
  let h' := I.restrictLocalQuasiIsogenyOnChart_orderLinear J (h := h) B b hb z hz hπ
  have h2 : (p : F) ^ n • z'.val = RationalSection.ofHom g.val ⊤ := by
    change (p : F) ^ n • P.restrictSection Q zB =
      RationalSection.ofHom (P.restrictHom Q (f.val.map φ)) ⊤
    have hcs : (p : F) ^ n • P.restrictSection Q zB =
        P.restrictSection Q ((p : F) ^ n • zB) := by
      simp only [Hom.IdempotentImage.restrictSection, RationalSection.smul_comp, RationalSection.comp_smul]
    exact hcs.trans ((congrArg (P.restrictSection Q) h1).trans (P.restrictSection_ofHom Q _ ⊤))
  let a := (I.centralDivisionImageOnChartIso hE B (sourceChart h b) hb).toModuleIso
  let d := (J.centralDivisionImageOnChartIso hG B b hb).toModuleIso
  let hgS := P.structuralCentralTangent (structuralDivisionTangent_test hE B)
  let hgT := Q.structuralCentralTangent (structuralDivisionTangent_test hG B)
  have hs := RationalSection.centralScalarSection_ofGlobalNumerator (hs := hgS) (ht := hgT)
    z' h' hπ hpK g h2
  let gC := (g.centralScalars (h := hgS) (h' := hgT)).val
  have hmaps : fC.val.hom B b hb = d.hom.comp (gC.comp a.inv) := by
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change fOld.val.toHom.toCoordinateMap =
      CoordinateMap.id.comp (fOld.val.toHom.toCoordinateMap.comp CoordinateMap.id)
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id]
  have hleft : RationalSection.ofGlobal (q.hom.onChart B b hb).val =
      ((p : K) ^ n)⁻¹ • RationalSection.ofHom (fC.val.hom B b hb) ⊤ := by
    let c := ((p : K) ^ n)⁻¹
    let fK := BasicAtlas.OrderAction.RationalHom.ofHom (F := K) fC
    let eval := BasicAtlas.OrderAction.RationalHom.onChartLinear
      (F := K) (E := (I.divisionOrder E).centralAtlasOrder S)
      (E' := (J.divisionOrder G).centralAtlasOrder T) (h := h) B b hb
    have hq' : q.hom = c • fK := hq
    have hchart : q.hom.onChart B b hb =
        c • ModuleLaw.OrderAction.RationalHom.ofHom (F := K) (fC.onChart B b hb) :=
      (congrArg eval hq').trans ((eval.map_smul c fK).trans
        (congrArg (c • ·) (BasicAtlas.OrderAction.RationalHom.onChart_ofHom fC B b hb)))
    have hchart' : (q.hom.onChart B b hb).val =
        c • ModuleLaw.RationalHom.ofHom (F := K) (fC.val.hom B b hb) := by
      have hh := congrArg Subtype.val hchart
      exact hh
    have hc := congrArg (RationalSection.ofGlobalOn (F := K) ⊤) hchart'
    rw [map_smul, RationalSection.ofGlobalOn_ofHom] at hc
    exact hc
  have hright : RationalSection.transportIso a d ⊤
      (RationalSection.centralOfGlobalNumerator (K := K) (hs := hgS) (ht := hgT) p n g ⊤) =
      ((p : K) ^ n)⁻¹ • RationalSection.ofHom (d.hom.comp (gC.comp a.inv)) ⊤ := by
    change RationalSection.comp (RationalSection.ofHom (F := K) d.hom ⊤)
      (RationalSection.comp (((p : K) ^ n)⁻¹ • RationalSection.ofHom gC ⊤)
        (RationalSection.ofHom a.inv ⊤)) = _
    rw [RationalSection.smul_comp, RationalSection.comp_smul,
      RationalSection.comp_ofHom, RationalSection.comp_ofHom]
  change RationalSection.ofGlobal (q.hom.onChart B b hb).val =
    RationalSection.transportIso a d ⊤ (RationalSection.centralScalarSection (hs := hgS) (ht := hgT) z' h' hπ hpK)
  exact hleft.trans ((congrArg (fun f => ((p : K) ^ n)⁻¹ • RationalSection.ofHom (F := K) f ⊤) hmaps).trans
    (hright.symm.trans (congrArg (RationalSection.transportIso a d ⊤) hs).symm))

/-- Zero prime-normalized height of the actual local projections gives zero
uniformizer-normalized height of their global central atlas tensor. -/
theorem restrictCentralQuasiIsogeny_height_zero {ϖ : C} {e q H : ℕ} {u : Cˣ}
    (hcal : (p : C) = (u : C) * ϖ ^ e)
    (hsource : ∀ (B : CommAlgCat.{v} R) (b : J.atlas.opens)
      (hb : IsUnit (algebraMap R B b.val)),
      ((((I.divisionOrder E).centralAtlas (I.divisionOrder_centralTangent hE)).chart
        (sourceChart (X := I.atlas) (Y := J.atlas) h b)).map
          (coefficientLift (O := C) b.val B hb)).HasPiHeight ϖ q H)
    (hzero : ∀ (B : CommAlgCat.{v} R) (b : J.atlas.opens)
      (hb : IsUnit (algebraMap R B b.val)),
      RationalSection.HasHeightFunction (p : O) p
        (I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ).val (fun _ => 0)) :
    let t := z.toOrderTensor hπ hz
    let g := I.restrictCentralQuasiIsogeny J (h := h) (I.divisionOrder_centralTangent hE)
      (J.divisionOrder_centralTangent hG) t hπ hpK z.source_divisible z.target_divisible
    g.hom.val.HasConstantChartHeight ϖ q 0 := by
  dsimp only
  intro B b hb
  have he := I.restrictCentralQuasiIsogeny_chart_section J (h := h) hE hG B b hb z hz hπ hpK
  let a := (I.centralDivisionImageOnChartIso hE B (sourceChart h b) hb).toModuleIso
  let d := (J.centralDivisionImageOnChartIso hG B b hb).toModuleIso
  let f := I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ
  let hf := I.restrictLocalQuasiIsogenyOnChart_orderLinear J (h := h) B b hb z hz hπ
  have hrank := a.symm.hasPiHeight ϖ (hsource B b hb)
  have hh : RationalSection.HasHeightFunction ϖ q
      (I.centralFramingOnChart J (h := h) hE hG B b hb z hz hπ hpK) (fun _ => 0) :=
    (RationalSection.HasHeightFunction.centralScalarSection_zero f hf hπ hpK
      (hzero B b hb) hcal hrank).transportIso a d
  exact he.symm ▸ hh

end Tensor

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
