import Langlands.Geometry.FormalGroup.CentralImageAtlasComparison
import Langlands.Geometry.FormalGroup.IdempotentLocalQuasiIsogeny
import Langlands.Geometry.FormalGroup.PolarizedRationalSectionIso
import Langlands.Geometry.FormalGroup.CentralOrderIntegralMap

/-! # Projecting the actual local quasi-isogeny on a chart test -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory TopologicalSpace BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} {G : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) N}
variable (I : IdempotentImageCover E.divisionProjector σ')
variable (J : IdempotentImageCover G.divisionProjector τ')

/-- The actual division retraction on a chart test algebra. -/
abbrev divisionImageOnChart (B : CommAlgCat.{v} R) (b : I.atlas.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    (E.overAlgebra B).DivisionImage ((I.atlas.chart b).map (coefficientLift (O := O) b.val B hb)) :=
  (I.image b).2.overChartTest B hb

section Central

variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable (hE : E.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))

include hE in
/-- The actual split tangent condition on a test algebra follows by coefficient extension. -/
theorem structuralDivisionTangent_test (B : CommAlgCat.{v} R) :
    (E.overAlgebra B).HasStructuralDivisionTangent (algebraMap C D) (algebraMap C B) := by
  rw [IsScalarTower.algebraMap_eq C R B]
  exact hE.map (IsScalarTower.toAlgHom O R B)

/-- Compare the central law of the retraction on a test with the test law of the
centralized division atlas. The comparison has identity coordinates. -/
def centralDivisionImageOnChartIso (B : CommAlgCat.{v} R) (b : I.atlas.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.Iso
      ((I.divisionImageOnChart B b hb).centralOrder (structuralDivisionTangent_test hE B))
      ((((I.divisionOrder E).centralAtlasOrder (I.divisionOrder_centralTangent hE)).chart b).map
        (coefficientLift (O := C) b.val B hb)) :=
  ModuleLaw.OrderAction.Iso.ofIdenticalCoordinates rfl (fun d => by
    let φ := IsScalarTower.toAlgHom O R (Localization.Away b.val)
    let I₀ : (E.map φ).DivisionImage _ := (I.image b).2
    have h := I₀.overChartTest_order_action B hb d
    exact (congrArg (fun g => g.toHom.toCoordinateMap) h).symm)

end Central

section LocalFraming

variable {F : Type v} [Field F] [Algebra O F] {π : O}
variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]
variable {h : I.atlas.opens = J.atlas.opens}
variable (B : CommAlgCat.{v} R) (b : J.atlas.opens) (hb : IsUnit (algebraMap R B b.val))
variable (z : LocalQuasiIsogeny F π M N ⊤) (hz : RationalSection.IsOrderLinear E G z.val)
variable (hπ : Irreducible π)

/-- Pull the local quasi-isogeny to a chart test and project it with the actual source
and target retractions. -/
def restrictLocalQuasiIsogenyOnChart : LocalQuasiIsogeny F π
    ((I.atlas.chart (sourceChart h b)).map (coefficientLift (O := O) b.val B hb))
    ((J.atlas.chart b).map (coefficientLift (O := O) b.val B hb)) ⊤ := by
  let φ := IsScalarTower.toAlgHom O R B
  let zB : LocalQuasiIsogeny F π (M.overAlgebra B) (N.overAlgebra B) ⊤ := z.baseChange φ
  let P := I.divisionImageOnChart B (sourceChart h b) hb
  let Q := J.divisionImageOnChart B b hb
  have hB : RationalSection.IsOrderLinear (E.overAlgebra B) (G.overAlgebra B) zB.val := hz.baseChange φ
  exact P.restrictLocalQuasiIsogeny Q hπ zB (hB (0, 1))

/-- The projected section is order-linear on the actual division images of the test laws. -/
theorem restrictLocalQuasiIsogenyOnChart_orderLinear :
    RationalSection.IsOrderLinear (I.divisionImageOnChart B (sourceChart h b) hb).order
      (J.divisionImageOnChart B b hb).order
      (I.restrictLocalQuasiIsogenyOnChart J (h := h) B b hb z hz hπ).val := by
  intro a
  let φ := IsScalarTower.toAlgHom O R B
  let zB : RationalSection F (M.overAlgebra B) (N.overAlgebra B) ⊤ := RationalSection.baseChange φ ⊤ z.val
  let P := I.divisionImageOnChart B (sourceChart h b) hb
  let Q := J.divisionImageOnChart B b hb
  let f := (E.overAlgebra B).action (0, a)
  let g := (G.overAlgebra B).action (0, a)
  have hB : RationalSection.IsOrderLinear (E.overAlgebra B) (G.overAlgebra B) zB := hz.baseChange φ
  have hf : RationalSection.comp (RationalSection.ofHom (F := F) f ⊤)
      (RationalSection.ofHom (E.overAlgebra B).divisionProjector ⊤) =
      RationalSection.comp (RationalSection.ofHom (E.overAlgebra B).divisionProjector ⊤)
        (RationalSection.ofHom f ⊤) := by
    rw [RationalSection.comp_ofHom, RationalSection.comp_ofHom]
    exact congrArg (fun m => RationalSection.ofHom m ⊤)
      (((E.overAlgebra B).action_comp_divisionProjector a).trans
        ((E.overAlgebra B).divisionProjector_comp_action a).symm)
  change RationalSection.comp (P.restrictSection Q zB)
      (RationalSection.ofHom (P.restrictHom P f) ⊤) =
    RationalSection.comp (RationalSection.ofHom (Q.restrictHom Q g) ⊤) (P.restrictSection Q zB)
  rw [← P.restrictSection_ofHom, ← Q.restrictSection_ofHom,
    ← P.restrictSection_comp P Q _ _ hf, hB (0, a), P.restrictSection_comp Q Q _ _ (hB (0, 1))]

end LocalFraming

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover
