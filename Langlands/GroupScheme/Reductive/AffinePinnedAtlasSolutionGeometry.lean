import Langlands.GroupScheme.Reductive.AffinePinnedAtlasCocharacterDescent
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport

/-! # Local geometry of actual solutions of a corrected pinned atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedAtlas

open Descent Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} (A : AffinePinnedAtlas G)
    (P : RelativePinnedComparison.{u}) (s : Solution (A.datum P))

/-- The solution's actual pullback on a chart identified with its pinned model. -/
def solutionChartIso (i : S) :
    (baseChange (A.chart i).map).obj s.obj ≅ (A.chart i).model.group :=
  (pullbackComparison A.projection (A.inclusion i) (A.chart i).map
      (A.inclusion_projection i) s.obj).symm ≪≫
    (baseChange (A.inclusion i)).mapIso s.iso ≪≫
    pullbackComparison A.projection (A.inclusion i) (A.chart i).map
      (A.inclusion_projection i) G ≪≫ (A.chart i).iso

/-- The descended cocharacter is the canonical positive-coroot cocharacter on each chart. -/
theorem descendedCocharacter_on_chart (i : S) :
    baseChangeCocharacter (A.chart i).map (A.descendedCocharacter P s) ≫
        (A.solutionChartIso P s i).hom =
      BasedBorelTransport.cocharacter (A.chart i).model.inclusion
        (A.chart i).model.rootDatum (A.chart i).model.basis := by
  have h := congrArg (fun χ => pullbackCocharacter A.projection (A.inclusion i)
    (A.chart i).map (A.inclusion_projection i) χ)
    (A.descendedCocharacter_recovers P s)
  rw [A.cocharacter_on_component] at h
  simp only [pullbackCocharacter, baseChangeCocharacter_comp_hom] at h
  rw [← baseChangeCocharacter_tower A.projection (A.inclusion i) (A.chart i).map
    (A.inclusion_projection i) (A.descendedCocharacter P s)]
  simp only [solutionChartIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [AffinePinnedChart.cocharacter, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
    using congrArg (fun χ => χ ≫ (A.chart i).iso.hom) h

/-- Reductivity of the original group is inherited by every actual solution. -/
theorem solution_isReductive (hG : IsReductive G) : IsReductive s.obj :=
  IsReductive.of_baseChange_of_etale A.projection
    ((hG.baseChange A.projection).of_iso s.iso)

/-- Any parabolic representative of the descended cocharacter is a relative Borel. -/
theorem isRelativeBorel_descendedCocharacter {B : GroupScheme S} (j : B ⟶ s.obj)
    (hG : IsReductive G)
    (hjclosed : IsClosedSubgroup j)
    (hj : (parabolic (A.descendedCocharacter P s)).IsRepresentedBy j) :
    IsRelativeBorelSubgroup j := by
  let : IsAffineHom s.obj.X.hom := (A.solution_isReductive P s hG).isAffineHom
  apply IsRelativeBorelSubgroup.of_etale_cover A.cover hjclosed
  change ∀ i : S, IsRelativeBorelSubgroup ((baseChange (A.chart i).map).map j)
  intro i
  let C := A.chart i
  let M := C.model
  let e := A.solutionChartIso P s i
  let n := BasedBorelExponent.positiveCorootSum M.rootDatum M.basis
  let : IsAffineHom M.group.X.hom := M.reductive.isAffineHom
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  have hrep : (parabolic (BasedBorelTransport.cocharacter M.inclusion
      M.rootDatum M.basis)).IsRepresentedBy ((baseChange C.map).map j ≫ e.hom) := by
    have h := hj.baseChange C.map
    rw [← parabolic_baseChange] at h
    have heq := (range_eq_parabolic_comp_iso_iff _ _ e).mpr h.2
    rw [A.descendedCocharacter_on_chart P s i] at heq
    exact ⟨(h.comp_iso e).1, heq⟩
  have hmodel : (parabolic (BasedBorelTransport.cocharacter M.inclusion
      M.rootDatum M.basis)).IsRepresentedBy (AffineRegularBorel.inclusion M.inclusion n) :=
    Dynamic.Affine.isRepresentedBy_parabolicHom _
  let b := hrep.isoOfIsRepresentedBy hmodel
  have hb := (AffineRegularBorel.isRelativeBorel_positiveCorootSum M.inclusion
    M.rootDatum M.basis M.fibrewiseRootDatum M.reductive M.maximal).iso_comp b
  rw [hrep.isoOfIsRepresentedBy_hom_comp hmodel] at hb
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    using hb.comp_iso e.symm

end Langlands.GroupScheme.AffinePinnedAtlas
