import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Derived.SemisimplePerfectProof

/-! # The unramified zero subgroup of a simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  (E : UnramifiedZeroDatum F H)

/-- For a simply connected ambient group the supplied derived-cover composite
is an isomorphism, independently of the torus and splitting-field choices. -/
theorem isIso_cover_comp_of_isSimplyConnected (hH : IsSimplyConnected H) :
    IsIso (E.π ≫ E.d) := by
  have hd : (⊤ : SubgroupFunctor H).IsRepresentedBy E.d := by
    simpa only [semisimplePerfect (UnramifiedClosure F) H hH.isSemisimple] using
      E.isSimplyConnectedDerivedCover.isDerivedSubgroup.isRepresentedBy
  have hid : (⊤ : SubgroupFunctor H).IsRepresentedBy (𝟙 H) :=
    ⟨inferInstance, SubgroupFunctor.range_id H⟩
  let e := hd.isoOfIsRepresentedBy hid
  have he : e.hom = E.d := by
    simpa only [Category.comp_id] using hd.isoOfIsRepresentedBy_hom_comp hid
  have : IsIso E.d := by rw [← he]; infer_instance
  have hD : IsSimplyConnected E.D := hH.of_iso (asIso E.d)
  have : IsIso E.π := hD.central_isogeny_isIso E.C E.π
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSimplyConnected.isSemisimple
    E.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isCentralIsogeny
  infer_instance

/-- The actual supplied derived-cover composite, regarded as an isomorphism. -/
def coverIso_of_isSimplyConnected (hH : IsSimplyConnected H) : E.C ≅ H := by
  letI := E.isIso_cover_comp_of_isSimplyConnected hH
  exact asIso (E.π ≫ E.d)

/-- The actual image of the simply connected cover is the whole point group. -/
theorem simplyConnectedImage_eq_top_of_isSimplyConnected (hH : IsSimplyConnected H) :
    E.simplyConnectedImage = ⊤ := by
  let f := E.π ≫ E.d
  have : IsIso f := E.isIso_cover_comp_of_isSimplyConnected hH
  apply MonoidHom.range_eq_top.mpr
  intro g
  refine ⟨rationalPoints.map (inv f) g, ?_⟩
  change (g ≫ (inv f).hom.hom) ≫ f.hom.hom = g
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- KP's `H(K)^0` is all of `H(K)` for every supplied zero datum of a
simply connected group over the maximal unramified field. -/
theorem zeroPoints_eq_top_of_isSimplyConnected (hH : IsSimplyConnected H) :
    E.zeroPoints = ⊤ := by
  unfold zeroPoints
  rw [E.simplyConnectedImage_eq_top_of_isSimplyConnected hH, top_sup_eq]

end UnramifiedZeroDatum

end Langlands.Geometry.Building
