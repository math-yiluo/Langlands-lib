import Langlands.GroupScheme.RelativeLevi.FaceCoverTermMaps
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Actual global fppf quotients of the descended face terms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open Descent

variable {S : Scheme.{u}} {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

local instance quotientAssemblyDecomposition : IsIso (Sigma.desc D.componentMap) := by
  change IsIso (Sigma.desc (Sigma.ι (fun a : D.Index => Spec (D.charts a.down).2.ring)))
  rw [Sigma.desc_ι]
  infer_instance

/-- Actual component projections compose to the prescribed original chart projection. -/
theorem componentMap_comp_groupsBaseMap (a : D.Index) :
    D.componentMap a ≫ D.groupsBaseMap = (D.charts a.down).2.projection := by
  simp only [componentMap, groupsBaseMap, Sigma.ι_comp_desc]

/-- The cover-family map is the prescribed original chart projection. -/
theorem chartCover_projection (a : D.Index) :
    D.chartCover.f a = (D.charts a.down).2.projection := rfl

/-- Compare a restricted global term with the same component of the assembled term. -/
def globalTermCoverComponentIso (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).obj
        ((baseChange D.groupsBaseMap).obj (D.globalTerm r hG hp hr d)) ≅
      (baseChange (D.componentMap a)).obj (D.termGroup d) :=
  Descent.pullbackComparison D.groupsBaseMap (D.componentMap a)
      (D.charts a.down).2.projection (D.componentMap_comp_groupsBaseMap a)
      (D.globalTerm r hG hp hr d) ≪≫
    D.globalTermChartIso r hG hp hr d a ≪≫ (D.termComponentIso d a).symm

/-- The original global term pulled to the finite affine cover is the actual assembled term. -/
def globalTermCoverIso (d : ℕ) :
    (baseChange D.groupsBaseMap).obj (D.globalTerm r hG hp hr d) ≅ D.termGroup d :=
  DisjointComponents.groupIso D.componentMap (D.globalTermCoverComponentIso r hG hp hr d)

/-- The assembled comparison retains the actual chart recovery on each component. -/
theorem globalTermCoverIso_component (d : ℕ) (a : D.Index) :
    (baseChange (D.componentMap a)).map (D.globalTermCoverIso r hG hp hr d).hom ≫
        (D.termComponentIso d a).hom =
      (Descent.pullbackComparison D.groupsBaseMap (D.componentMap a)
        (D.charts a.down).2.projection (D.componentMap_comp_groupsBaseMap a)
        (D.globalTerm r hG hp hr d)).hom ≫
          (D.globalTermChartIso r hG hp hr d a).hom := by
  rw [globalTermCoverIso, DisjointComponents.groupIso, DisjointComponents.map_groupHom]
  simp only [globalTermCoverComponentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Recovery on the affine cover preserves the ORIGINAL ambient inclusion. -/
theorem globalTermCoverIso_hom_comp_inclusion (d : ℕ) :
    (D.globalTermCoverIso r hG hp hr d).hom ≫ D.termInclusion d =
      (baseChange D.groupsBaseMap).map (D.globalTermInclusion r hG hp hr d) := by
  apply DisjointComponents.groupHom_ext D.componentMap
  intro a
  apply (cancel_mono (D.ambientComponentIso a).hom).mp
  rw [Functor.map_comp, Category.assoc, D.termInclusion_component,
    ← Category.assoc, D.globalTermCoverIso_component, Category.assoc,
    D.globalTermChartIso_hom_comp]
  simpa only [ambientComponentIso, globalTermInclusion, D.chartCover_projection] using
    (Descent.pullbackComparison_naturality D.groupsBaseMap (D.componentMap a)
      (D.charts a.down).2.projection (D.componentMap_comp_groupsBaseMap a)
      (D.globalTermInclusion r hG hp hr d)).symm

/-- The actual cover comparison preserves the original successive inclusions. -/
theorem globalTermCoverIso_step (d : ℕ) :
    (baseChange D.groupsBaseMap).map (D.globalTermStep r hG hp hr d) ≫
        (D.globalTermCoverIso r hG hp hr d).hom =
      (D.globalTermCoverIso r hG hp hr (d + 1)).hom ≫ D.termStep d := by
  let : IsClosedImmersion (D.termInclusion d).hom.hom.left :=
    D.isClosedSubgroup_termInclusion d
  have hrep : (SubgroupFunctor.range (D.termInclusion d)).IsRepresentedBy (D.termInclusion d) :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, D.globalTermCoverIso_hom_comp_inclusion, ← Functor.map_comp,
    D.globalTermStep_comp_inclusion, Category.assoc, D.termStep_comp_inclusion,
    D.globalTermCoverIso_hom_comp_inclusion]

/-- The actual quotient over the affine cover, with original global source. -/
def coverProjection (d : ℕ) :
    (baseChange D.groupsBaseMap).obj (D.globalTerm r hG hp hr d) ⟶ D.layerGroup d :=
  (D.globalTermCoverIso r hG hp hr d).hom ≫ D.layerProjection d

/-- Its full fppf kernel is exactly the pullback of the actual global successive inclusion. -/
theorem isFppfQuotient_coverProjection (d : ℕ) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange D.groupsBaseMap).map
        (D.globalTermStep r hG hp hr d)))
      (D.coverProjection r hG hp hr d) := by
  have h := FppfQuotientComparison.precomp_iso
    (D.isFppfQuotient_layerProjection d) (D.globalTermCoverIso r hG hp hr d)
  rw [FppfQuotientComparison.range_comap_of_compatible_isos
    ((baseChange D.groupsBaseMap).map (D.globalTermStep r hG hp hr d)) (D.termStep d)
    (D.globalTermCoverIso r hG hp hr d) (D.globalTermCoverIso r hG hp hr (d + 1))
    (D.globalTermCoverIso_step r hG hp hr d)] at h
  exact h

section Affine

variable [IsAffine S]

local instance quotientGlobalTermAffine (d : ℕ) :
    IsAffine (D.globalTerm r hG hp hr d).X.left := D.isAffine_globalTerm r hG hp hr d

local instance quotientGlobalCoverTermAffine (d : ℕ) :
    IsAffine ((baseChange D.groupsBaseMap).obj (D.globalTerm r hG hp hr d)).X.left := by
  change IsAffine (pullback (D.globalTerm r hG hp hr d).X.hom D.groupsBaseMap)
  infer_instance

/-- Actual global affine quotient data retaining the supplied cover projection. -/
structure GlobalFaceQuotientData (d : ℕ) where
  group : GroupScheme S
  projection : D.globalTerm r hG hp hr d ⟶ group
  affine : IsAffine group.X.left
  quotient : RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range (D.globalTermStep r hG hp hr d)) projection
  coverIso : (baseChange D.groupsBaseMap).obj group ≅ D.layerGroup d
  recovery : (baseChange D.groupsBaseMap).map projection ≫ coverIso.hom =
    D.coverProjection r hG hp hr d

/-- The actual affine cover quotient effectively descends with its full original kernel. -/
theorem nonempty_globalFaceQuotientData (d : ℕ) :
    Nonempty (D.GlobalFaceQuotientData r hG hp hr d) := by
  let : IsClosedImmersion (D.globalTermStep r hG hp hr d).hom.hom.left :=
    D.isClosedSubgroup_globalTermStep r hG hp hr d
  let : Mono (D.globalTermStep r hG hp hr d).hom.hom := Over.mono_of_mono_left _
  obtain ⟨Q, q, hQ, hq, e, he⟩ := Descent.exists_affine_fppfQuotient D.groupsBaseMap
    (D.globalTermStep r hG hp hr d) (D.layerGroup d)
    (D.coverProjection r hG hp hr d) (D.isFppfQuotient_coverProjection r hG hp hr d)
  exact ⟨⟨Q, q, hQ, hq, e, he⟩⟩

/-- Choose the proved actual global affine quotient at the prescribed cutoff. -/
def globalFaceQuotientData (d : ℕ) : D.GlobalFaceQuotientData r hG hp hr d :=
  Classical.choice (D.nonempty_globalFaceQuotientData r hG hp hr d)

/-- The next actual global term is normal in the preceding one, by the full quotient kernel. -/
theorem isNormal_globalTermStep (d : ℕ) :
    (SubgroupFunctor.range (D.globalTermStep r hG hp hr d)).IsNormal := by
  rw [← (D.globalFaceQuotientData r hG hp hr d).quotient.2.2.2]
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one, mul_inv_cancel]

end Affine
end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover
