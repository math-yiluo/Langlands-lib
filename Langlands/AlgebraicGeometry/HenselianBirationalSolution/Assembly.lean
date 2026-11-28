import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Group
import Langlands.AnthropicFLT.OverBase.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

/-! # The glued group scheme and its dense open chart

Every chart meets the original chart in a fibrewise dense open because its translation is
defined on a fibrewise dense open. The charts indexed by sections already cover the glued
scheme, and every such chart factors through the extended multiplication on `Y ×_S Y`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology NeronModelInfra GroupLawOverBase
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g]
  [QuasiCompact g] (H : GlueHyp m)

theorem original_chart_dense : FibreGenerizationDense (toS H) (Set.range (ch H none)) := by
  intro p
  obtain ⟨i, y, rfl⟩ := Glue.exists_chart H (secTrans H) p
  obtain ⟨z, hz, hbase, hspec⟩ := (secTrans H i).dom_dense y
  refine ⟨ch H i z, ?_, ?_, hspec.map (ch H i).continuous⟩
  · have h := congrArg (fun k : (secTrans H i).dom.toScheme ⟶ Gl H => k ⟨z, hz⟩)
      (dom_chart H i (𝟙 _))
    simp only [Category.id_comp] at h
    exact ⟨(secTrans H i).map ⟨z, hz⟩, h.symm⟩
  · simp only [← Scheme.Hom.comp_apply, ch_toS, hbase]

variable [S.IsSeparated] (hL : HasSectionLifts g)

include hL in
/-- The extended product of two points of `Y` covers the glued scheme. -/
theorem mulG_surjective : Function.Surjective (mulG H hL) := by
  intro p
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback p p (rfl : toS H p = toS H p)
  obtain ⟨c, a, ha⟩ := exists_common_chart H hL w
  have hf : chartPair H (some c) (some c) ≫ Gfst H = pullback.fst g g ≫ ch H (some c) := by
    simp [chartPair]
  have h₀ : ch H (some c) (pullback.fst g g a) = p := by
    rw [← Scheme.Hom.comp_apply, ← hf, Scheme.Hom.comp_apply, ha, hw]
  refine ⟨sectionPair c.1 c.2 (pullback.fst g g a), ?_⟩
  rw [← Scheme.Hom.comp_apply, sectionPair_mulG H hL c, h₀]

include hL in
/-- Quasi-compactness descends along the surjection from `Y ×_S Y`. -/
theorem compactSpace_glued : CompactSpace (Gl H) := by
  constructor
  rw [← Set.range_eq_univ.mpr (mulG_surjective H hL), ← Set.image_univ]
  exact isCompact_univ.image (mulG H hL).continuous

omit [S.IsSeparated] in
/-- The relative group law on the glued scheme is represented by a group object over `S`. -/
def gluedGroup (L : RelativeGroupLaw S (toS H)) : GroupScheme S :=
  { X := Over.mk (toS H), grp := L.grpObjOverMk }

variable (e : SchemeHomOver (𝟙 S) (toS H))
  (he : ∀ {T : Scheme.{u}} {t : T ⟶ S} (x : SchemeHomOver t (toS H)),
    mulPts H hL x (unitPt H e t) = x)

include he in
theorem gluedGroup_mul {T : Scheme.{u}} {t : T ⟶ S} (a b : Over.mk t ⟶
    (gluedGroup H (relativeGroupLaw H hL e he)).X) :
    (a * b).left = (mulPts H hL (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)).1 := by
  exact congrArg Subtype.val ((relativeGroupLaw H hL e he).overHomToSchemeHomOver_mul t a b)

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
