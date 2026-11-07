import Langlands.AlgebraicGeometry.IntegralSchemePushoutCompatibleCharts
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Constructing the global pushout from compatible affine models -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Affine locally ringed pushout models on a covering family of compatible opens. -/
structure CompatibleAffinePushoutAtlas {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) where
  Index : Type u
  leftOpen : Index → X.Opens
  rightOpen : Index → Y.Opens
  compatible : ∀ t, i ⁻¹ᵁ leftOpen t = j ⁻¹ᵁ rightOpen t
  covers_left : ∀ x : X, ∃ t, x ∈ leftOpen t
  covers_right : ∀ y : Y, ∃ t, y ∈ rightOpen t
  model : Index → Scheme.{u}
  affine : ∀ t, IsAffine (model t)
  inl : ∀ t, (leftOpen t).toScheme ⟶ model t
  inr : ∀ t, (rightOpen t).toScheme ⟶ model t
  isPushout : ∀ t, IsPushout (CompatibleOpen.leftMap i (leftOpen t)).toLRSHom
    (CompatibleOpen.rightMap i j (leftOpen t) (rightOpen t) (compatible t)).toLRSHom
    (inl t).toLRSHom (inr t).toLRSHom

namespace CompatibleAffinePushoutAtlas

attribute [instance] affine

variable {X Y Z : Scheme.{u}} {i : Z ⟶ X} {j : Z ⟶ Y}
    (D : CompatibleAffinePushoutAtlas i j)

/-- The canonical pushout in locally ringed spaces. -/
abbrev space (_D : CompatibleAffinePushoutAtlas i j) : LocallyRingedSpace.{u} := pushout i.toLRSHom j.toLRSHom

/-- The canonical locally ringed pushout square. -/
lemma space_isPushout : IsPushout i.toLRSHom j.toLRSHom
    (pushout.inl i.toLRSHom j.toLRSHom) (pushout.inr i.toLRSHom j.toLRSHom) :=
  .of_hasPushout _ _

/-- An affine model maps to the canonical locally ringed pushout. -/
def spaceChart (t : D.Index) : (D.model t).toLocallyRingedSpace ⟶ D.space :=
  CompatibleOpen.comparison i j (D.leftOpen t) (D.rightOpen t) (D.compatible t)
    (D.isPushout t) (space_isPushout (i := i) (j := j))

instance spaceChart_isOpenImmersion (t : D.Index) :
    LocallyRingedSpace.IsOpenImmersion (D.spaceChart t) :=
  (CompatibleOpen.comparison_isOpenImmersion_and_range i j
    (D.leftOpen t) (D.rightOpen t) (D.compatible t)
    (D.isPushout t) (space_isPushout (i := i) (j := j))).1

lemma spaceChart_range_left (t : D.Index) :
    (D.leftOpen t : Set X) = (pushout.inl i.toLRSHom j.toLRSHom).base ⁻¹'
      Set.range (D.spaceChart t).base :=
  (CompatibleOpen.comparison_isOpenImmersion_and_range i j
    (D.leftOpen t) (D.rightOpen t) (D.compatible t)
    (D.isPushout t) (space_isPushout (i := i) (j := j))).2.1

lemma spaceChart_range_right (t : D.Index) :
    (D.rightOpen t : Set Y) = (pushout.inr i.toLRSHom j.toLRSHom).base ⁻¹'
      Set.range (D.spaceChart t).base :=
  (CompatibleOpen.comparison_isOpenImmersion_and_range i j
    (D.leftOpen t) (D.rightOpen t) (D.compatible t)
    (D.isPushout t) (space_isPushout (i := i) (j := j))).2.2

/-- The affine models cover every point of the locally ringed pushout. -/
lemma spaceChart_covers (x : D.space) : ∃ t, x ∈ Set.range (D.spaceChart t).base := by
  have h := isColimitOfPreserves LocallyRingedSpace.forgetToSheafedSpace
    (space_isPushout (i := i) (j := j)).isColimit
  obtain ⟨t, y, hy⟩ := SheafedSpace.isColimit_exists_rep _ h x
  rcases t with _ | _ | _
  · change Z at y
    change (pushout.inl i.toLRSHom j.toLRSHom).base (i y) = x at hy
    obtain ⟨s, hs⟩ := D.covers_left (i y)
    refine ⟨s, hy ▸ ?_⟩
    exact (Set.ext_iff.mp (D.spaceChart_range_left s) (i y)).mp hs
  · change X at y
    change (pushout.inl i.toLRSHom j.toLRSHom).base y = x at hy
    obtain ⟨s, hs⟩ := D.covers_left y
    refine ⟨s, hy ▸ ?_⟩
    exact (Set.ext_iff.mp (D.spaceChart_range_left s) y).mp hs
  · change Y at y
    change (pushout.inr i.toLRSHom j.toLRSHom).base y = x at hy
    obtain ⟨s, hs⟩ := D.covers_right y
    refine ⟨s, hy ▸ ?_⟩
    exact (Set.ext_iff.mp (D.spaceChart_range_right s) y).mp hs

/-- The locally ringed pushout is locally affine, hence a scheme. -/
def scheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme D.space (by
    intro x
    obtain ⟨t, y, hy⟩ := D.spaceChart_covers x
    let e := (D.model t).isoSpec
    refine ⟨Γ(D.model t, ⊤), e.inv.toLRSHom ≫ D.spaceChart t, ?_, inferInstance⟩
    refine ⟨e.hom y, ?_⟩
    change (D.spaceChart t).base (e.inv (e.hom y)) = x
    have he : e.inv (e.hom y) = y := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rw [he]
    exact hy)

/-- The first global scheme cocone leg. -/
def left : X ⟶ D.scheme := ⟨pushout.inl i.toLRSHom j.toLRSHom⟩

/-- The second global scheme cocone leg. -/
def right : Y ⟶ D.scheme := ⟨pushout.inr i.toLRSHom j.toLRSHom⟩

/-- The global scheme square is a pushout. -/
lemma isPushout_global : IsPushout i j D.left D.right :=
  IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace
    (space_isPushout (i := i) (j := j))

/-- The affine charts of the resulting scheme. -/
def chart (t : D.Index) : D.model t ⟶ D.scheme := ⟨D.spaceChart t⟩

instance chart_isOpenImmersion (t : D.Index) : IsOpenImmersion (D.chart t) :=
  D.spaceChart_isOpenImmersion t

@[reassoc (attr := simp)]
lemma inl_chart (t : D.Index) : D.inl t ≫ D.chart t = (D.leftOpen t).ι ≫ D.left := by
  apply Scheme.Hom.ext'
  exact (D.isPushout t).inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_chart (t : D.Index) : D.inr t ≫ D.chart t = (D.rightOpen t).ι ≫ D.right := by
  apply Scheme.Hom.ext'
  exact (D.isPushout t).inr_desc _ _ _

lemma chart_preimage_left (t : D.Index) : D.left ⁻¹ᵁ (D.chart t).opensRange = D.leftOpen t :=
  Opens.ext (D.spaceChart_range_left t).symm

lemma chart_preimage_right (t : D.Index) : D.right ⁻¹ᵁ (D.chart t).opensRange = D.rightOpen t :=
  Opens.ext (D.spaceChart_range_right t).symm

/-- The prescribed left open is the pullback of an affine chart. -/
lemma isPullback_left (t : D.Index) :
    IsPullback (D.leftOpen t).ι (D.inl t) D.left (D.chart t) :=
  (IsOpenImmersion.isPullback _ _ _ _ (D.inl_chart t).symm
    (by rw [D.chart_preimage_left, Scheme.Opens.opensRange_ι])).flip

/-- The prescribed right open is the pullback of an affine chart. -/
lemma isPullback_right (t : D.Index) :
    IsPullback (D.rightOpen t).ι (D.inr t) D.right (D.chart t) :=
  (IsOpenImmersion.isPullback _ _ _ _ (D.inr_chart t).symm
    (by rw [D.chart_preimage_right, Scheme.Opens.opensRange_ι])).flip

/-- The family of model charts is an open cover of the global scheme. -/
def openCover : D.scheme.OpenCover where
  I₀ := D.Index
  X := D.model
  f := D.chart
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨D.spaceChart_covers, inferInstance⟩

end CompatibleAffinePushoutAtlas

end Langlands.AlgebraicGeometry.IntegralSchemePushout
