import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionGluing

/-! # The counit for the glued affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

instance affineChartWeilRestrictionOpenCover_preorder :
    Preorder (affineChartWeilRestrictionOpenCover A B Y).I₀ :=
  inferInstanceAs (Preorder Y.left.affineOpens)

/-- The actual chart cover is locally directed with its existing coordinate maps. -/
instance affineChartWeilRestrictionOpenCover_locallyDirected :
    (affineChartWeilRestrictionOpenCover A B Y).LocallyDirected where
  trans {U V} f := (affineChartWeilRestrictionDiagram A B Y).map f
  trans_id U := (affineChartWeilRestrictionDiagram A B Y).map_id U
  trans_comp f g := (affineChartWeilRestrictionDiagram A B Y).map_comp f g
  w f := colimit.w (affineChartWeilRestrictionDiagram A B Y) f
  directed {U V} x := by
    change Y.left.affineOpens at U V
    let i := (affineChartWeilRestrictionι A B Y U).left
    let j := (affineChartWeilRestrictionι A B Y V).left
    change (pullback i j).carrier at x
    have h : i (pullback.fst i j x) = j (pullback.snd i j x) := by
      have h' := congrArg (fun f : pullback i j ⟶
          (affineChartWeilRestriction A B Y).left => f x)
        (pullback.condition (f := i) (g := j))
      simpa only [Scheme.Hom.comp_apply] using h'
    obtain ⟨W, hU, hV, r, hr₁, hr₂⟩ :=
      (affineChartWeilRestrictionι_eq_iff A B Y _ _).mp h
    refine ⟨W, homOfLE hU, homOfLE hV, r, ?_⟩
    apply (pullback.fst i j).isOpenEmbedding.injective
    erw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hr₁

/-- Pull the actual directed chart cover back to the base-changed glued scheme. -/
def affineChartWeilRestrictionCounitCover :
    (ringBaseChange A B (affineChartWeilRestriction A B Y)).left.OpenCover :=
  (affineChartWeilRestrictionOpenCover A B Y).pullback₁
    (pullback.fst (affineChartWeilRestriction A B Y).hom (Spec.algebraMap A B))

instance affineChartWeilRestrictionCounitCover_preorder :
    Preorder (affineChartWeilRestrictionCounitCover A B Y).I₀ :=
  inferInstanceAs (Preorder Y.left.affineOpens)

instance affineChartWeilRestrictionCounitCover_locallyDirected :
    (affineChartWeilRestrictionCounitCover A B Y).LocallyDirected :=
  inferInstanceAs (Scheme.Cover.LocallyDirected
    ((affineChartWeilRestrictionOpenCover A B Y).pullback₁
    (pullback.fst (affineChartWeilRestriction A B Y).hom
      (Spec.algebraMap A B))))

/-- A pulled-back cover component, with its actual structure morphism to `Spec B`. -/
def affineChartWeilRestrictionCounitChart (U : Y.left.affineOpens) :
    Over (Spec (CommRingCat.of B)) :=
  Over.mk ((affineChartWeilRestrictionCounitCover A B Y).f U ≫
    (ringBaseChange A B (affineChartWeilRestriction A B Y)).hom)

/-- The canonical map from the pulled-back chart to the base change of the
original affine Weil-restriction chart. -/
def affineChartWeilRestrictionCounitChartMap (U : Y.left.affineOpens) :
    affineChartWeilRestrictionCounitChart A B Y U ⟶
      ringBaseChange A B (affineWeilRestriction A B (openOver B Y U.val)) := by
  let G := affineChartWeilRestriction A B Y
  let j := affineChartWeilRestrictionι A B Y U
  let a := Spec.algebraMap A B
  exact Over.homMk (pullback.lift
    (pullback.snd (pullback.fst G.hom a) j.left)
    (pullback.fst (pullback.fst G.hom a) j.left ≫ pullback.snd G.hom a)
    (by
      change pullback.snd (pullback.fst G.hom a) j.left ≫
          (affineWeilRestriction A B (openOver B Y U.val)).hom =
        (pullback.fst (pullback.fst G.hom a) j.left ≫
          pullback.snd G.hom a) ≫ a
      calc
        _ = (pullback.snd (pullback.fst G.hom a) j.left ≫ j.left) ≫ G.hom := by
          rw [Category.assoc, Over.w j]
        _ = (pullback.fst (pullback.fst G.hom a) j.left ≫
            pullback.fst G.hom a) ≫ G.hom := by rw [pullback.condition]
        _ = _ := by rw [Category.assoc, pullback.condition, ← Category.assoc])) (by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _)


/-- Transition morphisms of the pulled-back chart cover, over `Spec B`. -/
def affineChartWeilRestrictionCounitChartTransition
    {U V : Y.left.affineOpens} (h : U ≤ V) :
    affineChartWeilRestrictionCounitChart A B Y U ⟶
      affineChartWeilRestrictionCounitChart A B Y V :=
  Over.homMk ((affineChartWeilRestrictionCounitCover A B Y).trans (homOfLE h)) (by
    change _ ≫ ((affineChartWeilRestrictionCounitCover A B Y).f V ≫ _) = _
    rw [← Category.assoc, Scheme.Cover.trans_map]
    rfl)

/-- The two canonical base-change maps commute with every affine-open transition. -/
theorem affineChartWeilRestrictionCounitChartMap_natural
    {U V : Y.left.affineOpens} (h : U ≤ V) :
    affineChartWeilRestrictionCounitChartTransition A B Y h ≫
        affineChartWeilRestrictionCounitChartMap A B Y V =
      affineChartWeilRestrictionCounitChartMap A B Y U ≫
        (Over.pullback (Spec.algebraMap A B)).map
          (affineWeilRestrictionMap A B (openOverHomOfLE B Y h)) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullback.map _ _ _ _ (𝟙 _) _ (𝟙 _) (by simp) (by simp) ≫
        pullback.lift _ _ _) ≫ pullback.fst _ _ =
      (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _
    simp only [pullback.map, Category.assoc, Category.comp_id, pullback.lift_fst,
      pullback.lift_fst_assoc]
    erw [pullback.lift_snd]
    rfl
  · change (pullback.map _ _ _ _ (𝟙 _) _ (𝟙 _) (by simp) (by simp) ≫
        pullback.lift _ _ _) ≫ pullback.snd _ _ =
      (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _
    simp only [pullback.map, Category.assoc, Category.comp_id, pullback.lift_snd]
    erw [pullback.lift_fst_assoc]
    rfl

/-- The affine counit on one pulled-back chart, followed by its actual inclusion in `Y`. -/
def affineChartWeilRestrictionLocalCounit (U : Y.left.affineOpens) :
    affineChartWeilRestrictionCounitChart A B Y U ⟶ Y :=
  affineChartWeilRestrictionCounitChartMap A B Y U ≫
    affineWeilRestrictionCounit A B (openOver B Y U.val) ≫ openOverι B Y U.val

/-- The actual local counits agree on directed chart transitions. -/
theorem affineChartWeilRestrictionLocalCounit_natural
    {U V : Y.left.affineOpens} (h : U ≤ V) :
    affineChartWeilRestrictionCounitChartTransition A B Y h ≫
        affineChartWeilRestrictionLocalCounit A B Y V =
      affineChartWeilRestrictionLocalCounit A B Y U := by
  dsimp only [affineChartWeilRestrictionLocalCounit]
  rw [← Category.assoc, affineChartWeilRestrictionCounitChartMap_natural]
  simp only [Category.assoc]
  rw [← Category.assoc ((Over.pullback (Spec.algebraMap A B)).map _),
    affineWeilRestrictionCounit_natural]
  simp only [Category.assoc, openOverHomOfLE_ι]

/-- The actual global counit obtained by gluing the affine chart counits. -/
def affineChartWeilRestrictionCounit :
    ringBaseChange A B (affineChartWeilRestriction A B Y) ⟶ Y :=
  (affineChartWeilRestrictionCounitCover A B Y).glueMorphismsOverOfLocallyDirected
    (fun U => (affineChartWeilRestrictionLocalCounit A B Y U).left)
    (fun {_U _V} f => congrArg (fun g => g.left)
      (affineChartWeilRestrictionLocalCounit_natural A B Y (leOfHom f)))
    (fun U => Over.w (affineChartWeilRestrictionLocalCounit A B Y U))

/-- The canonical map in the opposite direction, from the exact affine chart
base change to the corresponding pulled-back cover component. -/
def affineChartWeilRestrictionCounitChartLift (U : Y.left.affineOpens) :
    ringBaseChange A B (affineWeilRestriction A B (openOver B Y U.val)) ⟶
      affineChartWeilRestrictionCounitChart A B Y U := by
  let G := affineChartWeilRestriction A B Y
  let C := affineWeilRestriction A B (openOver B Y U.val)
  let j := affineChartWeilRestrictionι A B Y U
  let a := Spec.algebraMap A B
  let F := Over.pullback a
  exact Over.homMk (pullback.lift (F.map j).left (pullback.fst C.hom a) (by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _)) (by
      change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ pullback.snd G.hom a) = _
      rw [pullback.lift_fst_assoc]
      exact Over.w (F.map j))

@[simp]
theorem affineChartWeilRestrictionCounitChartLift_cover (U : Y.left.affineOpens) :
    (affineChartWeilRestrictionCounitChartLift A B Y U).left ≫
        (affineChartWeilRestrictionCounitCover A B Y).f U =
      ((Over.pullback (Spec.algebraMap A B)).map
        (affineChartWeilRestrictionι A B Y U)).left := by
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  exact pullback.lift_fst _ _ _

@[simp]
theorem affineChartWeilRestrictionCounitChartLift_map (U : Y.left.affineOpens) :
    affineChartWeilRestrictionCounitChartLift A B Y U ≫
        affineChartWeilRestrictionCounitChartMap A B Y U = 𝟙 _ := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ =
      pullback.fst _ _
    rw [Category.assoc, pullback.lift_fst]
    erw [pullback.lift_snd]
  · change (pullback.lift _ _ _ ≫ pullback.lift _ _ _) ≫ pullback.snd _ _ =
      pullback.snd _ _
    rw [Category.assoc, pullback.lift_snd]
    erw [pullback.lift_fst_assoc]
    exact Over.w ((Over.pullback (Spec.algebraMap A B)).map
      (affineChartWeilRestrictionι A B Y U))

@[reassoc (attr := simp)]
theorem affineChartWeilRestrictionCounit_cover (U : Y.left.affineOpens) :
    (affineChartWeilRestrictionCounitCover A B Y).f U ≫
        (affineChartWeilRestrictionCounit A B Y).left =
      (affineChartWeilRestrictionLocalCounit A B Y U).left := by
  unfold affineChartWeilRestrictionCounit
  apply Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
  intro i j h
  exact congrArg (fun g => g.left)
    (affineChartWeilRestrictionLocalCounit_natural A B Y (leOfHom h))

/-- The global counit restricts to the existing affine counit on every exact
base-changed chart, followed by the chart's actual inclusion in `Y`. -/
@[reassoc (attr := simp)]
theorem affineChartWeilRestrictionCounit_chart (U : Y.left.affineOpens) :
    (Over.pullback (Spec.algebraMap A B)).map
        (affineChartWeilRestrictionι A B Y U) ≫
        affineChartWeilRestrictionCounit A B Y =
      affineWeilRestrictionCounit A B (openOver B Y U.val) ≫ openOverι B Y U.val := by
  apply Over.OverMorphism.ext
  change ((Over.pullback (Spec.algebraMap A B)).map
      (affineChartWeilRestrictionι A B Y U)).left ≫
        (affineChartWeilRestrictionCounit A B Y).left =
      (affineWeilRestrictionCounit A B (openOver B Y U.val) ≫ openOverι B Y U.val).left
  rw [← affineChartWeilRestrictionCounitChartLift_cover, Category.assoc,
    affineChartWeilRestrictionCounit_cover]
  change (affineChartWeilRestrictionCounitChartLift A B Y U).left ≫
      ((affineChartWeilRestrictionCounitChartMap A B Y U).left ≫ _) = _
  rw [← Category.assoc]
  change (affineChartWeilRestrictionCounitChartLift A B Y U ≫
    affineChartWeilRestrictionCounitChartMap A B Y U).left ≫ _ = _
  rw [affineChartWeilRestrictionCounitChartLift_map]
  exact Category.id_comp _

/-- The canonical comparison for the glued scheme on any actual test scheme. -/
def affineChartWeilRestrictionComparison
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    ringBaseChange A B T ⟶ Y :=
  (Over.pullback (Spec.algebraMap A B)).map p ≫
    affineChartWeilRestrictionCounit A B Y

/-- The canonical comparison is natural in every test scheme. -/
theorem affineChartWeilRestrictionComparison_natural
    {T U : Over (Spec (CommRingCat.of A))} (f : T ⟶ U)
    (p : U ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionComparison A B Y T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A B)).map f ≫
        affineChartWeilRestrictionComparison A B Y U p := by
  dsimp only [affineChartWeilRestrictionComparison]
  rw [Functor.map_comp, Category.assoc]

/-- On any test scheme, comparison on a chart is exactly the existing affine
comparison followed by the actual open inclusion. -/
theorem affineChartWeilRestrictionComparison_chart
    (T : Over (Spec (CommRingCat.of A))) (U : Y.left.affineOpens)
    (p : T ⟶ affineWeilRestriction A B (openOver B Y U.val)) :
    affineChartWeilRestrictionComparison A B Y T
        (p ≫ affineChartWeilRestrictionι A B Y U) =
      affineWeilRestrictionComparison A B (openOver B Y U.val) T p ≫ openOverι B Y U.val := by
  dsimp only [affineChartWeilRestrictionComparison, affineWeilRestrictionComparison]
  rw [Functor.map_comp, Category.assoc, affineChartWeilRestrictionCounit_chart,
    ← Category.assoc]

end Langlands.AlgebraicGeometry.PointTopology
