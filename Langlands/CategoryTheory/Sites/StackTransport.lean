import Langlands.CategoryTheory.Sites.StackPullback
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Sites.CoverPreserving

universe t v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite
open CategoryTheory.Functor

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.StackPullback

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (G : C ⥤ D) (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v₃, u₃})
  [PreservesLimitsOfShape WalkingCospan G]
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

omit [PreservesLimitsOfShape WalkingCospan G] in
lemma ofObj_hom_reindex (M : F.obj (.mk (op (G.obj S))))
    {Y : C} (q : Y ⟶ S) {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q) :
    (((reindex G F).toDescentData f).obj M).hom q f₁ f₂ h₁ h₂ =
      ((F.toDescentData (fun i ↦ G.map (f i))).obj M).hom
        (G.map q) (G.map f₁) (G.map f₂)
        (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) := by
  change
    ((reindex G F).mapComp' (f i).op.toLoc f₁.op.toLoc q.op.toLoc _).inv.toNatTrans.app M ≫
      ((reindex G F).mapComp' (f j).op.toLoc f₂.op.toLoc q.op.toLoc _).hom.toNatTrans.app M = _
  rw [mapComp'_reindex G F f₁ (f i) q h₁, mapComp'_reindex G F f₂ (f j) q h₂]
  rfl

/-- The global-to-descent functors agree after passing to image pullbacks. -/
def toDescentDataPrimeIso :
    (reindex G F).toDescentData f ⋙
        Pseudofunctor.DescentData'.fromDescentDataFunctor (reindex G F) sq sq₃ ⋙
        toImageDescentDataPrime G F sq sq₃ ≅
      F.toDescentData (fun i ↦ G.map (f i)) ⋙
        Pseudofunctor.DescentData'.fromDescentDataFunctor F
          (fun i j ↦ mapChosenPullback G (sq i j))
          (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k)) :=
  NatIso.ofComponents
    (fun (M : F.obj (.mk (op (G.obj S)))) ↦
      Pseudofunctor.DescentData'.isoMk (fun i ↦ Iso.refl _) (by
      intro i j
      change
        (F.map (G.map (sq i j).p₁).op.toLoc).toFunctor.map (𝟙 _) ≫
          ((F.toDescentData (fun i ↦ G.map (f i))).obj M).hom
            (G.map (sq i j).p) (G.map (sq i j).p₁) (G.map (sq i j).p₂)
            (by rw [← G.map_comp, (sq i j).hp₁])
            (by rw [← G.map_comp, (sq i j).hp₂]) =
        (((reindex G F).toDescentData f).obj M).hom
          (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂ ≫
            (F.map (G.map (sq i j).p₂).op.toLoc).toFunctor.map (𝟙 _)
      exact
        (congrArg (fun a ↦ a ≫ _)
          ((F.map (G.map (sq i j).p₁).op.toLoc).toFunctor.map_id _)).trans
        ((Category.id_comp _).trans
          ((ofObj_hom_reindex G F M _ _ _ (sq i j).hp₁ (sq i j).hp₂).symm.trans
            ((Category.comp_id _).symm.trans
              (congrArg (fun a ↦ _ ≫ a)
                ((F.map (G.map (sq i j).p₂).op.toLoc).toFunctor.map_id _)).symm)))))
    (by
      intro M N φ
      ext i
      change (F.map (G.map (f i)).op.toLoc).toFunctor.map φ ≫ 𝟙 _ =
        𝟙 _ ≫ (F.map (G.map (f i)).op.toLoc).toFunctor.map φ
      simp)

/-- Compatibility of the equivalence of descent categories with global objects. -/
def toDescentDataIso :
    (reindex G F).toDescentData f ⋙ (descentDataEquivalence G F sq sq₃).functor ≅
      F.toDescentData (fun i ↦ G.map (f i)) :=
  isoWhiskerRight (toDescentDataPrimeIso G F sq sq₃)
      (Pseudofunctor.DescentData'.descentDataEquivalence F
        (fun i j ↦ mapChosenPullback G (sq i j))
        (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k))).functor ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (Pseudofunctor.DescentData'.descentDataEquivalence F
      (fun i j ↦ mapChosenPullback G (sq i j))
      (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k))).counitIso ≪≫
    Functor.rightUnitor _

include sq sq₃ in
/-- Equivalence of global-to-descent for the mapped family implies the same
property for the original family and reindexed pseudofunctor. -/
lemma isEquivalence_toDescentData_reindex
    [(F.toDescentData (fun i ↦ G.map (f i))).IsEquivalence] :
    ((reindex G F).toDescentData f).IsEquivalence := by
  have : ((reindex G F).toDescentData f ⋙
      (descentDataEquivalence G F sq sq₃).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (toDescentDataIso G F sq sq₃).symm
  exact Functor.isEquivalence_of_comp_right _ (descentDataEquivalence G F sq sq₃).functor

/-- Choose the usual categorical pullback. -/
def chosenPullback [HasPullbacks C] {A B S : C} (a : A ⟶ S) (b : B ⟶ S) :
    ChosenPullback a b where
  pullback := pullback a b
  p₁ := pullback.fst a b
  p₂ := pullback.snd a b
  condition := pullback.condition
  isLimit := pullbackIsPullback a b

/-- Choose a triple pullback compatible with any three chosen pair pullbacks. -/
def chosenPullback₃ [HasPullbacks C] {A B E S : C}
    {a : A ⟶ S} {b : B ⟶ S} {c : E ⟶ S}
    (h₁₂ : ChosenPullback a b) (h₂₃ : ChosenPullback b c)
    (h₁₃ : ChosenPullback a c) : ChosenPullback₃ h₁₂ h₂₃ h₁₃ := by
  let q := chosenPullback h₁₂.p₂ h₂₃.p₁
  refine
    { chosenPullback := q
      l := Classical.choice (ChosenPullback.LiftStruct.nonempty ?_ ?_) }
  · calc
      (q.p₁ ≫ h₁₂.p₁) ≫ a = q.p₁ ≫ h₁₂.p := by rw [Category.assoc, h₁₂.hp₁]
      _ = (q.p₁ ≫ h₁₂.p₂) ≫ b := by rw [Category.assoc, h₁₂.hp₂]
      _ = (q.p₂ ≫ h₂₃.p₁) ≫ b := by rw [q.condition]
      _ = q.p₂ ≫ h₂₃.p := by rw [Category.assoc, h₂₃.hp₁]
      _ = (q.p₂ ≫ h₂₃.p₂) ≫ c := by rw [Category.assoc, h₂₃.hp₂]
  · simp

/-- Pullback-preserving and cover-preserving reindexing transports stacks. -/
lemma isStack_reindex [HasPullbacks C]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (hG : CoverPreserving J K G) [F.IsStack K] :
    (reindex G F).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  rw [Pseudofunctor.isStackFor_iff]
  have hm :
      Sieve.ofArrows _ (fun (i : R.arrows.category) ↦ G.map i.obj.hom) ∈ K (G.obj S) := by
    rw [← Sieve.functorPushforward_ofArrows, Sieve.ofArrows_category]
    exact hG.cover_preserve hR
  let := F.isEquivalence_toDescentData _ hm
  exact isEquivalence_toDescentData_reindex G F
    (fun i j ↦ chosenPullback i.obj.hom j.obj.hom)
    (fun i j k ↦ chosenPullback₃ _ _ _)

end Langlands.CategoryTheory.StackPullback
