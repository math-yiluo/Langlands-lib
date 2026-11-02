import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

universe t v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.CategoryTheory.StackPullback

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (G : C ⥤ D) (F : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{v₃, u₃})

abbrev reindex : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v₃, u₃} :=
  G.op.toPseudofunctor.comp F

lemma map_reindex {X Y : C} (f : X ⟶ Y) :
    (reindex G F).map f.op.toLoc = F.map (G.map f).op.toLoc := rfl

set_option backward.isDefEq.respectTransparency false in
lemma mapComp'_reindex {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    (reindex G F).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc (by aesop) =
      F.mapComp' (G.map g).op.toLoc (G.map f).op.toLoc (G.map fg).op.toLoc
        (by have := congrArg G.map h; aesop) := by
  simp only [Pseudofunctor.mapComp', Pseudofunctor.comp_mapComp,
    Functor.toPseudofunctor_mapComp]
  dsimp only [Quiver.Hom.toLoc]
  simp only [PrelaxFunctor.map₂Iso_eqToIso]
  simp only [Iso.ext_iff, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc]
  congr 1

lemma pullHom_reindex {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (op (G.obj X₁)))} {M₂ : F.obj (.mk (op (G.obj X₂)))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map (G.map f₁).op.toLoc).toFunctor.obj M₁ ⟶
      (F.map (G.map f₂).op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom (F := reindex G F) φ g gf₁ gf₂ h₁ h₂ =
      pullHom (F := F) φ (G.map g) (G.map gf₁) (G.map gf₂)
        (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) := by
  simp only [pullHom]
  rw [mapComp'_reindex G F g f₁ gf₁ h₁, mapComp'_reindex G F g f₂ gf₂ h₂]
  rfl

variable [PreservesLimitsOfShape WalkingCospan G]

/-- A pullback square and its structure maps transported through `G`. -/
def mapChosenPullback {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    (sq : ChosenPullback f₁ f₂) : ChosenPullback (G.map f₁) (G.map f₂) where
  pullback := G.obj sq.pullback
  p₁ := G.map sq.p₁
  p₂ := G.map sq.p₂
  condition := by rw [← G.map_comp, ← G.map_comp, sq.condition]
  isLimit := (sq.isPullback.map G).isLimit
  p := G.map sq.p
  hp₁ := by rw [← G.map_comp, sq.hp₁]

/-- The corresponding transport of a chosen threefold pullback. -/
def mapChosenPullback₃ {X₁ X₂ X₃ S : C}
    {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    {sq₁₂ : ChosenPullback f₁ f₂} {sq₂₃ : ChosenPullback f₂ f₃}
    {sq₁₃ : ChosenPullback f₁ f₃} (sq₃ : ChosenPullback₃ sq₁₂ sq₂₃ sq₁₃) :
    ChosenPullback₃ (mapChosenPullback G sq₁₂) (mapChosenPullback G sq₂₃)
      (mapChosenPullback G sq₁₃) where
  chosenPullback := mapChosenPullback G sq₃.chosenPullback
  p := G.map sq₃.p
  p₁ := G.map sq₃.p₁
  p₃ := G.map sq₃.p₃
  l :=
    { f := G.map sq₃.l.f
      f_p₁ := by dsimp [mapChosenPullback]; rw [← G.map_comp, sq₃.l.f_p₁]
      f_p₂ := by dsimp [mapChosenPullback]; rw [← G.map_comp, sq₃.l.f_p₂]
      f_p := by dsimp [mapChosenPullback]; rw [← G.map_comp, sq₃.l.f_p] }
  hp₁ := by dsimp [mapChosenPullback]; rw [← G.map_comp, sq₃.hp₁]
  hp₃ := by dsimp [mapChosenPullback]; rw [← G.map_comp, sq₃.hp₃]

variable {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))

lemma pullHom'_reindex {obj obj' : ∀ i, F.obj (.mk (op (G.obj (X i))))}
    (hom : ∀ i j, (F.map (G.map (sq i j).p₁).op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (G.map (sq i j).p₂).op.toLoc).toFunctor.obj (obj' j))
    {Y : C} (q : Y ⟶ S) {i j : ι} (f₁ : Y ⟶ X i) (f₂ : Y ⟶ X j)
    (h₁ : f₁ ≫ f i = q) (h₂ : f₂ ≫ f j = q) :
    Pseudofunctor.DescentData'.pullHom' (F := reindex G F) (sq := sq) hom q f₁ f₂ h₁ h₂ =
      Pseudofunctor.DescentData'.pullHom' (F := F)
        (sq := fun i j ↦ mapChosenPullback G (sq i j)) hom
          (G.map q) (G.map f₁) (G.map f₂)
            (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂]) := by
  rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom (F := F)
    (sq := fun i j ↦ mapChosenPullback G (sq i j)) hom (G.map q) (G.map f₁) (G.map f₂)
    (G.map ((sq i j).isPullback.lift f₁ f₂ (by rw [h₁, h₂])))
    (by rw [← G.map_comp, h₁]) (by rw [← G.map_comp, h₂])
    (by dsimp [mapChosenPullback]; rw [← G.map_comp, IsPullback.lift_fst])
    (by dsimp [mapChosenPullback]; rw [← G.map_comp, IsPullback.lift_snd])]
  exact pullHom_reindex _ _ _ _ _ _ _ _

/-- Read descent data for the reindexed pseudofunctor over the image pullbacks. -/
@[simps]
def toImageDescentDataPrime :
    (reindex G F).DescentData' sq sq₃ ⥤
      F.DescentData' (fun i j ↦ mapChosenPullback G (sq i j))
        (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k)) where
  obj D :=
    { obj := D.obj
      hom := D.hom
      pullHom'_hom_self i := by
        have h := D.pullHom'_hom_self i
        simp only [pullHom'_reindex, map_reindex] at h ⊢
        convert h using 1 <;> first
        | simp only [G.map_id]
        | (congr 1 <;> simp only [G.map_id])
        all_goals exact proof_irrel_heq _ _
      pullHom'_hom_comp i j k := by
        have h := D.pullHom'_hom_comp i j k
        simp only [pullHom'_reindex] at h ⊢
        dsimp [reindex, mapChosenPullback₃, mapChosenPullback, ChosenPullback₃.p₂] at h ⊢
        exact h }
  map φ :=
    { hom := φ.hom
      comm := φ.comm }

/-- Read descent data on the image pullbacks as descent data for the reindexing. -/
@[simps]
def fromImageDescentDataPrime :
    F.DescentData' (fun i j ↦ mapChosenPullback G (sq i j))
      (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k)) ⥤
        (reindex G F).DescentData' sq sq₃ where
  obj D :=
    { obj := D.obj
      hom := D.hom
      pullHom'_hom_self i := by
        have h := D.pullHom'_hom_self i
        simp only [pullHom'_reindex, map_reindex] at h ⊢
        convert h using 1 <;> first
        | simp only [G.map_id]
        | (congr 1 <;> simp only [G.map_id])
        all_goals exact proof_irrel_heq _ _
      pullHom'_hom_comp i j k := by
        have h := D.pullHom'_hom_comp i j k
        simp only [pullHom'_reindex] at h ⊢
        dsimp [reindex, mapChosenPullback₃, mapChosenPullback, ChosenPullback₃.p₂] at h ⊢
        exact h }
  map φ :=
    { hom := φ.hom
      comm := φ.comm }

/-- Pullback-preserving reindexing does not change the category of descent data. -/
def imageDescentDataPrimeEquivalence :
    (reindex G F).DescentData' sq sq₃ ≌
      F.DescentData' (fun i j ↦ mapChosenPullback G (sq i j))
        (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k)) where
  functor := toImageDescentDataPrime G F sq sq₃
  inverse := fromImageDescentDataPrime G F sq sq₃
  unitIso := NatIso.ofComponents (fun _ ↦ Pseudofunctor.DescentData'.isoMk (fun _ ↦ Iso.refl _))
  counitIso := NatIso.ofComponents
    (fun _ ↦ Pseudofunctor.DescentData'.isoMk (fun _ ↦ Iso.refl _))

/-- Comparison of unrestricted descent data under pullback-preserving reindexing. -/
def descentDataEquivalence :
    (reindex G F).DescentData f ≌ F.DescentData (fun i ↦ G.map (f i)) :=
  (Pseudofunctor.DescentData'.descentDataEquivalence (reindex G F) sq sq₃).symm |>.trans
    ((imageDescentDataPrimeEquivalence G F sq sq₃).trans
      (Pseudofunctor.DescentData'.descentDataEquivalence F
        (fun i j ↦ mapChosenPullback G (sq i j))
        (fun i j k ↦ mapChosenPullback₃ G (sq₃ i j k))))

end Langlands.CategoryTheory.StackPullback
