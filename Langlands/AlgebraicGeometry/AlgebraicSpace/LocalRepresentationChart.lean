import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct

/-! # Local representations as global charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace LocalRepresentation

variable {B U : Scheme.{u}} {F : Presheaf B} (j : U ⟶ B) (H : Over U)
    (e : (schemeYoneda U).obj H ≅ (Over.map j).op ⋙ F)

/-- The global chart supplied by a representation after restriction to `U`. -/
def chart : (schemeYoneda B).obj ((Over.map j).obj H) ⟶ F :=
  uliftYonedaEquiv.{u + 1}.symm (e.hom.app (op H) ⟨𝟙 H⟩)

lemma chart_app_map {Z : Over U} (k : Z ⟶ H) :
    (chart j H e).app (op ((Over.map j).obj Z)) ⟨(Over.map j).map k⟩ =
      e.hom.app (op Z) ⟨k⟩ := by
  change F.map ((Over.map j).map k).op (e.hom.app (op H) ⟨𝟙 H⟩) = _
  simpa using (e.hom.naturality_apply k.op ⟨𝟙 H⟩).symm

/-- A local representation maps to the product with the represented base chart. -/
def chartToProduct :
    (schemeYoneda B).obj ((Over.map j).obj H) ⟶ extProd F (Over.mk j) :=
  FunctorToTypes.prod.lift (chart j H e)
    ((schemeYoneda B).map (Over.homMk H.hom))

lemma chartToProduct_bijective (Z : Over B) :
    Function.Bijective ((chartToProduct j H e).app (op Z)) := by
  constructor
  · intro a b hab
    have h₁ := congrArg Prod.fst hab
    have h₂ := congrArg (fun z ↦ z.2.down.left) hab
    change (chart j H e).app (op Z) a = (chart j H e).app (op Z) b at h₁
    change a.down.left ≫ H.hom = b.down.left ≫ H.hom at h₂
    let Z' : Over U := Over.mk (a.down.left ≫ H.hom)
    let d : (Over.map j).obj Z' ≅ Z :=
      Over.isoMk (Iso.refl _) (by simpa [Z'] using a.down.w.symm)
    let a' : Z' ⟶ H := Over.homMk a.down.left
    let b' : Z' ⟶ H := Over.homMk b.down.left (by exact h₂.symm)
    have ha : d.hom ≫ a.down = (Over.map j).map a' := by
      apply Over.OverMorphism.ext
      change 𝟙 _ ≫ a.down.left = a.down.left
      exact Category.id_comp _
    have hb : d.hom ≫ b.down = (Over.map j).map b' := by
      apply Over.OverMorphism.ext
      change 𝟙 _ ≫ b.down.left = b.down.left
      exact Category.id_comp _
    have he : e.hom.app (op Z') ⟨a'⟩ = e.hom.app (op Z') ⟨b'⟩ := by
      rw [← chart_app_map, ← chart_app_map]
      have hn := (chart j H e).naturality_apply d.hom.op a
      have hn' := (chart j H e).naturality_apply d.hom.op b
      change (chart j H e).app _ ⟨d.hom ≫ a.down⟩ = _ at hn
      change (chart j H e).app _ ⟨d.hom ≫ b.down⟩ = _ at hn'
      rw [ha] at hn
      rw [hb] at hn'
      exact hn.trans ((congrArg (F.map d.hom.op) h₁).trans hn'.symm)
    have hk : a' = b' :=
      congrArg ULift.down ((ConcreteCategory.bijective_of_isIso (e.hom.app (op Z'))).injective he)
    apply ULift.ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.left) hk
  · rintro ⟨x, α⟩
    let Z' : Over U := Over.mk α.down.left
    let d : (Over.map j).obj Z' ≅ Z :=
      Over.isoMk (Iso.refl _) (by simpa [Z'] using α.down.w.symm)
    let k : Z' ⟶ H := (e.inv.app (op Z') (F.map d.hom.op x)).down
    refine ⟨⟨d.inv ≫ (Over.map j).map k⟩, ?_⟩
    apply Prod.ext
    · change (chart j H e).app _ ⟨d.inv ≫ (Over.map j).map k⟩ = x
      have hn := (chart j H e).naturality_apply d.inv.op ⟨(Over.map j).map k⟩
      change (chart j H e).app _ ⟨d.inv ≫ (Over.map j).map k⟩ = _ at hn
      rw [hn]
      rw [chart_app_map]
      change F.map d.inv.op (e.hom.app _ (e.inv.app _ (F.map d.hom.op x))) = x
      simp only [Iso.inv_hom_id_app_apply]
      rw [← F.map_comp_apply]
      simp [← op_comp]
    · apply ULift.ext
      apply Over.OverMorphism.ext
      change (𝟙 _ ≫ k.left) ≫ H.hom = α.down.left
      simp [Z']

/-- A representation after arbitrary base restriction represents the product
with that base chart, on the full original slice. -/
def chartProductIso :
    (schemeYoneda B).obj ((Over.map j).obj H) ≅ extProd F (Over.mk j) := by
  letI : IsIso (chartToProduct j H e) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [isIso_iff_bijective]
    exact chartToProduct_bijective j H e Z.unop
  exact asIso (chartToProduct j H e)

@[reassoc (attr := simp)]
lemma chartProductIso_hom_fst :
    (chartProductIso j H e).hom ≫ extProd.fst = chart j H e := rfl

/-- A local representation over an open base chart gives an open global chart. -/
theorem chart_isOpenImmersion [_root_.AlgebraicGeometry.IsOpenImmersion j] :
    IsOpenImmersion (chart j H e) := by
  rw [← chartProductIso_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget B)).relative (schemeYoneda B)) _ _).mpr
    (extProd.relative_fst (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Λ := Over.mk j) (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion j)))

end LocalRepresentation

end Langlands.AlgebraicGeometry.AlgebraicSpace
