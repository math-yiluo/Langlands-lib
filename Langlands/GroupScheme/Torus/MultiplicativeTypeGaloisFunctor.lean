import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor

/-! # The finitely generated Galois character functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SplitMultiplicativeType

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual finitely generated character module, with its canonical action. -/
def characterAction (T : SplitMultiplicativeType k L) :
    Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L) where
  V := characterModule k L T
  ρ := (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
    ((ModuleCat.endRingEquiv (characterModule k L T).obj).symm.toMonoidHom.comp
      (characterLattice.galoisRepresentation k L T.obj))

@[simp]
theorem characterAction_ρ_apply (T : SplitMultiplicativeType k L)
    (σ : L ≃ₐ[k] L)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T.obj)) :
    ((characterAction k L T).ρ σ).hom.hom χ =
      characterLattice.galoisRepresentation k L T.obj σ χ := rfl

/-- Actual character pullback, bundled between the finitely generated actions. -/
def characterPullback {H G : SplitMultiplicativeType k L} (f : H ⟶ G) :
    characterAction k L G ⟶ characterAction k L H where
  hom := InducedCategory.homMk
    (ModuleCat.ofHom (characterLattice.galoisPullback k L f.hom).hom.toLinearMap)
  comm σ := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    exact (characterLattice.galoisRepresentation_naturality k L f.hom σ χ).symm

@[simp]
theorem characterPullback_apply {H G : SplitMultiplicativeType k L} (f : H ⟶ G)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj G.obj)) :
    (characterPullback k L f).hom.hom.hom χ =
      (CommGroupScheme.baseChange (algebraBaseMap k L)).map f.hom ≫ χ := rfl

/-- The contravariant actual character functor with finitely generated integral target. -/
def characterFunctor :
    (SplitMultiplicativeType k L)ᵒᵖ ⥤
      Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L) where
  obj T := characterAction k L T.unop
  map f := characterPullback k L f.unop
  map_id T := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    change (CommGroupScheme.baseChange (algebraBaseMap k L)).map (𝟙 T.unop.obj) ≫ χ = χ
    simp
  map_comp f g := by
    apply Action.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro χ
    change (CommGroupScheme.baseChange (algebraBaseMap k L)).map
        (g.unop.hom ≫ f.unop.hom) ≫ χ =
      (CommGroupScheme.baseChange (algebraBaseMap k L)).map g.unop.hom ≫
        ((CommGroupScheme.baseChange (algebraBaseMap k L)).map f.unop.hom ≫ χ)
    simp only [Functor.map_comp, Category.assoc]

@[simp]
theorem characterFunctor_map_apply
    {H G : (SplitMultiplicativeType k L)ᵒᵖ} (f : H ⟶ G)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj H.unop.obj)) :
    ((characterFunctor k L).map f).hom.hom.hom χ =
      (CommGroupScheme.baseChange (algebraBaseMap k L)).map f.unop.hom ≫ χ := rfl

/-- Forget finite generation using the existing action and representation functors. -/
def forgetCharacterFiniteness :
    Action (FGModuleCat.{u} ℤ) (L ≃ₐ[k] L) ⥤ Rep.{u} ℤ (L ≃ₐ[k] L) :=
  (forget₂ (FGModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapAction (L ≃ₐ[k] L) ⋙
    Rep.ActionToRep ℤ (L ≃ₐ[k] L)

/-- Forgetting finite generation recovers the published unrestricted character functor. -/
theorem characterFunctor_forget :
    characterFunctor k L ⋙ forgetCharacterFiniteness k L =
      (inclusion k L).op ⋙ characterLattice.galoisFunctor k L := rfl

end Langlands.GroupScheme.SplitMultiplicativeType
