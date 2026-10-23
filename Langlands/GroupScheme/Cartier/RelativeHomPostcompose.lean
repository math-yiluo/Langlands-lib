import Langlands.GroupScheme.Cartier.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.Cartier
universe u
variable {S : Scheme.{u}}

/-- Postcomposition with the base change of a homomorphism in the target. -/
def postcompose (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') (T : Over S) : RelativeHom G H T →+ RelativeHom G H' T :=
  Preadditive.rightComp _ ((CommGroupScheme.baseChange T.hom).map ψ)

@[simp]
lemma postcompose_apply (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') (T : Over S) (χ : RelativeHom G H T) :
    postcompose G ψ T χ = χ ≫ (CommGroupScheme.baseChange T.hom).map ψ := rfl

lemma postcompose_id (G H : CommGroupScheme S) (T : Over S) (χ : RelativeHom G H T) :
    postcompose G (𝟙 H) T χ = χ := by
  rw [postcompose_apply, CategoryTheory.Functor.map_id, Category.comp_id]

lemma postcompose_comp (G : CommGroupScheme S) {H H' H'' : CommGroupScheme S}
    (ψ : H ⟶ H') (θ : H' ⟶ H'') (T : Over S) (χ : RelativeHom G H T) :
    postcompose G (ψ ≫ θ) T χ = postcompose G θ T (postcompose G ψ T χ) := by
  simp only [postcompose_apply, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Postcomposition commutes with actual pullback restriction. -/
lemma restrict_postcompose (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') {T T' : Over S} (a : T' ⟶ T) (χ : RelativeHom G H T) :
    restrict G H' a (postcompose G ψ T χ) = postcompose G ψ T' (restrict G H a χ) := by
  apply relativeHom_ext
  rw [restrict_fst]
  simp only [postcompose_apply, CommGroupScheme.hom_comp, Category.assoc,
    baseChange_map_fst, restrict_fst_assoc]

/-- The natural transformation induced by a homomorphism in the target. -/
def postcomposeNatTrans (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') : relativeHomFunctor G H ⟶ relativeHomFunctor G H' where
  app T := AddCommGrpCat.ofHom (postcompose G ψ T.unop)
  naturality T T' a := by
    ext χ
    exact (restrict_postcompose G ψ a.unop χ).symm

@[simp]
lemma postcomposeNatTrans_app_apply (G : CommGroupScheme S) {H H' : CommGroupScheme S}
    (ψ : H ⟶ H') (T : Over S) (χ : RelativeHom G H T) :
    (postcomposeNatTrans G ψ).app (op T) χ = postcompose G ψ T χ := rfl

lemma postcomposeNatTrans_id (G H : CommGroupScheme S) :
    postcomposeNatTrans G (𝟙 H) = 𝟙 (relativeHomFunctor G H) := by
  ext T χ
  exact postcompose_id G H T.unop χ

lemma postcomposeNatTrans_comp (G : CommGroupScheme S) {H H' H'' : CommGroupScheme S}
    (ψ : H ⟶ H') (θ : H' ⟶ H'') :
    postcomposeNatTrans G (ψ ≫ θ) = postcomposeNatTrans G ψ ≫ postcomposeNatTrans G θ := by
  ext T χ
  exact postcompose_comp G ψ θ T.unop χ

/-- Relative Hom is covariant in its target group scheme. -/
def relativeHomTargetFunctor (G : CommGroupScheme S) :
    CommGroupScheme S ⥤ (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj H := relativeHomFunctor G H
  map ψ := postcomposeNatTrans G ψ
  map_id H := postcomposeNatTrans_id G H
  map_comp ψ θ := postcomposeNatTrans_comp G ψ θ

/-- Source precomposition and target postcomposition commute. -/
lemma precompose_postcompose {G' G H H' : CommGroupScheme S}
    (φ : G' ⟶ G) (ψ : H ⟶ H') (T : Over S) (χ : RelativeHom G H T) :
    precompose H' φ T (postcompose G ψ T χ) =
      postcompose G' ψ T (precompose H φ T χ) := by
  simp only [precompose_apply, postcompose_apply, Category.assoc]

/-- The commuting source and target actions, as natural transformations. -/
lemma precomposeNatTrans_postcomposeNatTrans {G' G H H' : CommGroupScheme S}
    (φ : G' ⟶ G) (ψ : H ⟶ H') :
    postcomposeNatTrans G ψ ≫ precomposeNatTrans H' φ =
      precomposeNatTrans H φ ≫ postcomposeNatTrans G' ψ := by
  ext T χ
  exact precompose_postcompose φ ψ T.unop χ

end Langlands.GroupScheme.Cartier
