import Langlands.AlgebraicGeometry.Stacks.SchemeAtlas
import Langlands.CategoryTheory.Sites.PointFiberProduct
import Langlands.CategoryTheory.OverTotalRepresentable

/-! # Scheme representations of actual point fibres from product Hom presheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Stacks

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Langlands.CategoryTheory

variable {S : Scheme.{u}}
  (F : LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1})
  [∀ A : Over S, IsGroupoid (F.obj (.mk (op A)))]
  {U T : Over S}
  (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

/-- The full-slice product Hom presheaf on actual schemes over the product. -/
def productHomPresheaf : AlgebraicSpace.Presheaf (U ⨯ T).left :=
  (U ⨯ T).iteratedSliceBackward.op ⋙ PointFiberProduct.productHom F ξ η

/-- The actual representing scheme composed with the product's second projection. -/
abbrev pointFiberScheme (I : Over (U ⨯ T).left) : Over T.left :=
  Over.mk (I.hom ≫ (prod.snd : U ⨯ T ⟶ T).left)

private def underlyingRepresentation {T : Over S}
    {H : (Over T)ᵒᵖ ⥤ Type (u + 1)} {A : Over T}
    (e : H.RepresentableBy A) :
    (T.iteratedSliceBackward.op ⋙ H).RepresentableBy (T.iteratedSliceForward.obj A) where
  homEquiv {Z} :=
    (T.iteratedSliceEquiv.symm.toAdjunction.homEquiv Z A).symm.trans e.homEquiv
  homEquiv_comp g b :=
    (congrArg e.homEquiv
      (T.iteratedSliceEquiv.symm.toAdjunction.homEquiv_naturality_left_symm g b)).trans
        (e.homEquiv_comp _ _)

variable {I : Over (U ⨯ T).left}
  (e : (AlgebraicSpace.schemeYoneda (U ⨯ T).left).obj I ≅
    productHomPresheaf F ξ η)

/-- A supplied product Hom representation yields an actual representation of
all point-fibre sections on the full scheme slice. -/
def pointFiberRepresentation :
    (pointFiberPresheaf F ξ η).RepresentableBy (pointFiberScheme I) := by
  let e₁ := (Functor.RepresentableBy.equivUliftYonedaIso _ I).symm e
  let e₂ := Functor.RepresentableBy.ofEquivalence (U ⨯ T).iteratedSliceEquiv.symm e₁
  let e₃ : uliftYoneda.{u + 1}.obj ((U ⨯ T).iteratedSliceBackward.obj I) ≅
      PointFiberProduct.productHom F ξ η :=
    (Functor.RepresentableBy.equivUliftYonedaIso _ _) e₂
  let e₄ := SlicePresheafTotal.representationIso (PointFiberProduct.productOver U T) _ e₃
  let e₅ := e₄ ≪≫ (PointFiberProduct.presheafIso F ξ η).symm
  exact underlyingRepresentation
    ((Functor.RepresentableBy.equivUliftYonedaIso _ _).symm e₅)

/-- The representation is a natural isomorphism on every scheme over the test base. -/
def pointFiberSchemeIso :
    (AlgebraicSpace.schemeYoneda T.left).obj (pointFiberScheme I) ≅
      pointFiberPresheaf F ξ η :=
  (Functor.RepresentableBy.equivUliftYonedaIso _ _) (pointFiberRepresentation F ξ η e)

end Langlands.AlgebraicGeometry.Stacks
