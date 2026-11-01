import Langlands.Shimura.Coefficients.EtaleTorsorPullback
import Langlands.Geometry.EtalePullback

/-! # Natural geometric product comparison for etale restriction -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]

/-- The first fiber projection as a morphism of etale objects over X. -/
def etalePullbackProjection (V : X.Etale) :
    (EtalePullback.siteMap f).obj ((etaleObjectPullback f).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom f) (by
    exact pullback.condition)

/-- The first fiber projection is natural in the original cover. -/
@[reassoc (attr := simp)] theorem etalePullbackProjection_natural
    {V V' : X.Etale} (a : V ⟶ V') :
    (EtalePullback.siteMap f).map ((etaleObjectPullback f).map a) ≫
        etalePullbackProjection f V' = etalePullbackProjection f V ≫ a := by
  apply MorphismProperty.Over.Hom.ext
  change ((etaleObjectPullback f).map a).left ≫ pullback.fst V'.hom f =
    pullback.fst V.hom f ≫ a.left
  simp [etaleObjectPullback]

/-- The canonical map from the product over Z to the product over X. -/
def etaleProductPullbackHom (V : X.Etale) (U : Z.Etale) :
    (EtalePullback.siteMap f).obj (((etaleObjectPullback f).obj V) ⨯ U) ⟶
      V ⨯ (EtalePullback.siteMap f).obj U :=
  prod.lift
    ((EtalePullback.siteMap f).map prod.fst ≫ etalePullbackProjection f V)
    ((EtalePullback.siteMap f).map prod.snd)

/-- The product over X has the structural map to Z supplied by U. -/
def etaleProductOverBase (V : X.Etale) (U : Z.Etale) : Z.Etale :=
  Scheme.Etale.mk ((prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left ≫ U.hom)

/-- First coordinate of the inverse product comparison. -/
def etaleProductOverBaseFst (V : X.Etale) (U : Z.Etale) :
    etaleProductOverBase f V U ⟶ (etaleObjectPullback f).obj V :=
  MorphismProperty.Over.homMk
    (pullback.lift (prod.fst : V ⨯ (EtalePullback.siteMap f).obj U ⟶ V).left
      ((prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left ≫ U.hom) (by
        rw [Category.assoc]
        exact (MorphismProperty.Over.w prod.fst).trans
          (MorphismProperty.Over.w prod.snd).symm))

/-- Second coordinate of the inverse product comparison. -/
def etaleProductOverBaseSnd (V : X.Etale) (U : Z.Etale) :
    etaleProductOverBase f V U ⟶ U :=
  MorphismProperty.Over.homMk
    (prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left

/-- Inverse map constructed by the two product coordinates over Z. -/
def etaleProductPullbackInv (V : X.Etale) (U : Z.Etale) :
    V ⨯ (EtalePullback.siteMap f).obj U ⟶
      (EtalePullback.siteMap f).obj (((etaleObjectPullback f).obj V) ⨯ U) :=
  MorphismProperty.Over.homMk
    (prod.lift (etaleProductOverBaseFst f V U) (etaleProductOverBaseSnd f V U)).left
    (by
      have h := MorphismProperty.Over.w
        (prod.lift (etaleProductOverBaseFst f V U) (etaleProductOverBaseSnd f V U))
      change (prod.lift (etaleProductOverBaseFst f V U)
        (etaleProductOverBaseSnd f V U)).left ≫
        ((((etaleObjectPullback f).obj V) ⨯ U).hom ≫ f) = _
      erw [← Category.assoc, h]
      change ((prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left ≫
        U.hom) ≫ f = _
      rw [Category.assoc]
      exact MorphismProperty.Over.w
        (prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _))

/-- The comparison has the original first fiber coordinate. -/
@[reassoc (attr := simp)] theorem etaleProductPullbackHom_fst
    (V : X.Etale) (U : Z.Etale) :
    (etaleProductPullbackHom f V U).left ≫
        (prod.fst : V ⨯ (EtalePullback.siteMap f).obj U ⟶ V).left =
      (prod.fst : ((etaleObjectPullback f).obj V) ⨯ U ⟶ _).left ≫
        pullback.fst V.hom f := by
  change (etaleProductPullbackHom f V U ≫ prod.fst).left = _
  rw [etaleProductPullbackHom, prod.lift_fst]
  rfl

/-- The comparison retains the second product coordinate. -/
@[reassoc (attr := simp)] theorem etaleProductPullbackHom_snd
    (V : X.Etale) (U : Z.Etale) :
    (etaleProductPullbackHom f V U).left ≫
        (prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left =
      (prod.snd : ((etaleObjectPullback f).obj V) ⨯ U ⟶ U).left := by
  change (etaleProductPullbackHom f V U ≫ prod.snd).left = _
  rw [etaleProductPullbackHom, prod.lift_snd]
  rfl

/-- The inverse has its constructed first product coordinate. -/
@[reassoc (attr := simp)] theorem etaleProductPullbackInv_fst
    (V : X.Etale) (U : Z.Etale) :
    (etaleProductPullbackInv f V U).left ≫
        (prod.fst : ((etaleObjectPullback f).obj V) ⨯ U ⟶ _).left =
      (etaleProductOverBaseFst f V U).left := by
  exact congrArg
    (fun k : etaleProductOverBase f V U ⟶ (etaleObjectPullback f).obj V => k.left)
    (prod.lift_fst (etaleProductOverBaseFst f V U) (etaleProductOverBaseSnd f V U))

/-- The inverse retains its second product coordinate. -/
@[reassoc (attr := simp)] theorem etaleProductPullbackInv_snd
    (V : X.Etale) (U : Z.Etale) :
    (etaleProductPullbackInv f V U).left ≫
        (prod.snd : ((etaleObjectPullback f).obj V) ⨯ U ⟶ U).left =
      (prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left := by
  exact congrArg (fun k : etaleProductOverBase f V U ⟶ U => k.left)
    (prod.lift_snd (etaleProductOverBaseFst f V U) (etaleProductOverBaseSnd f V U))

/-- Canonical geometric comparison between the two actual product objects. -/
def etaleProductPullbackIso (V : X.Etale) (U : Z.Etale) :
    (EtalePullback.siteMap f).obj (((etaleObjectPullback f).obj V) ⨯ U) ≅
      V ⨯ (EtalePullback.siteMap f).obj U where
  hom := etaleProductPullbackHom f V U
  inv := etaleProductPullbackInv f V U
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    change (etaleProductPullbackHom f V U).left ≫
      (etaleProductPullbackInv f V U).left = 𝟙 _
    let P := ((etaleObjectPullback f).obj V) ⨯ U
    let a : P ⟶ P := MorphismProperty.Over.homMk
      ((etaleProductPullbackHom f V U).left ≫
        (etaleProductPullbackInv f V U).left) (by
          have h := MorphismProperty.Over.w
            (prod.lift (etaleProductOverBaseFst f V U)
              (etaleProductOverBaseSnd f V U))
          change (etaleProductPullbackHom f V U).left ≫
            ((etaleProductPullbackInv f V U).left ≫ P.hom) = _
          erw [h]
          change (etaleProductPullbackHom f V U).left ≫
            ((prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left ≫ U.hom) = _
          rw [← Category.assoc, etaleProductPullbackHom_snd]
          exact MorphismProperty.Over.w prod.snd)
    change a.left = (𝟙 P : P ⟶ P).left
    have ha : a = 𝟙 P := by
      apply prod.hom_ext
      · apply MorphismProperty.Over.Hom.ext
        change (etaleProductPullbackHom f V U).left ≫
          (etaleProductPullbackInv f V U).left ≫
          (prod.fst : P ⟶ _).left = (prod.fst : P ⟶ _).left
        rw [etaleProductPullbackInv_fst]
        apply pullback.hom_ext
        · simp [etaleProductOverBaseFst, MorphismProperty.Over.homMk, Category.assoc]
        · simp only [Category.assoc]
          change (etaleProductPullbackHom f V U).left ≫
            pullback.lift _ _ _ ≫ pullback.snd V.hom f = _
          rw [pullback.lift_snd, ← Category.assoc, etaleProductPullbackHom_snd]
          exact (MorphismProperty.Over.w (prod.snd : P ⟶ U)).trans
            (MorphismProperty.Over.w (prod.fst : P ⟶ (etaleObjectPullback f).obj V)).symm
      · apply MorphismProperty.Over.Hom.ext
        change (etaleProductPullbackHom f V U).left ≫
          (etaleProductPullbackInv f V U).left ≫
          (prod.snd : P ⟶ U).left = (prod.snd : P ⟶ U).left
        rw [etaleProductPullbackInv_snd, etaleProductPullbackHom_snd]
    exact congrArg (fun k : P ⟶ P => k.left) ha
  inv_hom_id := by
    apply prod.hom_ext
    · apply MorphismProperty.Over.Hom.ext
      change (etaleProductPullbackInv f V U).left ≫
        (etaleProductPullbackHom f V U).left ≫
        (prod.fst : V ⨯ (EtalePullback.siteMap f).obj U ⟶ V).left = _
      rw [etaleProductPullbackHom_fst, ← Category.assoc, etaleProductPullbackInv_fst]
      exact pullback.lift_fst _ _ _
    · apply MorphismProperty.Over.Hom.ext
      change (etaleProductPullbackInv f V U).left ≫
        (etaleProductPullbackHom f V U).left ≫
        (prod.snd : V ⨯ (EtalePullback.siteMap f).obj U ⟶ _).left = _
      rw [etaleProductPullbackHom_snd, etaleProductPullbackInv_snd, Category.id_comp]

/-- The geometric product comparison is natural in both factors. -/
@[reassoc] theorem etaleProductPullbackHom_natural
    {V V' : X.Etale} {U U' : Z.Etale} (a : V ⟶ V') (b : U ⟶ U') :
    (EtalePullback.siteMap f).map (prod.map ((etaleObjectPullback f).map a) b) ≫
        etaleProductPullbackHom f V' U' =
      etaleProductPullbackHom f V U ≫ prod.map a ((EtalePullback.siteMap f).map b) := by
  apply prod.hom_ext
  · simp only [etaleProductPullbackHom, Category.assoc, prod.lift_fst,
      prod.map_fst, prod.lift_fst_assoc]
    rw [← Category.assoc, ← Functor.map_comp, prod.map_fst, Functor.map_comp,
      Category.assoc, etalePullbackProjection_natural]
  · simp only [etaleProductPullbackHom, Category.assoc, prod.lift_snd,
      prod.map_snd, prod.lift_snd_assoc, ← Functor.map_comp, prod.map_snd]

end Langlands.Shimura.Coefficients
