import Langlands.Shimura.Coefficients.EtaleAssociatedPullback
import Langlands.Shimura.Coefficients.EtaleTorsorPullbackFunctoriality
import Langlands.Shimura.Coefficients.CrossCover

/-! # Unit and composition coherence of product-sheaf base change -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z W : Scheme.{u}}
variable (f : Z ⟶ X) [Etale f] (g : W ⟶ Z) [Etale g]

/-- Successive projections recover the single fiber-product projection. -/
@[reassoc] theorem etalePullbackProjection_comp (V : X.Etale) :
    (EtalePullback.siteMap (g ≫ f)).map
        ((MorphismProperty.Over.pullbackComp g f).hom.app V) ≫
      (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).hom.app
          ((etaleObjectPullback g).obj ((etaleObjectPullback f).obj V)) ≫
      (EtalePullback.siteMap f).map
        (etalePullbackProjection g ((etaleObjectPullback f).obj V)) ≫
      etalePullbackProjection f V =
    etalePullbackProjection (g ≫ f) V := by
  apply MorphismProperty.Over.Hom.ext
  change ((MorphismProperty.Over.pullbackComp g f).hom.app V).left ≫
    𝟙 _ ≫ pullback.fst (pullback.snd V.hom f) g ≫ pullback.fst V.hom f =
      pullback.fst V.hom (g ≫ f)
  rw [Category.id_comp]
  exact MorphismProperty.Over.pullbackComp_left_fst_fst g f V

/-- The actual geometric product comparison respects successive base changes. -/
theorem etaleProductPullbackHom_comp (V : X.Etale) (U : W.Etale) :
    etaleProductPullbackHom (g ≫ f) V U ≫
      prod.map (𝟙 V)
        ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
          (inferInstance : Etale f)).hom.app U) =
    (EtalePullback.siteMap (g ≫ f)).map
        (prod.map ((MorphismProperty.Over.pullbackComp g f).hom.app V) (𝟙 U)) ≫
      (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).hom.app
          (((etaleObjectPullback g).obj ((etaleObjectPullback f).obj V)) ⨯ U) ≫
      (EtalePullback.siteMap f).map
        (etaleProductPullbackHom g ((etaleObjectPullback f).obj V) U) ≫
      etaleProductPullbackHom f V ((EtalePullback.siteMap g).obj U) := by
  let S := (etaleObjectPullback (g ≫ f)).obj V
  let T := (etaleObjectPullback g).obj ((etaleObjectPullback f).obj V)
  let Q := (etaleObjectPullback f).obj V
  let a : (S ⨯ U).left ⟶ (T ⨯ U).left :=
    (prod.map ((MorphismProperty.Over.pullbackComp g f).hom.app V) (𝟙 U)).left
  let b : (T ⨯ U).left ⟶ (Q ⨯ (EtalePullback.siteMap g).obj U).left :=
    (etaleProductPullbackHom g Q U).left
  let c : (Q ⨯ (EtalePullback.siteMap g).obj U).left ⟶
      (V ⨯ (EtalePullback.siteMap f).obj ((EtalePullback.siteMap g).obj U)).left :=
    (etaleProductPullbackHom f V ((EtalePullback.siteMap g).obj U)).left
  let d : (S ⨯ U).left ⟶ (V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U).left :=
    (etaleProductPullbackHom (g ≫ f) V U).left
  let e : (V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U).left ⟶
      (V ⨯ (EtalePullback.siteMap f).obj ((EtalePullback.siteMap g).obj U)).left :=
    (prod.map (𝟙 V) ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
      (inferInstance : Etale f)).hom.app U)).left
  have af : a ≫ (prod.fst : T ⨯ U ⟶ T).left =
      (prod.fst : S ⨯ U ⟶ S).left ≫
        ((MorphismProperty.Over.pullbackComp g f).hom.app V).left :=
    congrArg (fun k : S ⨯ U ⟶ T => k.left) (prod.map_fst _ _)
  have asnd : a ≫ (prod.snd : T ⨯ U ⟶ U).left =
      (prod.snd : S ⨯ U ⟶ U).left := by
    have h := congrArg (fun k : S ⨯ U ⟶ U => k.left)
      (prod.map_snd ((MorphismProperty.Over.pullbackComp g f).hom.app V) (𝟙 U))
    exact h.trans (Category.comp_id _)
  have bf := etaleProductPullbackHom_fst g Q U
  have bs := etaleProductPullbackHom_snd g Q U
  have cf := etaleProductPullbackHom_fst f V ((EtalePullback.siteMap g).obj U)
  have cs := etaleProductPullbackHom_snd f V ((EtalePullback.siteMap g).obj U)
  have df := etaleProductPullbackHom_fst (g ≫ f) V U
  have ds := etaleProductPullbackHom_snd (g ≫ f) V U
  have ef : e ≫ (prod.fst : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ V).left =
      (prod.fst : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶ V).left := by
    have h := congrArg (fun k : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶ V => k.left)
      (prod.map_fst (𝟙 V) ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).hom.app U))
    exact h.trans (Category.comp_id _)
  have es : e ≫ (prod.snd : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ _).left =
      (prod.snd : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶ _).left := by
    have h := congrArg
      (fun k : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶
        (EtalePullback.siteMap f).obj ((EtalePullback.siteMap g).obj U) => k.left)
      (prod.map_snd (𝟙 V) ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).hom.app U))
    exact h.trans (Category.comp_id _)
  have cpf := MorphismProperty.Over.pullbackComp_left_fst_fst g f V
  change ((MorphismProperty.Over.pullbackComp g f).hom.app V).left ≫
    pullback.fst Q.hom g ≫ pullback.fst V.hom f =
      pullback.fst V.hom (g ≫ f) at cpf
  change b ≫ (prod.fst : Q ⨯ (EtalePullback.siteMap g).obj U ⟶ Q).left =
    (prod.fst : T ⨯ U ⟶ T).left ≫ pullback.fst Q.hom g at bf
  change b ≫ (prod.snd : Q ⨯ (EtalePullback.siteMap g).obj U ⟶ _).left =
    (prod.snd : T ⨯ U ⟶ U).left at bs
  change c ≫ (prod.fst : V ⨯ (EtalePullback.siteMap f).obj
    ((EtalePullback.siteMap g).obj U) ⟶ V).left =
    (prod.fst : Q ⨯ (EtalePullback.siteMap g).obj U ⟶ Q).left ≫ pullback.fst V.hom f at cf
  change c ≫ (prod.snd : V ⨯ (EtalePullback.siteMap f).obj
    ((EtalePullback.siteMap g).obj U) ⟶ _).left =
    (prod.snd : Q ⨯ (EtalePullback.siteMap g).obj U ⟶ _).left at cs
  change d ≫ (prod.fst : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶ V).left =
    (prod.fst : S ⨯ U ⟶ S).left ≫ pullback.fst V.hom (g ≫ f) at df
  change d ≫ (prod.snd : V ⨯ (EtalePullback.siteMap (g ≫ f)).obj U ⟶ _).left =
    (prod.snd : S ⨯ U ⟶ U).left at ds
  apply prod.hom_ext
  · apply MorphismProperty.Over.Hom.ext
    change (d ≫ e) ≫ (prod.fst : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ V).left =
      (a ≫ 𝟙 _ ≫ b ≫ c) ≫ (prod.fst : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ V).left
    simp only [Category.assoc, Category.id_comp, ef, cf, reassoc_of% bf,
      reassoc_of% af, cpf, df]
  · apply MorphismProperty.Over.Hom.ext
    change (d ≫ e) ≫ (prod.snd : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ _).left =
      (a ≫ 𝟙 _ ≫ b ≫ c) ≫ (prod.snd : V ⨯ (EtalePullback.siteMap f).obj
        ((EtalePullback.siteMap g).obj U) ⟶ _).left
    simp only [Category.assoc, Category.id_comp, es, cs, bs, asnd, ds]

/-- The geometric product comparison at the identity is the first-projection
cover comparison after the canonical site identification. -/
theorem etaleProductPullbackHom_id (V U : X.Etale) :
    (MorphismProperty.Over.mapId ⊤ X).inv.app
        (((etaleObjectPullback (𝟙 X)).obj V) ⨯ U) ≫
      etaleProductPullbackHom (𝟙 X) V U =
    prod.map ((etaleObjectPullbackId X).hom.app V) (𝟙 U) ≫
      prod.map (𝟙 V) ((MorphismProperty.Over.mapId ⊤ X).inv.app U) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc]
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 ((((etaleObjectPullback (𝟙 X)).obj V) ⨯ U).left) ≫
      (etaleProductPullbackHom (𝟙 X) V U).left ≫
      (prod.fst : V ⨯ (EtalePullback.siteMap (𝟙 X)).obj U ⟶ V).left =
        (prod.fst : ((etaleObjectPullback (𝟙 X)).obj V) ⨯ U ⟶ _).left ≫
          pullback.fst V.hom (𝟙 X)
    rw [Category.id_comp, etaleProductPullbackHom_fst]
  · simp only [Category.assoc, prod.map_snd, prod.map_snd_assoc]
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 ((((etaleObjectPullback (𝟙 X)).obj V) ⨯ U).left) ≫
      (etaleProductPullbackHom (𝟙 X) V U).left ≫
      (prod.snd : V ⨯ (EtalePullback.siteMap (𝟙 X)).obj U ⟶ _).left =
        (prod.snd : ((etaleObjectPullback (𝟙 X)).obj V) ⨯ U ⟶ U).left ≫ 𝟙 U.left
    rw [Category.id_comp, etaleProductPullbackHom_snd, Category.comp_id]

variable (R : Type u) [CommRing R]

/-- The natural comparison for a product sheaf restricted in two steps, with
the actual single-pullback cover at the target. -/
def etaleProductSheafPullbackComp (V : X.Etale) :
    (productSheaf X.smallEtaleTopology V ⋙
        EtalePullback.restriction f (ModuleCat.{u} R)) ⋙
      EtalePullback.restriction g (ModuleCat.{u} R) ≅
    EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R) ⋙
      productSheaf W.smallEtaleTopology ((etaleObjectPullback (g ≫ f)).obj V) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (productSheaf X.smallEtaleTopology V)
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g) ≪≫
    etaleProductSheafPullback (g ≫ f) R V

/-- The two-step comparison uses the actual restriction composition map. -/
@[simp] theorem etaleProductSheafPullbackComp_hom_app
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleProductSheafPullbackComp f g R V).hom.app F =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        ((productSheaf X.smallEtaleTopology V).obj F) ≫
      (etaleProductSheafPullback (g ≫ f) R V).hom.app F := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

/-- Identity restriction recovers product-sheaf cover change along the actual
first-projection identity comparison. -/
@[reassoc] theorem etaleProductSheafPullback_id
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleProductSheafPullback (𝟙 X) R V).hom.app F ≫
      (productSheaf X.smallEtaleTopology ((etaleObjectPullback (𝟙 X)).obj V)).map
        ((EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app F) =
    (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app
        ((productSheaf X.smallEtaleTopology V).obj F) ≫
      coverPullback X.smallEtaleTopology ((etaleObjectPullbackId X).hom.app V) F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (etaleProductPullbackHom (𝟙 X) V U.unop).op ≫
      F.obj.map ((MorphismProperty.Over.mapId ⊤ X).inv.app
        (((etaleObjectPullback (𝟙 X)).obj V) ⨯ U.unop)).op =
    F.obj.map (prod.map (𝟙 V)
      ((MorphismProperty.Over.mapId ⊤ X).inv.app U.unop)).op ≫
      F.obj.map (prod.map ((etaleObjectPullbackId X).hom.app V) (𝟙 U.unop)).op
  simp only [← Functor.map_comp, ← op_comp]
  exact congrArg (fun k => F.obj.map k.op) (etaleProductPullbackHom_id V U.unop)

/-- The canonical product-sheaf comparison agrees with successive comparisons,
including the contravariant change from the iterated to the single cover. -/
@[reassoc] theorem etaleProductSheafPullback_comp
    (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        ((productSheaf X.smallEtaleTopology V).obj F) ≫
      (etaleProductSheafPullback (g ≫ f) R V).hom.app F =
    (EtalePullback.restriction g (ModuleCat.{u} R)).map
        ((etaleProductSheafPullback f R V).hom.app F) ≫
      (etaleProductSheafPullback g R ((etaleObjectPullback f).obj V)).hom.app
        ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) ≫
      (productSheaf W.smallEtaleTopology
        ((etaleObjectPullback g).obj ((etaleObjectPullback f).obj V))).map
          ((EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app F) ≫
      coverPullback W.smallEtaleTopology
        ((MorphismProperty.Over.pullbackComp g f).hom.app V)
          ((EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map
      (prod.map (𝟙 V)
        ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
          (inferInstance : Etale f)).hom.app U.unop)).op ≫
      F.obj.map (etaleProductPullbackHom (g ≫ f) V U.unop).op =
    F.obj.map (etaleProductPullbackHom f V ((EtalePullback.siteMap g).obj U.unop)).op ≫
      F.obj.map ((EtalePullback.siteMap f).map
        (etaleProductPullbackHom g ((etaleObjectPullback f).obj V) U.unop)).op ≫
      F.obj.map ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale g)
        (inferInstance : Etale f)).hom.app
          (((etaleObjectPullback g).obj ((etaleObjectPullback f).obj V)) ⨯ U.unop)).op ≫
      F.obj.map ((EtalePullback.siteMap (g ≫ f)).map
        (prod.map ((MorphismProperty.Over.pullbackComp g f).hom.app V) (𝟙 U.unop))).op
  simp only [← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simpa only [Category.assoc, Quiver.Hom.unop_op] using
    etaleProductPullbackHom_comp f g V U.unop

end Langlands.Shimura.Coefficients
