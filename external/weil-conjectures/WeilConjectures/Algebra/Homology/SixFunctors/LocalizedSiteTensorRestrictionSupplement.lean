/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Tensor products and restriction to a localized ringed site

Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(blueprint: lem-sfb-localized-site-tensor-restriction).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory Opposite Functor

namespace SheafOfModules

section SheafificationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{m}]
  (R : Sheaf J RingCat.{r}) (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]

private noncomputable def overSheafificationMap (P : PresheafOfModules.{m} R.obj) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).obj
      ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P) ⟶
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))

set_option backward.isDefEq.respectTransparency false in
private lemma overSheafificationMap_unit (P : PresheafOfModules.{m} R.obj) :
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val =
      whiskerLeft (Over.forget U).op (toSheafify J P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv (R := R.over U) (𝟙 _)
    (P := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P)
    (F := ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U)).apply_symm_apply
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (R.over U).obj).map) h

private lemma overSheafificationMap_isIso (P : PresheafOfModules.{m} R.obj) :
    IsIso (overSheafificationMap R U P) := by
  let a := toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val
  have hi : Presheaf.IsLocallyInjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hs : Presheaf.IsLocallySurjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have hi' : Presheaf.IsLocallyInjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

set_option backward.isDefEq.respectTransparency false in
private lemma overSheafificationMap_naturality {P Q : PresheafOfModules.{m} R.obj}
    (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).map
        ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map f) ≫
        overSheafificationMap R U Q =
      overSheafificationMap R U P ≫
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f).over U := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext (J.over U) _ _
    (((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj Q).over U).isSheaf
  change toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
      (sheafifyMap (J.over U)
        (whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf _).map f)) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U Q).val) =
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
      ((PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val ≫
        whiskerLeft (Over.forget U).op
          (sheafifyMap J ((PresheafOfModules.toPresheaf _).map f)))
  rw [← toSheafify_naturality_assoc]
  erw [overSheafificationMap_unit R U Q]
  rw [← Category.assoc, overSheafificationMap_unit R U P]
  exact (whiskerLeft_comp _ _ _).symm.trans
    ((congrArg (whiskerLeft (Over.forget U).op) (toSheafify_naturality J _)).trans
      (whiskerLeft_comp _ _ _))

end SheafificationComparison

section TensorComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{m}]
  {A : Sheaf J CommRingCat.{r}} (U : C)
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorOverPresheafIso
    (F G : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    siteTensorPresheaf (R := (A.over U).obj) (F.over U).val (G.over U).val ≅
      (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj
        (siteTensorPresheaf F.val G.val) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorOverComparison
    (F G : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U) ⟶
      ((siteSheafTensorRight G).obj F).over U :=
  (PresheafOfModules.sheafification
    (R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A).over U) (𝟙 _)).map
      (tensorOverPresheafIso U F G).hom ≫
    overSheafificationMap ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) U
      (siteTensorPresheaf F.val G.val)

private lemma tensorOverComparison_isIso
    (F G : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
    IsIso (tensorOverComparison U F G) := by
  have := overSheafificationMap_isIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) U
    (siteTensorPresheaf F.val G.val)
  dsimp only [tensorOverComparison]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private lemma tensorOverComparison_naturality
    {F F' G G' : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
        siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U) ≫
          tensorOverComparison U F' G' =
      tensorOverComparison U F G ≫
        ((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let S := PresheafOfModules.sheafification (R := R.over U) (𝟙 _)
  let h := siteTensorHom f.val G.val ≫ siteTensorSecondMap F'.val g.val
  let hl := siteTensorHom (R := (A.over U).obj) (f.over U).val (G.over U).val ≫
    siteTensorSecondMap (A := A.over U) (F'.over U).val (g.over U).val
  have ht : hl ≫ (tensorOverPresheafIso U F' G').hom =
      (tensorOverPresheafIso U F G).hom ≫
        (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map h := by
    ext V : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    rfl
  change S.map (siteTensorHom (R := (A.over U).obj) (f.over U).val (G.over U).val) ≫
      S.map (siteTensorSecondMap (A := A.over U) (F'.over U).val (g.over U).val) ≫
        (S.map (tensorOverPresheafIso U F' G').hom ≫
          overSheafificationMap R U _) =
    (S.map (tensorOverPresheafIso U F G).hom ≫ overSheafificationMap R U _) ≫
      (((PresheafOfModules.sheafification (R := R) (𝟙 _)).map
        (siteTensorHom f.val G.val) ≫
        (PresheafOfModules.sheafification (R := R) (𝟙 _)).map
          (siteTensorSecondMap F'.val g.val)).over U)
  rw [← S.map_comp_assoc, ← S.map_comp_assoc]
  change S.map (hl ≫ (tensorOverPresheafIso U F' G').hom) ≫ _ = _
  rw [ht, S.map_comp, Category.assoc]
  have hn := congrArg (fun k ↦ S.map (tensorOverPresheafIso U F G).hom ≫ k)
    (overSheafificationMap_naturality R U h)
  simp only [h, Functor.map_comp, Category.assoc] at hn ⊢
  convert! hn using 1

set_option backward.isDefEq.respectTransparency false in
private lemma tensorOverComparison_pure
    (F G : ringedSiteModules.{m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)) :
    (tensorOverComparison U F G).val.app (op V)
        (siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y) =
      siteSheafTensorTmul F G (op V.left) x y := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let P := siteTensorPresheaf F.val G.val
  let t := (tensorOverPresheafIso U F G).hom
  have h := toSheafify_naturality (J.over U)
    ((PresheafOfModules.toPresheaf _).map t)
  have h' := overSheafificationMap_unit R U P
  let z := x ⊗ₜ[A.obj.obj (op V.left)] y
  have ha := congrArg (fun k ↦ (k.app (op V)) z) h
  have hb := congrArg (fun k ↦ (k.app (op V)) z) h'
  exact (congrArg (fun z ↦ (overSheafificationMap R U P).val.app (op V) z)
    ha.symm).trans hb

end TensorComparison

attribute [local instance] tensorOverComparison_isIso

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to a localized ringed site commutes naturally with tensor products,
with the comparison sending each sheafified pure tensor to the same pure tensor.
Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(blueprint: lem-sfb-localized-site-tensor-restriction).

Proof:
1. The restriction of the sectionwise tensor presheaf equals the tensor presheaf of
   the restrictions: at `V → U` both have sections `F(V) ⊗ G(V)` and the same
   restriction maps. This identification is natural in both factors, by
   `def-pur-localized-ringed-site` and `def-pur-sheaf-tensor-product`.
2. Apply `lem-cbc-sieve-slice-sheafification` to the underlying abelian presheaf.
   By `def-weil-presheaf-modules-sheafification`, module sheafification has this
   underlying abelian sheafification. The comparison from slice sheafification
   to restricted sheafification commutes with the two units.
3. Transport the module action through this comparison. The unit equation shows
   that the transported action extends the original presheaf action. Uniqueness
   of the extending action in module sheafification makes the comparison linear.
4. Invert that comparison to obtain the isomorphism below. Its unit equation on
   `x ⊗ y` gives the pure-tensor formula. Naturality of the presheaf identification
   and of slice sheafification gives the equation for arbitrary `f` and `g`.
No finiteness, flatness, fibre products or subcanonicity is used. -/
theorem exists_localizedSiteTensorRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify J AddCommGrpCat.{m}]
    (A : Sheaf J CommRingCat.{r}) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{m}] :
    ∃ e : ∀ F G : ringedSiteModules.{m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A),
        ((siteSheafTensorRight G).obj F).over U ≅
          (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U),
      (∀ (F F' G G' : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (f : F ⟶ F') (g : G ⟶ G'),
        (((siteSheafTensorRight G).map f ≫ siteSheafTensorSecondMap F' g).over U) ≫
            (e F' G').hom =
          (e F G).hom ≫
            (siteSheafTensorRight (A := A.over U) (G.over U)).map (f.over U) ≫
              siteSheafTensorSecondMap (A := A.over U) (F'.over U) (g.over U)) ∧
      (∀ (F G : ringedSiteModules.{m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
          (V : Over U) (x : F.val.obj (op V.left)) (y : G.val.obj (op V.left)),
        ((e F G).hom.val.app (op V)) (siteSheafTensorTmul F G (op V.left) x y) =
          siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
  let c (F G : ringedSiteModules.{m} R) := tensorOverComparison U F G
  let e : ∀ F G : ringedSiteModules.{m} R,
      ((siteSheafTensorRight G).obj F).over U ≅
        (siteSheafTensorRight (A := A.over U) (G.over U)).obj (F.over U) :=
    fun F G ↦ (asIso (c F G)).symm
  refine ⟨e, ?_, ?_⟩
  · intro F F' G G' f g
    change _ ≫ inv (c F' G') = inv (c F G) ≫ _
    apply (cancel_mono (c F' G')).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    dsimp only [c]
    rw [tensorOverComparison_naturality U f g]
    simp only [IsIso.inv_hom_id_assoc]
  · intro F G V x y
    have h := tensorOverComparison_pure U F G V x y
    have hi := congrArg (fun z ↦ (inv (c F G)).val.app (op V) z) h
    have hh := congrArg (fun k ↦ k.val.app (op V)
      (siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y))
      (IsIso.hom_inv_id (c F G))
    change _ = siteSheafTensorTmul (A := A.over U) (F.over U) (G.over U) (op V) x y
      at hh
    exact hi.symm.trans hh

end SheafOfModules
