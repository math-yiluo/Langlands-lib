/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Internal Hom from a module with a finite global presentation

Source: Stacks Project, Modules on Sites, Tag 0GMZ, the finite global presentation case
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

open CategoryTheory CategoryTheory.Limits Opposite
namespace PresheafOfModules.SiteFinitePresentation
open PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
  (N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
private noncomputable def homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

/-- Unlike `PresheafOfModules.map_id_apply'`, the object and morphism universes here
are different. Keep all binders explicit to record this distinction. -/
private lemma map_id_apply'
    {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
    (N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))
    {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

/-- The unit calculation for the site's distinct object and morphism universes.
The same-named source lemma requires both universes to coincide. -/
private lemma homObjUnitInvApp_app_one
    {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
    (N : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))
    {U : C} (n : N.obj (op U)) :
    (homObjUnitInvApp N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (map_id_apply' N n))

/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
private noncomputable def homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ConcreteCategory.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ConcreteCategory.ofHom
        { toFun n := homObjUnitInvApp N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (n + n')) =
                (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) +
                    (1 : R.obj (op W.unop.left)) •
                      (show N.obj (op W.unop.left) from N.map W.unop.hom.op n')
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op (r • n)) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n)
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • (show N.obj (op W.unop.left) from
          N.map W.unop.hom.op (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop)))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact homObjUnitInvApp_app_one N n }

/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
private noncomputable def homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (homObjUnitIsoApp N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm

end PresheafOfModules.SiteFinitePresentation

namespace SheafOfModules.SiteFinitePresentation
open SheafOfModules
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
  (A : Sheaf J CommRingCat.{u + 1})
set_option hygiene false in
local notation "𝓐" => (sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A

private noncomputable def unit_iso (N : SheafOfModules.{u + 1} 𝓐) :
    homObj (unit 𝓐) N ≅ N :=
  (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.SiteFinitePresentation.homObjUnitIso N.val)

private instance (N : SheafOfModules.{u + 1} 𝓐) :
    ((homFunctor A).flip.obj N).Additive where
  map_add {M M' f f'} := by
    apply hom_ext
    exact PresheafOfModules.homObjMap_add_left f.unop.val f'.unop.val (𝟙 N.val)

variable [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private noncomputable instance : HasFiniteBiproducts (SheafOfModules.{u + 1} 𝓐) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def free_iso (N : SheafOfModules.{u + 1} 𝓐)
    (κ : Type (u + 1)) [Fintype κ] : homObj (free κ) N ≅ ⨁ fun _ : κ ↦ N := by
  letI : HasFiniteBiproducts (SheafOfModules.{u + 1} 𝓐) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact ((homFunctor A).flip.obj N).mapIso (biproduct.isoCoproduct fun _ : κ ↦ unit 𝓐).op ≪≫
    ((homFunctor A).flip.obj N).opMapBiproductIso (fun _ : κ ↦ unit 𝓐) ≪≫
      biproduct.mapIso fun _ ↦ unit_iso A N

private theorem free_iso_π (N : SheafOfModules.{u + 1} 𝓐)
    (κ : Type (u + 1)) [Fintype κ] (i : κ) :
    (free_iso A N κ).hom ≫ biproduct.π (fun _ : κ ↦ N) i =
      homObjMap (R := A) (ιFree i) (𝟙 N) ≫ (unit_iso A N).hom := by
  simp [free_iso, Functor.opMapBiproductIso, biproduct.uniqueUpToIso,
    Functor.opMapBicone, Category.assoc, ιFree]

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem unit_iso_natural {N N' : SheafOfModules.{u + 1} 𝓐} (f : N ⟶ N') :
    homObjMap (R := A) (𝟙 (unit 𝓐)) f ≫ (unit_iso A N').hom =
      (unit_iso A N).hom ≫ f := by
  apply hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  rfl

private noncomputable def copies (κ : Type (u + 1)) [Fintype κ] :
    SheafOfModules.{u + 1} 𝓐 ⥤ SheafOfModules.{u + 1} 𝓐 where
  obj N := ⨁ fun _ : κ ↦ N
  map f := biproduct.map fun _ ↦ f
  map_id N := by
    apply biproduct.hom_ext
    intro i
    simp
  map_comp f g := by
    apply biproduct.hom_ext
    intro i
    simp

private noncomputable def free_functor_iso (κ : Type (u + 1)) [Fintype κ] :
    (homFunctor A).obj (op (free κ)) ≅ copies A κ :=
  NatIso.ofComponents (fun N ↦ free_iso A N κ) (by
    intro N N' f
    apply biproduct.hom_ext
    intro i
    change (homObjMap (R := A) (𝟙 (free κ)) f ≫ (free_iso A N' κ).hom) ≫
        biproduct.π (fun _ : κ ↦ N') i =
      ((free_iso A N κ).hom ≫ biproduct.map (fun _ : κ ↦ f)) ≫
        biproduct.π (fun _ : κ ↦ N') i
    rw [Category.assoc, free_iso_π, Category.assoc, biproduct.map_π]
    rw [← Category.assoc (free_iso A N κ).hom (biproduct.π (fun _ : κ ↦ N) i) f,
      free_iso_π]
    rw [Category.assoc, ← unit_iso_natural, ← Category.assoc, ← Category.assoc]
    congr 1)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def copies_iso (κ : Type (u + 1)) [Fintype κ] :
    copies A κ ≅ (Functor.const (Discrete κ)) ⋙ colim :=
  NatIso.ofComponents
    (fun N ↦ biproduct.isoCoproduct (fun _ : κ ↦ N) ≪≫
      Sigma.isoColimit ((Functor.const (Discrete κ)).obj N)) (by
    intro N N' f
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι (fun _ : κ ↦ N) i ≫ biproduct.map (fun _ : κ ↦ f) ≫
        ((biproduct.isoCoproduct (fun _ : κ ↦ N')).hom ≫
          (Sigma.isoColimit ((Functor.const (Discrete κ)).obj N')).hom) =
      biproduct.ι (fun _ : κ ↦ N) i ≫
        ((biproduct.isoCoproduct (fun _ : κ ↦ N)).hom ≫
          (Sigma.isoColimit ((Functor.const (Discrete κ)).obj N)).hom) ≫
            colim.map ((Functor.const (Discrete κ)).map f)
    simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.isoCoproduct_hom,
      biproduct.ι_desc_assoc]
    have h (M : SheafOfModules.{u + 1} 𝓐) :
        Sigma.ι (fun _ : κ ↦ M) i ≫
          (Sigma.isoColimit ((Functor.const (Discrete κ)).obj M)).hom =
        colimit.ι ((Functor.const (Discrete κ)).obj M) (Discrete.mk i) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete κ)).obj M) i
    rw [h, ← Category.assoc, h]
    exact (ι_colimMap ((Functor.const (Discrete κ)).map f) (Discrete.mk i)).symm)

private theorem free_preserves_colimit (κ : Type (u + 1)) [Finite κ]
    (I : Type (u + 1)) [SmallCategory I]
    (N : I ⥤ SheafOfModules.{u + 1} 𝓐) :
    PreservesColimit N ((homFunctor A).obj (op (free κ))) := by
  let := Fintype.ofFinite κ
  have : PreservesColimit N (copies A κ) :=
    preservesColimit_of_natIso N (copies_iso A κ).symm
  exact preservesColimit_of_natIso N (free_functor_iso A κ).symm

end SheafOfModules.SiteFinitePresentation

open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SiteFinitePresentation
open SheafOfModules
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
  (A : Sheaf J CommRingCat.{u + 1})
set_option hygiene false in
local notation "𝓐" => (sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A

private theorem over_preserves_finite_colimits (U : C) :
    PreservesFiniteColimits (overFunctor.{u + 1} 𝓐 U) where
  preservesFiniteColimits I _ _ := by
    have : PreservesColimitsOfShape I
        ((Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (J.over U) J) :=
      ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
        (J.over U) J).leftAdjoint_preservesColimits.preservesColimitsOfShape
    have : PreservesColimitsOfShape I
        (overFunctor.{u + 1} 𝓐 U ⋙ toSheaf.{u + 1} ((𝓐).over U)) :=
      inferInstanceAs (PreservesColimitsOfShape I
        (toSheaf.{u + 1} 𝓐 ⋙
          (Over.forget U).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (J.over U) J))
    have : ReflectsColimitsOfShape I (toSheaf.{u + 1} ((𝓐).over U)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (toSheaf ((𝓐).over U))

private noncomputable def over_val_iso (M : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (M.over U).val ≅ (PresheafOfModules.restrictOver A.obj U).obj M.val :=
  PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intro W W' f; rfl)

private noncomputable def hom_sections_equiv
    (M N : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (M.over U ⟶ N.over U) ≃ (homObj (R := A) M N).val.obj (op U) :=
  (fullyFaithfulForget ((𝓐).over U)).homEquiv.trans
    (Iso.homCongr (over_val_iso A M U) (over_val_iso A N U))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def hom_sections_iso
    (N : SheafOfModules.{u + 1} 𝓐) (U : C) :
    (homFunctor A).flip.obj N ⋙ evaluation 𝓐 (op U) ⋙ CategoryTheory.forget _ ≅
      (overFunctor 𝓐 U).op ⋙ yoneda.obj (N.over U) :=
  NatIso.ofComponents
    (F := (homFunctor A).flip.obj N ⋙ evaluation 𝓐 (op U) ⋙ CategoryTheory.forget _)
    (G := (overFunctor 𝓐 U).op ⋙ yoneda.obj (N.over U))
    (fun M ↦ (hom_sections_equiv A M.unop N U).symm.toIso) (by
      intro M M' f
      ext φ
      apply hom_ext
      apply PresheafOfModules.hom_ext
      intro V
      ext x
      rfl)

private theorem hom_preserves_finite_limits :
    PreservesFiniteLimits (homFunctor.{u + 1} A) where
  preservesFiniteLimits I _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro N
    constructor
    intro K
    constructor
    intro c hc
    constructor
    apply isLimitOfReflects (SheafOfModules.forget 𝓐)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    apply isLimitOfReflects (CategoryTheory.forget (ModuleCat ((𝓐).obj.obj U)))
    have : PreservesFiniteColimits (overFunctor 𝓐 U.unop) :=
      over_preserves_finite_colimits A U.unop
    have : PreservesFiniteLimits (overFunctor 𝓐 U.unop).op :=
      preservesFiniteLimits_op _
    have : PreservesLimitsOfShape I
        ((homFunctor A).flip.obj N ⋙ evaluation 𝓐 U ⋙ CategoryTheory.forget _) :=
      preservesLimitsOfShape_of_natIso (hom_sections_iso A N U.unop).symm
    exact isLimitOfPreserves
      ((homFunctor A).flip.obj N ⋙ evaluation 𝓐 U ⋙ CategoryTheory.forget _) hc
end SheafOfModules.SiteFinitePresentation

universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

private theorem preserves_colimit_of_limit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {I : Type w} [SmallCategory I] {J : Type} [SmallCategory J] [FinCategory J]
    [HasColimitsOfShape I D] [HasFiniteLimits D] [HasExactColimitsOfShape I D]
    (K : J ⥤ C ⥤ D) (c : Cone K) (hc : IsLimit c)
    (N : I ⥤ C) [HasColimit N]
    (hK : ∀ j, PreservesColimit N (K.obj j)) : PreservesColimit N c.pt := by
  let W := (whiskeringLeft I C D).obj N
  let E := (evaluation C D).obj (colimit N)
  let G := K ⋙ W
  let d := W.mapCone c
  have hd : IsLimit d := isLimitOfPreserves W hc
  let e : G ⋙ colim ≅ K ⋙ E := NatIso.ofComponents
    (fun j ↦ by
      have := hK j
      exact asIso (colimit.post N (K.obj j))) (by
      intro j j' f
      apply colimit.hom_ext
      intro i
      change colimit.ι (N ⋙ K.obj j) i ≫
          colim.map (whiskerLeft N (K.map f)) ≫ colimit.post N (K.obj j') =
        colimit.ι (N ⋙ K.obj j) i ≫ colimit.post N (K.obj j) ≫
          (K.map f).app (colimit N)
      simp only [colim_map]
      rw [ι_colimMap_assoc, colimit.ι_post, colimit.ι_post_assoc]
      exact ((K.map f).naturality (colimit.ι N i)).symm)
  let s := (Cone.postcompose e.hom).obj (colim.mapCone d)
  let t := E.mapCone c
  have hs : IsLimit s := (IsLimit.postcomposeHomEquiv e _).symm
    (isLimitOfPreserves colim hd)
  have ht : IsLimit t := isLimitOfPreserves E hc
  let p : s ⟶ t :=
    { hom := colimit.post N c.pt
      w j := by
        apply colimit.hom_ext
        intro i
        change colimit.ι (N ⋙ c.pt) i ≫ colimit.post N c.pt ≫
            (c.π.app j).app (colimit N) =
          colimit.ι (N ⋙ c.pt) i ≫ colim.map (whiskerLeft N (c.π.app j)) ≫
            colimit.post N (K.obj j)
        simp only [colim_map]
        rw [colimit.ι_post_assoc, ι_colimMap_assoc, colimit.ι_post]
        exact (c.π.app j).naturality (colimit.ι N i) }
  have : IsIso p := hs.hom_isIso ht p
  have : IsIso (colimit.post N c.pt) :=
    inferInstanceAs (IsIso ((Cone.forget _).map p))
  exact preservesColimit_of_isIso_post c.pt N

namespace SheafOfModules

/-- Internal Hom from a module with a finite global presentation preserves filtered colimits.

Source: Stacks Project, Modules on Sites, Tag 0GMZ, proof after the local reduction.
(auxiliary; not a blueprint node)

Proof: Let `G` and `K` be the finite sets of generators and relations in `p`.
The presentation is the cokernel of `free K → free G`. Restriction to any slice site
preserves this cokernel: its underlying abelian restriction is a left adjoint because
`Over.forget` is cocontinuous, and the module forgetful functor preserves and reflects
colimits. Applying Hom on each slice therefore identifies internal Hom from `P` with
the kernel of internal Hom from `free G` to internal Hom from `free K`, naturally in
the target. Internal Hom from `free G` is the finite product of copies of the target:
a local linear map from a rank-one free module is determined by the image of one.
Filtered colimits of abelian sheaves are exact and commute with finite products.
The same holds for module sheaves, since their forgetful functor preserves colimits,
preserves finite limits and reflects isomorphisms. Consequently the comparison on
these kernels is an isomorphism, with the given coprojections. This proves preservation
of the colimit. Empty sets of generators or relations are included by empty products.
-/
theorem internalHom_preserves_filteredColimit_of_finitePresentation
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (A : Sheaf J CommRingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A))
    (p : P.Presentation) [p.IsFinite]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A)) :
    PreservesColimit N ((homFunctor A).obj (op P)) := by
  let a := (freeHomEquiv _).symm p.relations.s ≫ kernel.ι p.generators.π
  have w : a ≫ p.generators.π = 0 := by simp [a]
  have h : IsLimit (KernelFork.ofι p.generators.π.op
      (by rw [← op_comp, w, op_zero])) :=
    CokernelCofork.IsColimit.ofπOp p.generators.π w p.isColimit
  have : PreservesFiniteLimits (homFunctor A) :=
    SiteFinitePresentation.hom_preserves_finite_limits A
  let c := (homFunctor A).mapCone
    (KernelFork.ofι p.generators.π.op (by rw [← op_comp, w, op_zero]))
  have hc : IsLimit c := isLimitOfPreserves (homFunctor A) h
  have : HasExactColimitsOfShape I (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj A)) :=
    HasExactColimitsOfShape.domain_of_functor I (toSheaf _)
  apply preserves_colimit_of_limit _ c hc N
  intro j
  cases j
  · exact SiteFinitePresentation.free_preserves_colimit A p.generators.I I N
  · exact SiteFinitePresentation.free_preserves_colimit A p.relations.I I N

end SheafOfModules
