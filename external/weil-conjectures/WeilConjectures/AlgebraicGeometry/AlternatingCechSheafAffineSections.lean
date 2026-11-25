/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Global sections of the increasing-tuple sheaf complex

Source: Stacks Project, Tag 01FM, signed faces and intersection sections.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-sections).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

open Opposite Limits TopologicalSpace in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section

set_option backward.isDefEq.respectTransparency false in
private theorem capIsSheaf {X : Scheme.{u}} (G : X.Modules) (W : X.Opens) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (cechCapModule G W).presheaf := by
  let j : TopCat.of W ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Topology.IsOpenEmbedding j := W.isOpenEmbedding
  let K : X.Opens ⥤ X.Opens := Opens.map j ⋙ hj.isOpenMap.functor
  have : hj.isOpenMap.functor.IsContinuous (Opens.grothendieckTopology W)
      (Opens.grothendieckTopology X) := hj.functor_isContinuous
  have : K.IsContinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology X) := inferInstance
  have he (V : X.Opens) : (cechCapFunctor W).obj V = K.obj V := by
    ext x
    change (x ∈ V ∧ x ∈ W) ↔ x ∈ Subtype.val '' {y : W | y.val ∈ V}
    aesop
  let e : (cechCapModule G W).presheaf ≅ K.op ⋙ G.val.presheaf :=
    NatIso.ofComponents (fun V ↦ G.val.presheaf.mapIso (eqToIso (congrArg op (he V.unop))))
      (by
        intro V Z h
        change G.val.presheaf.map ((cechCapFunctor W).map h.unop).op ≫
            G.val.presheaf.map (eqToHom (congrArg op (he Z.unop))) =
          G.val.presheaf.map (eqToHom (congrArg op (he V.unop))) ≫
            G.val.presheaf.map (K.map h.unop).op
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1)
  exact (Presheaf.isSheaf_of_iso_iff e).mpr
    (Functor.op_comp_isSheaf K _ _ ⟨G.val.presheaf, G.isSheaf⟩)

private theorem cechSheafificationUnit_isIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) :
    IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (alternatingCechSheafPresheafTerms U G p)) := by
  let H : X.Modules :=
    ⟨alternatingCechSheafPresheafTerms U G p,
      PresheafOfModules.isSheaf_of_isLimit (limit.isLimit
        (Discrete.functor (fun t : Fin (p + 1) ↪o Fin r ↦
          cechCapModule G (alternatingCechIntersection U t))))
        (fun t ↦ capIsSheaf G (alternatingCechIntersection U t.as))⟩
  exact Adjunction.isIso_unit_app_of_iso
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)) (X := H) (Iso.refl _)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def pushforwardSectionsIso
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) :
    Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor (R := A) ≅
      SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) := by
  refine NatIso.ofComponents (fun G ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
  · intro a
    ext x
    rfl
  · intro G H g
    ext x
    rfl

private noncomputable def mapExtendIso
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasZeroObject C] [HasZeroObject D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat := by
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let e := ComplexShape.embeddingUpNat
  have hi (n : ℤ) (h : 0 ≤ n) : e.f n.toNat = n := Int.toNat_of_nonneg h
  have hn (n : ℤ) (h : ¬ 0 ≤ n) : ∀ i, e.f i ≠ n := by
    intro i
    change (i : ℤ) ≠ n
    omega
  let α : ∀ n : ℤ,
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend e)).X n ≅
        (L.extend e).X n := fun n ↦
    if h : 0 ≤ n then
      F.mapIso (K.extendXIso e (hi n h)) ≪≫ (L.extendXIso e (hi n h)).symm
    else
      (F.map_isZero (K.isZero_extend_X e n (hn n h))).isoZero ≪≫
        ((L.isZero_extend_X e n (hn n h)).isoZero).symm
  refine HomologicalComplex.Hom.isoOfComponents α ?_
  intro n m hnm
  by_cases hn' : 0 ≤ n
  · by_cases hm' : 0 ≤ m
    · dsimp only [α]
      simp only [dite_eq_left hn', dite_eq_left hm', Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom]
      change _ ≫ (L.extend e).d n m = F.map ((K.extend e).d n m) ≫ _
      rw [L.extend_d_eq e (hi n hn') (hi m hm'),
        K.extend_d_eq e (hi n hn') (hi m hm')]
      simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc (K.extendXIso e (hi m hm')).inv,
        Iso.inv_hom_id, F.map_id, Category.id_comp]
      rfl
    · exact (L.isZero_extend_X e m (hn m hm')).eq_of_tgt _ _
  · exact (F.map_isZero (K.isZero_extend_X e n (hn n hn'))).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def capSectionsIso {X : Scheme.{u}} (G : X.Modules) (W : X.Opens) :
    (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)).obj (cechCapModule G W) ≅
      G.presheafModuleCat.obj (op W) :=
  G.presheafModuleCat.mapIso (eqToIso (congrArg op (top_inf_eq W)))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def presheafTermsSectionsIso {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) :
    (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)).obj
        (alternatingCechSheafPresheafTerms U G p) ≅
      alternatingCechTerms U G.presheafModuleCat p :=
  PreservesProduct.iso (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤))
      (fun t : Fin (p + 1) ↪o Fin r ↦ cechCapModule G (alternatingCechIntersection U t)) ≪≫
    Pi.mapIso (fun t ↦ capSectionsIso G (alternatingCechIntersection U t)) ≪≫
    ModuleCat.piIsoPi _

set_option backward.isDefEq.respectTransparency false in
private theorem capSectionsIso_naturality {X : Scheme.{u}} (G : X.Modules)
    {W Z : X.Opens} (h : W ≤ Z) :
    (capSectionsIso G Z).hom ≫ G.presheafModuleCat.map (homOfLE h).op =
      (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)).map (cechCapModuleMap G h) ≫
        (capSectionsIso G W).hom := by
  change G.presheafModuleCat.map (eqToHom (congrArg op (top_inf_eq Z))) ≫
      G.presheafModuleCat.map (homOfLE h).op =
    G.presheafModuleCat.map (homOfLE (inf_le_inf_left (⊤ : X.Opens) h)).op ≫
      G.presheafModuleCat.map (eqToHom (congrArg op (top_inf_eq W)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private theorem presheafTermsSectionsIso_π {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) (t : Fin (p + 1) ↪o Fin r) :
    (presheafTermsSectionsIso U G p).hom ≫
        ModuleCat.ofHom (LinearMap.proj t) =
      (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)).map
        (Pi.π (fun q : Fin (p + 1) ↪o Fin r ↦
          cechCapModule G (alternatingCechIntersection U q)) t) ≫
        (capSectionsIso G (alternatingCechIntersection U t)).hom := by
  simp only [presheafTermsSectionsIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype]
  rw [Pi.mapIso_hom_π, ← Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π]

set_option backward.isDefEq.respectTransparency false in
private theorem sectionsDifferential_π {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) (t : Fin (p + 2) ↪o Fin r) :
    alternatingCechDifferential U G.presheafModuleCat p ≫
        ModuleCat.ofHom (LinearMap.proj t) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (ModuleCat.ofHom (X := alternatingCechTerms U G.presheafModuleCat p)
          (Y := G.presheafModuleCat.obj
            (op (alternatingCechIntersection U ((Fin.succAboveOrderEmb j).trans t))))
          (LinearMap.proj ((Fin.succAboveOrderEmb j).trans t)) ≫
          G.presheafModuleCat.map
            (homOfLE (alternatingCechIntersection_face_le U p t j)).op) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  simp only [alternatingCechDifferential, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem presheafTermsSectionsIso_comm {X : Scheme.{u}} {r : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) :
    (presheafTermsSectionsIso U G p).hom ≫ alternatingCechDifferential U
        G.presheafModuleCat p =
      (PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)).map
          (alternatingCechSheafPresheafD U G p) ≫
        (presheafTermsSectionsIso U G (p + 1)).hom := by
  classical
  let E := PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (op ⊤)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  change ((presheafTermsSectionsIso U G p).hom ≫
      alternatingCechDifferential U G.presheafModuleCat p ≫
        ModuleCat.ofHom (LinearMap.proj t)).hom s =
    (E.map (alternatingCechSheafPresheafD U G p) ≫
      (presheafTermsSectionsIso U G (p + 1)).hom ≫
        ModuleCat.ofHom (LinearMap.proj t)).hom s
  congr 1
  rw [sectionsDifferential_π, presheafTermsSectionsIso_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← Category.assoc,
    presheafTermsSectionsIso_π]
  simp only [Category.assoc, capSectionsIso_naturality]
  rw [← E.map_comp_assoc, alternatingCechSheafPresheafD, Pi.lift_comp_π]
  simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Functor.map_comp, Category.assoc]
  rfl

end

/-- Taking global sections after pushforward recovers the section complex, with scalars
restricted along the base morphism. Source: Stacks Project, Tags 01FM and 02KG.
(blueprint: lem-pc-s3-alternating-cech-sheaf-affine-sections).

Proof: The intersection presheaf V ↦ G(V ∩ W) is already a sheaf: it is the direct
image from the over site of W. Its sheafification unit is therefore an isomorphism.
Module sheafification is additive and preserves finite biproducts, hence finite
products. The forgetful functor and evaluation preserve products. Therefore the
degree-p global sections of the sheafified product are the product of G(W_t).
At the top open, top ∩ W_t = W_t.
Pushforward sections at the top are sections on X, and restriction of scalars is
along A → Γ(X,O_X), the composite of ΓSpecIso.inv and f.appTop. These identifications
commute with each face restriction since they are the sheafification unit followed
by restriction along top ∩ W_t = W_t. Additivity then identifies the finite signed
sums defining both differentials. Thus the degree comparisons form a complex
isomorphism. In negative degrees both extended complexes are zero, and the unique
maps give the comparison there. The empty family and empty tuple types contribute
zero modules, and require no covering or affineness hypothesis. -/
theorem alternatingCechSheafComplex_affineSections
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    letI : (moduleSpecΓFunctor (R := A)).Additive := ⟨by intros; rfl⟩
    Nonempty (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)) ≅
      ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).mapHomologicalComplex
         (ComplexShape.up ℤ)).obj
        ((alternatingCechComplex U G.presheafModuleCat).extend
          ComplexShape.embeddingUpNat)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let : (moduleSpecΓFunctor (R := A)).Additive := ⟨by intros; rfl⟩
    let E := PresheafOfModules.evaluation.{u} X.ringCatSheaf.obj (Opposite.op ⊤)
    let S := SheafOfModules.evaluation.{u} X.ringCatSheaf (Opposite.op ⊤)
    let : S.Additive := ⟨by intros; rfl⟩
    let R := ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let : L.Additive :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
    let P := alternatingCechSheafPresheafComplex U G
    let C := alternatingCechSheafComplex U G
    let η : (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ⟶
        (S.mapHomologicalComplex (ComplexShape.up ℕ)).obj C :=
      (NatTrans.mapHomologicalComplex
        (Functor.whiskerRight (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit E) (ComplexShape.up ℕ)).app P
    have hη : ∀ p, IsIso (η.f p) := by
      intro p
      have := cechSheafificationUnit_isIso U G p
      change IsIso (E.map ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app (alternatingCechSheafPresheafTerms U G p)))
      infer_instance
    have : IsIso η := HomologicalComplex.Hom.isIso_of_components η
    let eP : (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ≅
        alternatingCechComplex U G.presheafModuleCat :=
      HomologicalComplex.Hom.isoOfComponents (presheafTermsSectionsIso U G) (by
        intro p q hpq
        have hq : p + 1 = q := hpq
        subst q
        simpa only [P, alternatingCechComplex, alternatingCechSheafPresheafComplex,
          CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d] using
            presheafTermsSectionsIso_comm U G p)
    let e := (asIso η).symm ≪≫ eP
    let α := (Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso f)
      (ComplexShape.up ℤ)).app (C.extend ComplexShape.embeddingUpNat)
    let β := (Functor.mapHomologicalComplexCompIso (Iso.refl (S ⋙ R))
      (ComplexShape.up ℤ)).app (C.extend ComplexShape.embeddingUpNat)
    exact ⟨α ≪≫ β.symm ≪≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (mapExtendIso S C ≪≫ (ComplexShape.embeddingUpNat.extendFunctor _).mapIso e)⟩
end AlgebraicGeometry
