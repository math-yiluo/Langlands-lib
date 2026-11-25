/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLisseRestriction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite locally constant cohomology under an isomorphism of coefficient rings

Source: Stacks Project, Cohomology on Sites, Tags 06YY and 094I.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

section Restriction

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S : Sheaf T RingCat.{u}}

private noncomputable def restrictCancelIso (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    restrictScalars β ⋙ restrictScalars α ≅ 𝟭 (SheafOfModules.{u} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private noncomputable def coefficientEquivalence (e : R ≅ S) :
    SheafOfModules.{u} S ≌ SheafOfModules.{u} R :=
  CategoryTheory.Equivalence.mk (restrictScalars e.hom) (restrictScalars e.inv)
    (restrictCancelIso e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso e.hom e.inv e.hom_inv_id)

end Restriction

section OrdinaryExtension

variable {C : Type u} [Category.{u} C] {T : GrothendieckTopology C}
  {R S : Sheaf T CommRingCat.{u}}

private noncomputable def extensionSectionIso (e : R ≅ S)
    (M : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (U : Cᵒᵖ) :
    (changeOfRingsPresheaf.{u, u, u} e.hom M).obj U ≅
      ((restrictScalars ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).obj M).val.obj U := by
  let eU := (((sheafToPresheaf T RingCat.{u}).mapIso
    ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e)).app U)
  exact ((ModuleCat.extendRestrictScalarsAdj (e.hom.hom.app U).hom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      eU.ringCatIsoToRingEquiv).symm.toAdjunction).app
        (M.val.obj U)

private theorem extensionSectionIso_one (e : R ≅ S)
    (M : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (extensionSectionIso e M U).hom
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (e.hom.hom.app U).hom] m) = m := by
  let eU := (((sheafToPresheaf T RingCat.{u}).mapIso
    ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e)).app U)
  exact congrArg (fun k ↦ k m)
    ((ModuleCat.extendRestrictScalarsAdj (e.hom.hom.app U).hom).homEquiv_leftAdjointUniq_hom_app
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          eU.ringCatIsoToRingEquiv).symm.toAdjunction) (M.val.obj U))

attribute [local irreducible] extensionSectionIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionPresheafIso (e : R ≅ S)
    (M : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    changeOfRingsPresheaf.{u, u, u} e.hom M ≅
      ((restrictScalars ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).obj M).val := by
  refine PresheafOfModules.isoMk (extensionSectionIso e M) ?_
  intro U V f
  let : Module (R.obj.obj V)
      ((ModuleCat.restrictScalars
        (((sheafCompose T (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
          (M.val.obj V)) := inferInstanceAs (Module (R.obj.obj V) (M.val.obj V))
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (extensionSectionIso e M V).hom (changeOfRingsMap.{u, u, u} e.hom M f _) = _
  rw [show changeOfRingsMap.{u, u, u} e.hom M f
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (e.hom.hom.app U).hom] m) =
        (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (e.hom.hom.app V).hom] M.val.map f m from by
    simpa only [changeOfRingsMap, map_one] using
      Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} e.hom M f) 1 m]
  simp only [ModuleCat.comp_apply]
  rw [extensionSectionIso_one]
  exact congrArg (fun x ↦ M.val.map f x) (extensionSectionIso_one e M U m).symm

private theorem extensionPresheafIso_naturality (e : R ≅ S)
    {M N : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N) :
    (show changeOfRingsPresheaf.{u, u, u} e.hom M ⟶
        changeOfRingsPresheaf.{u, u, u} e.hom N from
      { app := fun U ↦ (ModuleCat.extendScalars (e.hom.hom.app U).hom).map (a.val.app U)
        naturality := changeOfRingsHom_naturality.{u, u, u} e.hom M a }) ≫
      (extensionPresheafIso e N).hom =
    (extensionPresheafIso e M).hom ≫
      ((restrictScalars ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).map a).val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply]
  change (extensionSectionIso e N U).hom
      ((ModuleCat.extendScalars (e.hom.hom.app U).hom).map (a.val.app U) _) = _
  erw [ModuleCat.ExtendScalars.map_tmul]
  rw [extensionSectionIso_one]
  exact congrArg (fun x ↦ a.val.app U x) (extensionSectionIso_one e M U m).symm

attribute [local irreducible] extensionPresheafIso

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafIso (e : R ≅ S)
    (M : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    changeOfRings.{u, u, u} e.hom M ≅
      (restrictScalars ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).obj M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso (extensionPresheafIso e M) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).counit.app
        ((restrictScalars ((sheafCompose T
          (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).obj M))

private theorem extensionSheafIso_naturality (e : R ≅ S)
    {M N : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N) :
    changeOfRingsHom.{u, u, u} e.hom M a ≫ (extensionSheafIso e N).hom =
    (extensionSheafIso e M).hom ≫
      (restrictScalars ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).map a := by
  dsimp only [extensionSheafIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  change (PresheafOfModules.sheafification _).map _ ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp]
  rw [extensionPresheafIso_naturality]
  rw [Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  exact congrArg (fun k ↦
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).map
        (extensionPresheafIso e M).hom ≫ k)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose T (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).counit.naturality
        ((restrictScalars ((sheafCompose T
          (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)).map a))

attribute [local irreducible] extensionSheafIso

private noncomputable def ordinaryExtensionIso (e : R ≅ S)
    (E : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (h : ∀ M, E.obj M = changeOfRings.{u, u, u} e.hom M)
    (ha : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} e.hom M a ≫ eqToHom (h N).symm) :
    E ≅ restrictScalars ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv) := by
  refine NatIso.ofComponents (fun M ↦ eqToIso (h M) ≪≫ extensionSheafIso e M) ?_
  intro M N a
  simp only [Iso.trans_hom, eqToIso.hom, ha, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [extensionSheafIso_naturality]

attribute [local irreducible] ordinaryExtensionIso

private noncomputable def derivedExtensionIso (e : R ≅ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (E : SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) [E.Additive]
    (h : ∀ M, E.obj M = changeOfRings.{u, u, u} e.hom M)
    (ha : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} e.hom M a ≫ eqToHom (h N).symm)
    (LF : DerivedCategory (SheafOfModules.{u} ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤
      DerivedCategory (SheafOfModules.{u} ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))] :
    let G := restrictScalars ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)
    letI : G.IsEquivalence :=
      (coefficientEquivalence ((sheafCompose T
        (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e).symm).isEquivalence_functor
    LF ≅ G.mapDerivedCategory := by
  let G := restrictScalars ((sheafCompose T
    (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)
  letI : G.IsEquivalence :=
    (coefficientEquivalence ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e).symm).isEquivalence_functor
  let i := ordinaryExtensionIso e E h ha
  let j : E.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory i.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory i.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, i.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, i.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  let d := G.mapDerivedCategoryFactorsh ≪≫ (Functor.isoWhiskerRight j
    DerivedCategory.Qh).symm
  have : G.mapDerivedCategory.IsLeftDerivedFunctor d.hom
      (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ d
  exact Functor.leftDerivedUnique G.mapDerivedCategory LF ε d.hom
    (HomotopyCategory.quasiIso _ (.up ℤ))

attribute [local irreducible] derivedExtensionIso

end OrdinaryExtension

private theorem lisse_of_iso
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    (B : Type u) [CommRing B]
    {F G : SheafOfModules.{u} (constantCoefficientRing T B)} (e : F ≅ G)
    (h : IsLocallyConstantFiniteTypeModules T B G) :
    IsLocallyConstantFiniteTypeModules T B F := by
  intro V
  obtain ⟨S, hS, hs⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨i⟩⟩ := hs U f hf
  exact ⟨M, hM, ⟨(overFunctor _ U).mapIso e ≪≫ i⟩⟩

/-- A bijective change of constant coefficients reflects finite locally constant
cohomology in each degree. Source: Stacks Project, Cohomology on Sites, Tags 06YY
and 094I (auxiliary; not a blueprint node).

Proof: the inverse ring isomorphism gives an exact inverse to restriction of scalars
on sheaves. Extension of scalars is naturally isomorphic to this exact inverse:
on sections, the maps are s tensor m maps to f inverse(s) times m and
m maps to 1 tensor m. Sheafification preserves these inverse maps. Thus derived
extension is the functor induced by this exact equivalence and commutes with
cohomology. Restriction to a slice commutes with the equivalence. A constant finite
module is carried to the same abelian group with the transported scalar action;
its finite generating set still generates, using bijectivity of f. Applying the
inverse coefficient equivalence to each local trivialization proves the assertion. -/
theorem locallyConstantFiniteTypeModules_of_scalarExtension_bijective
    {C : Type u} [Category.{u} C] (T : GrothendieckTopology C)
    {B D : Type u} [CommRing B] [CommRing D] (f : B →+* D)
    (hf : Function.Bijective f)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T B))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (constantCoefficientRing T D))]
    (K : DerivedCategory (SheafOfModules.{u} (constantCoefficientRing T B)))
    (i : ℤ)
    (h : IsLocallyConstantFiniteTypeModules T D
      ((DerivedCategory.homologyFunctor _ i).obj
        ((constantCoefficientScalarExtension T f).obj K))) :
    IsLocallyConstantFiniteTypeModules T B
      ((DerivedCategory.homologyFunctor _ i).obj K) := by
  let eBD := RingEquiv.ofBijective f hf
  let e : (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of B) ≅
      (constantSheaf T CommRingCat.{u}).obj (CommRingCat.of D) :=
    (constantSheaf T CommRingCat.{u}).mapIso eBD.toCommRingCatIso
  let p := derivedChangeOfRings e.hom
  let E := p.choose
  let he := p.choose_spec.choose
  have ha : ∀ {M N} (a : M ⟶ N), E.map a =
      eqToHom (he M) ≫ changeOfRingsHom e.hom M a ≫ eqToHom (he N).symm :=
    p.choose_spec.choose_spec.choose
  let hA := p.choose_spec.choose_spec.choose_spec.choose
  have : E.Additive := hA
  let hp := p.choose_spec.choose_spec.choose_spec.choose_spec
  let LF := hp.2.2.choose
  let ε := hp.2.2.choose_spec.choose
  have := hp.2.2.choose_spec.choose_spec.1
  let G := restrictScalars ((sheafCompose T
    (forget₂ CommRingCat.{u} RingCat.{u})).map e.inv)
  have : G.IsEquivalence :=
    (coefficientEquivalence ((sheafCompose T
      (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e).symm).isEquivalence_functor
  let d : LF ≅ G.mapDerivedCategory := derivedExtensionIso e E he ha LF ε
  have h' : IsLocallyConstantFiniteTypeModules T D
      ((DerivedCategory.homologyFunctor _ i).obj (LF.obj K)) := h
  let j := (G.mapDerivedCategoryHomologyFunctorIso i).app K ≪≫
    ((DerivedCategory.homologyFunctor _ i).mapIso (d.app K)).symm
  have hG := lisse_of_iso T D j h'
  have hres := locallyConstantFiniteTypeModules_restrictScalars_surjective T f hf.2 _ hG
  let c := (coefficientEquivalence ((sheafCompose T
    (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e)).counitIso.app
      ((DerivedCategory.homologyFunctor _ i).obj K)
  exact lisse_of_iso T B c.symm hres

end SheafOfModules
