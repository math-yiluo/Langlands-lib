/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Base change for bounded below right derived functors

Consider a square of additive functors between abelian categories
```
    B ───── G ─────▶ C
    │                │
    β                γ
    ▼                ▼
    B' ──── G' ────▶ C'
```
related by a natural transformation `e : G ⋙ γ ⟶ β ⋙ G'` (typically an isomorphism), where `β`
and `γ` are exact. We construct
the base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` of functors
`DerivedCategory.Plus B ⥤ DerivedCategory.Plus C'`, where `β⁺` and `γ⁺` are the functors
induced by `β` and `γ` on the bounded below derived categories
(`Functor.rightDerivedFunctorPlusBaseChange`), and the induced base change morphisms
`γ (R^p G Y) ⟶ R^p G' (β Y)` of the classical right derived functors
(`Functor.rightDerivedBaseChange`).

The morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` is the unique one compatible with the units: on a bounded
below complex `K` it is the composite of `e : γ G(K) ⟶ G' β(K)` with the unit
`G' β(K) ⟶ R⁺G'(β K)`. When `e` is an isomorphism, it is an isomorphism as soon as `β` sends
injective objects to `G'`-acyclic objects
(`Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic`), but in general it is not.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The base change morphism `G(K) ⟶ R⁺G'(β K)` at the level of bounded below homotopy
categories, from which `Functor.rightDerivedFunctorPlusBaseChange` is obtained by the universal
property of `R⁺G`: it is `γ G(K) ≅ G' β(K)` followed by the unit of `R⁺G'`. -/
noncomputable def rightDerivedFunctorPlusBaseChangeAux (e : G ⋙ γ ⟶ β ⋙ G') :
    G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ γ.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  Functor.whiskerLeft G.mapHomotopyCategoryPlus γ.mapDerivedCategoryPlusFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ γ))).hom
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e) DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (β ⋙ G'))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft β.mapHomotopyCategoryPlus G'.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight β.mapDerivedCategoryPlusFactorsh.inv G'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` attached to a natural transformation
`e : G ⋙ γ ⟶ β ⋙ G'` with `β` and `γ` exact. -/
noncomputable def rightDerivedFunctorPlusBaseChange (e : G ⋙ γ ⟶ β ⋙ G') :
    G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  (G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus).rightDerivedDesc
    (Functor.whiskerRight G.rightDerivedFunctorPlusUnith γ.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso B) _ (rightDerivedFunctorPlusBaseChangeAux e)

/-- The base change morphism is characterized by its compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorPlusBaseChange_fac (e : G ⋙ γ ⟶ β ⋙ G') :
    (Functor.whiskerRight G.rightDerivedFunctorPlusUnith γ.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusBaseChange e) =
    rightDerivedFunctorPlusBaseChangeAux e :=
  rightDerived_fac _ _ _ _ _


/-- **The base change morphism commutes with the shifts.** On complexes of injective objects it
is computed by `e` and the units of the right derived functors
(`Functor.rightDerivedFunctorPlusBaseChange_fac`), all of which commute with the shifts; every
bounded below complex is quasi-isomorphic to a complex of injective objects. In particular the
base change morphism is a morphism of triangulated functors. -/
instance commShift_rightDerivedFunctorPlusBaseChange (e : G ⋙ γ ⟶ β ⋙ G') :
    NatTrans.CommShift (rightDerivedFunctorPlusBaseChange e) ℤ := by
  let inj := (InjectiveObject.ι B).mapHomotopyCategoryPlus
  let α : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ γ.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight G.rightDerivedFunctorPlusUnith γ.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom
  have hfac : α ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh
      (rightDerivedFunctorPlusBaseChange e) = rightDerivedFunctorPlusBaseChangeAux e := by
    rw [← rightDerivedFunctorPlusBaseChange_fac e]
    ext K
    simp [α]
  have hβ : NatTrans.CommShift (rightDerivedFunctorPlusBaseChangeAux e) ℤ := by
    dsimp only [rightDerivedFunctorPlusBaseChangeAux]
    infer_instance
  have hα : NatTrans.CommShift α ℤ := by
    have := NatTrans.CommShift.whiskerRight (A := ℤ) G.rightDerivedFunctorPlusUnith
      (G := γ.mapDerivedCategoryPlus)
    dsimp only [α]
    infer_instance
  have : IsIso (Functor.whiskerLeft inj α) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K ↦ ?_)
    dsimp [α]
    infer_instance
  have h₁ : NatTrans.CommShift (Functor.whiskerLeft inj
      (Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusBaseChange e))) ℤ := by
    have : Functor.whiskerLeft inj
        (Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusBaseChange e)) =
        CategoryTheory.inv (Functor.whiskerLeft inj α) ≫ Functor.whiskerLeft inj
          (rightDerivedFunctorPlusBaseChangeAux e) := by
      rw [IsIso.eq_inv_comp, ← Functor.whiskerLeft_comp, ← hfac]
    rw [this]
    have : NatTrans.CommShift (Functor.whiskerLeft inj α) ℤ := inferInstance
    have : NatTrans.CommShift (CategoryTheory.inv (Functor.whiskerLeft inj α)) ℤ :=
      NatTrans.CommShift.of_isIso _ _
    have : NatTrans.CommShift (Functor.whiskerLeft inj (rightDerivedFunctorPlusBaseChangeAux e))
        ℤ := inferInstance
    infer_instance
  have h₂ : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusBaseChange e)) ℤ := by
    refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
    let E := DerivedCategory.Plus.injectiveObjectEquivalence B
    obtain ⟨f, hf⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K
      (inj.obj (E.inverse.obj (DerivedCategory.Plus.Qh.obj K)))
      inferInstance).2 (E.counitIso.inv.app (DerivedCategory.Plus.Qh.obj K))
    refine ⟨_, f, ?_⟩
    rw [Functor.comp_map, hf]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh (fun K ↦ ?_)
  exact ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso K).inv, inferInstance⟩

/-- The base change morphism `γ (R^p G Y) ⟶ R^p G' (β Y)` of the classical right derived
functors, natural in `Y`, attached to a natural transformation `e : G ⋙ γ ⟶ β ⋙ G'` with `β`
and `γ` exact. It is induced by `Functor.rightDerivedFunctorPlusBaseChange` through the
identifications `R^p G Y ≅ H^p(R⁺G(Y[0]))`. -/
noncomputable def rightDerivedBaseChange (e : G ⋙ γ ⟶ β ⋙ G') (p : ℕ) :
    G.rightDerived p ⋙ γ ⟶ β ⋙ G'.rightDerived p :=
  (Functor.isoWhiskerRight (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).symm
      γ).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0 ⋙ G.rightDerivedFunctorPlus)
      (γ.mapDerivedCategoryPlusHomologyFunctorIso p).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (Functor.whiskerRight (rightDerivedFunctorPlusBaseChange e)
        (DerivedCategory.Plus.homologyFunctor C' p)) ≫
    Functor.whiskerRight (β.mapDerivedCategoryPlusSingleFunctor 0).hom
      (G'.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C' p) ≫
    Functor.whiskerLeft β (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom

lemma rightDerivedBaseChange_app (e : G ⋙ γ ⟶ β ⋙ G') (p : ℕ) (Y : B) :
    (rightDerivedBaseChange e p).app Y =
      γ.map ((G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).inv.app Y) ≫
        (γ.mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
          (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map
          ((rightDerivedFunctorPlusBaseChange e).app
            ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map (G'.rightDerivedFunctorPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y)) ≫
        (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom.app
          (β.obj Y) := by
  simp only [rightDerivedBaseChange, NatTrans.comp_app, Iso.symm_hom, isoWhiskerRight_hom,
    whiskerRight_app, whiskerLeft_app, Functor.comp_map]
  rfl

/-- The base change morphism is compatible with the shifts on homology: through the
isomorphisms `H^a(K⟦m⟧) ≅ H^{a'}(K)`, the base change morphism on `H^a(R⁺G(Y⟦m⟧))` is the one on
`H^{a'}(R⁺G(Y))`. -/
@[reassoc]
lemma rightDerivedFunctorPlusBaseChange_homologyFunctor_shiftIso (e : G ⋙ γ ⟶ β ⋙ G')
    (Y : DerivedCategory.Plus B) (m a a' : ℤ) (h : m + a = a') :
    γ.map ((DerivedCategory.Plus.homologyFunctor C a).map
        ((G.rightDerivedFunctorPlus.commShiftIso m).hom.app Y) ≫
        ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso m a a' h).hom.app
          (G.rightDerivedFunctorPlus.obj Y)) ≫
      (γ.mapDerivedCategoryPlusHomologyFunctorIso a').hom.app (G.rightDerivedFunctorPlus.obj Y) ≫
      (DerivedCategory.Plus.homologyFunctor C' a').map
        ((rightDerivedFunctorPlusBaseChange e).app Y) =
    (γ.mapDerivedCategoryPlusHomologyFunctorIso a).hom.app (G.rightDerivedFunctorPlus.obj (Y⟦m⟧)) ≫
      (DerivedCategory.Plus.homologyFunctor C' a).map
        ((rightDerivedFunctorPlusBaseChange e).app (Y⟦m⟧)) ≫
      (DerivedCategory.Plus.homologyFunctor C' a).map
        (G'.rightDerivedFunctorPlus.map ((β.mapDerivedCategoryPlus.commShiftIso m).hom.app Y)) ≫
      (DerivedCategory.Plus.homologyFunctor C' a).map
        ((G'.rightDerivedFunctorPlus.commShiftIso m).hom.app (β.mapDerivedCategoryPlus.obj Y)) ≫
      ((DerivedCategory.Plus.homologyFunctor C' 0).shiftIso m a a' h).hom.app
        (G'.rightDerivedFunctorPlus.obj (β.mapDerivedCategoryPlus.obj Y)) := by
  have h₁ := γ.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_shiftIso m a a' h
    (G.rightDerivedFunctorPlus.obj Y)
  have h₂ := NatTrans.shift_app_comm (rightDerivedFunctorPlusBaseChange e) m Y
  simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at h₂
  have h₃ := (γ.mapDerivedCategoryPlusHomologyFunctorIso a).hom.naturality
    ((G.rightDerivedFunctorPlus.commShiftIso m).hom.app Y)
  have h₄ : (DerivedCategory.Plus.homologyFunctor C' a).map
      (((rightDerivedFunctorPlusBaseChange e).app Y)⟦m⟧') ≫
      ((DerivedCategory.Plus.homologyFunctor C' 0).shiftIso m a a' h).hom.app
        (G'.rightDerivedFunctorPlus.obj (β.mapDerivedCategoryPlus.obj Y)) =
      ((DerivedCategory.Plus.homologyFunctor C' 0).shiftIso m a a' h).hom.app
        (γ.mapDerivedCategoryPlus.obj (G.rightDerivedFunctorPlus.obj Y)) ≫
      (DerivedCategory.Plus.homologyFunctor C' a').map
        ((rightDerivedFunctorPlusBaseChange e).app Y) :=
    (DerivedCategory.Plus.homologyFunctor C' 0).shiftIso_hom_naturality m a a' h _
  have h₂' := congrArg (DerivedCategory.Plus.homologyFunctor C' a).map h₂
  simp only [Functor.comp_obj, Functor.comp_map] at h₃
  simp only [Functor.map_comp] at h₂'
  rw [γ.map_comp, Category.assoc, reassoc_of% h₁, ← h₄, reassoc_of% h₃, reassoc_of% h₂']

/-- **The base change morphism is invertible when `β` sends injectives to `G'`-acyclics.** If `G'`
is left exact and `β` sends injective objects to `G'`-acyclic objects, then the base change
morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` attached to `e : G ⋙ γ ≅ β ⋙ G'` is an isomorphism. On a
bounded below complex `T` of injectives it is the composite of `γ G(T) ≅ G' β(T)` with the unit
`G' β(T) ⟶ R⁺G'(β T)`, which is invertible since `β T` is a bounded below complex of
`G'`-acyclic objects. -/
theorem isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic [PreservesFiniteLimits G']
    (e : G ⋙ γ ≅ β ⋙ G') (h : ∀ (I : B) [Injective I], G'.rightAcyclic (β.obj I)) :
    IsIso (rightDerivedFunctorPlusBaseChange e.hom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  -- represent `X` by a bounded below complex of injectives `T`
  obtain ⟨K, ⟨eK⟩⟩ : ∃ K : HomotopyCategory.Plus B,
      Nonempty (DerivedCategory.Plus.Qh.obj K ≅ X) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso X⟩⟩
  obtain ⟨M, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  obtain ⟨a, _⟩ := M.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M a
  let T' := (InjectiveObject.ι B).mapCochainComplexPlus.obj T
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
  rw [← NatTrans.isIso_app_iff_of_iso _ eK,
    NatTrans.isIso_app_iff_of_iso _
      (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map i)))]
  set K' := (HomotopyCategory.Plus.quotient B).obj T'
  have hK' : ∀ n : ℤ, Injective (K'.obj.as.X n) := fun n ↦ (T.obj.X n).2
  have h₁ : IsIso (G.rightDerivedFunctorPlusUnith.app K') := inferInstance
  let LT : CochainComplex.Plus B' := ⟨(β.mapHomotopyCategoryPlus.obj K').obj.as,
    (HomotopyCategory.plus_quotient_obj_iff _).1 (β.mapHomotopyCategoryPlus.obj K').property⟩
  have h₂ : IsIso (G'.rightDerivedFunctorPlusUnith.app (β.mapHomotopyCategoryPlus.obj K')) :=
    G'.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic LT (fun n ↦ h (T'.obj.X n))
  have hfac := congr_app (rightDerivedFunctorPlusBaseChange_fac e.hom) K'
  have h₃ : IsIso ((rightDerivedFunctorPlusBaseChangeAux e.hom).app K') := by
    dsimp [rightDerivedFunctorPlusBaseChangeAux]
    infer_instance
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Functor.whiskerLeft_app] at hfac
  rw [← hfac] at h₃
  exact IsIso.of_isIso_comp_left (γ.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusUnith.app K')) _

end CategoryTheory.Functor
