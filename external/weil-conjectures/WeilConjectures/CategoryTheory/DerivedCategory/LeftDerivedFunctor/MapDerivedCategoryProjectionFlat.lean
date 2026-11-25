/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.FlatLazard
public import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The projection map at flat modules placed in degree zero

Let `F : Mod_Λ ⥤ D` be an exact strong monoidal functor to a monoidal Grothendieck abelian
category, preserving flat objects and left adjoint, let `Γ : D ⥤ Mod_Λ` be a left exact functor
whose derived functors `RᵠΓ` commute with filtered colimits, and let `adj : D(F) ⊣ RΓ`. For `E`
bounded below and `M` a flat `Λ`-module, the projection map
`τ_E : RΓ E ⊗ᴸ M[0] ⟶ RΓ (E ⊗ᴸ D(F) M[0])`
(`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`) is an isomorphism
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat`).

Indeed it is an isomorphism at the unit, hence at the finite free modules `Λ^k`, and both sides,
in a fixed degree `n`, commute with filtered colimits of flat modules: writing `RΓ E` as `Q(L)`
for a K-flat complex `L`, the source is `Hⁿ(L ⊗ M)`; writing `E` as `Q(I)` for a bounded below
complex `I` of injective objects, the target is `Hⁿ(Γ(I ⊗ F M))`, the complex `I ⊗ F M` being a
bounded below complex of `Γ`-acyclic objects. By Lazard's theorem
(`ModuleCat.FinFreeOver.isColimitCocone`), a flat module is a filtered colimit of finite free
modules.
-/

@[expose] public section

universe u u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The finite free module `R^k` is a biproduct of `k` copies of `R`. -/
noncomputable def finsuppIsoBiproduct (k : ℕ) :
    ModuleCat.of R (Fin k →₀ R) ≅ ⨁ fun _ : Fin k ↦ ModuleCat.of R R :=
  (Finsupp.linearEquivFunOnFinite R R (Fin k)).toModuleIso ≪≫
    (ModuleCat.biproductIsoPi fun _ : Fin k ↦ ModuleCat.of R R).symm

end ModuleCat

namespace CategoryTheory

namespace Functor

/-- For a complex `L`, the functor `M ↦ L ⊗ M` (tensoring termwise on the right) from `C` to
cochain complexes. -/
@[simps]
noncomputable def tensorRightComplex {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] (L : CochainComplex C ℤ) :
    C ⥤ CochainComplex C ℤ where
  obj M := (((curriedTensor C).flip.obj M).mapHomologicalComplex (.up ℤ)).obj L
  map f := (NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map f) (.up ℤ)).app L
  map_id M := by
    ext
    simp
  map_comp f g := by
    ext
    simp

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    (L : CochainComplex C ℤ) (n : ℤ) [MonoidalClosed C] (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
  preservesColimitsOfShape_of_natIso (F := tensorLeft (L.X n)) (NatIso.ofComponents
    (fun _ ↦ Iso.refl _) (by intros; simp))

instance {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
    [MonoidalClosed C] (L : CochainComplex C ℤ) (J : Type*) [Category* J] :
    PreservesColimitsOfShape J (tensorRightComplex L) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun _ ↦ inferInstance

end Functor

namespace DerivedCategory

variable {C : Type u₂} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]

/-- The single complex `X[0]` tensored on the left by a complex `L` is `L` tensored termwise by
`X`, naturally in `X`. -/
noncomputable def singleCompTensorLeftIso (L : CochainComplex C ℤ) :
    HomologicalComplex.single C (.up ℤ) 0 ⋙ tensorLeft L ≅ Functor.tensorRightComplex L :=
  NatIso.ofComponents (fun X ↦ CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) X L)
    (fun f ↦ CochainComplex.mapBifunctorSingle₂Iso_hom_naturality₂ (curriedTensor C) f L)

/-- The comparison `Q(L) ⊗ᴸ X[0] ⟶ Q(L ⊗ X)`, natural in `X`: the lax monoidal structure of
`Qh`, followed by the identification of `L ⊗ X[0]` with `L` tensored termwise by `X`. It is an
isomorphism at flat objects `X`
(`DerivedCategory.isIso_tensorSingleToTensorRightComplex_app`). -/
noncomputable def tensorSingleToTensorRightComplex (L : CochainComplex C ℤ) :
    singleFunctor C 0 ⋙ (curriedTensor (DerivedCategory C)).obj (Q.obj L) ⟶
      Functor.tensorRightComplex L ⋙ Q :=
  Functor.whiskerLeft (singleFunctor C 0)
      ((curriedTensor _).map ((quotientCompQhIso C).inv.app L)) ≫
    (Functor.whiskerRight ((singleFunctorIsoCompQ C 0).hom ≫
      Functor.whiskerLeft (HomologicalComplex.single C (.up ℤ) 0) (quotientCompQhIso C).inv) _ :
        _ ⟶ (HomologicalComplex.single C (.up ℤ) 0 ⋙ HomotopyCategory.quotient C (.up ℤ)) ⋙
          Qh ⋙ (curriedTensor _).obj (Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj L))) ≫
    Functor.whiskerLeft (HomologicalComplex.single C (.up ℤ) 0 ⋙
      HomotopyCategory.quotient C (.up ℤ))
        (tensorLeftCounit ((HomotopyCategory.quotient C (.up ℤ)).obj L)) ≫
    (Functor.whiskerRight (Functor.whiskerLeft (HomologicalComplex.single C (.up ℤ) 0)
      (Functor.Monoidal.commTensorLeft (HomotopyCategory.quotient C (.up ℤ)) L).hom) Qh :
        (HomologicalComplex.single C (.up ℤ) 0 ⋙ HomotopyCategory.quotient C (.up ℤ) ⋙
          tensorLeft ((HomotopyCategory.quotient C (.up ℤ)).obj L)) ⋙ Qh ⟶ _) ≫
    (Functor.whiskerRight (singleCompTensorLeftIso L).hom
      (HomotopyCategory.quotient C (.up ℤ) ⋙ Qh) :
        (HomologicalComplex.single C (.up ℤ) 0 ⋙ tensorLeft L) ⋙
          HomotopyCategory.quotient C (.up ℤ) ⋙ Qh ⟶ _) ≫
    Functor.whiskerLeft (Functor.tensorRightComplex L) (quotientCompQhIso C).hom

lemma isIso_tensorSingleToTensorRightComplex_app (L : CochainComplex C ℤ) (X : C)
    (hX : ObjectProperty.flat X) :
    IsIso ((tensorSingleToTensorRightComplex L).app X) := by
  have : IsIso ((tensorLeftCounit ((HomotopyCategory.quotient C (.up ℤ)).obj L)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj X))) :=
    Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      ((CochainComplex.kFlat_single_obj_iff_flat X 0).2 hX))
  dsimp only [tensorSingleToTensorRightComplex, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  refine IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' this (IsIso.comp_isIso' inferInstance
      (IsIso.comp_isIso' inferInstance inferInstance))))

end DerivedCategory

namespace Functor

variable {Λ : Type (u + 1)} [CommRing Λ]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {F : ModuleCat.{u + 1} Λ ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {Γ : D ⥤ ModuleCat.{u + 1} Λ} [Γ.Additive] [PreservesFiniteLimits Γ]

omit [IsGrothendieckAbelian.{u + 1} D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] in
/-- The tensor product of an injective object `I` with the image under `F` of a finite free
module is injective: it is a finite product of copies of `I`. -/
lemma injective_tensorObj_obj_finsupp (I : D) [Injective I] (k : ℕ) :
    Injective (I ⊗ F.obj (ModuleCat.of Λ (Fin k →₀ Λ))) := by
  have : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  have : (F ⋙ tensorLeft I).Additive := inferInstance
  refine Injective.of_iso ?_ (inferInstance : Injective (∏ᶜ fun _ : Fin k ↦ I))
  exact (biproduct.isoProduct _).symm ≪≫
    (biproduct.mapIso fun _ ↦ (ρ_ I).symm ≪≫
      whiskerLeftIso I (Functor.Monoidal.εIso F)) ≪≫
    ((F ⋙ tensorLeft I).mapBiproduct _).symm ≪≫
    (F ⋙ tensorLeft I).mapIso (ModuleCat.finsuppIsoBiproduct Λ k).symm

omit [PreservesFiniteLimits Γ] [BraidedCategory D] [HasFunctorialFlatResolution D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesFlat] in
/-- Let `I` be injective and `M` a flat module. If the derived functors of `Γ` commute with
filtered colimits, `I ⊗ F M` is `Γ`-acyclic: `M` is a filtered colimit of finite free modules
`Λ^k`, and the objects `I ⊗ F(Λ^k)` are injective. -/
lemma rightAcyclic_tensorObj_obj_of_flat
    (hΓ : ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (q : ℕ),
      PreservesColimitsOfShape J (Γ.rightDerived q))
    (I : D) [Injective I] (M : ModuleCat.{u + 1} Λ) [Module.Flat Λ M] :
    Γ.rightAcyclic (I ⊗ F.obj M) := fun q ↦ by
  have := hΓ (ModuleCat.FinFreeOver M) (q + 1)
  have hc := isColimitOfPreserves (F ⋙ tensorLeft I ⋙ Γ.rightDerived (q + 1))
    (ModuleCat.FinFreeOver.isColimitCocone M)
  refine hc.isZero_pt (Functor.isZero _ fun A ↦ ?_)
  have := injective_tensorObj_obj_finsupp (F := F) I A.n
  exact Γ.isZero_rightDerived_obj_injective_succ q (I ⊗ F.obj (ModuleCat.of Λ (Fin A.n →₀ Λ)))

end Functor

end CategoryTheory

namespace CategoryTheory.Functor

section Unit

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasInjectiveResolutions A] [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions A] (Γ : A ⥤ B) [Γ.Additive] [PreservesFiniteLimits Γ]

/-- **Bounded below acyclic complexes compute the right derived functor**: the unit
`Γ(T) ⟶ RΓ(T)` is an isomorphism at a bounded below complex `T` of `Γ`-acyclic objects. -/
lemma isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE (T : CochainComplex A ℤ) (a : ℤ)
    [T.IsStrictlyGE a] (hT : ∀ n, Γ.rightAcyclic (T.X n)) :
    IsIso (Γ.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj T)) := by
  obtain ⟨I, ι, _, hI, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective T a
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have := Γ.quasiIso_map_of_rightAcyclic ι a hT (fun n ↦ rightAcyclic_of_injective _)
  have h₁ : IsIso (Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map ι)) :=
    Localization.inverts Qh (HomotopyCategory.quasiIso A _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₂ : IsIso ((Γ.mapHomotopyCategory (.up ℤ) ⋙ Qh).map
      ((HomotopyCategory.quotient A (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts Qh (HomotopyCategory.quasiIso B _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))
  have h₃ : IsIso ((Qh ⋙ Γ.rightDerivedFunctor).map
      ((HomotopyCategory.quotient A (.up ℤ)).map ι)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have h₄ : IsIso (Γ.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient A (.up ℤ)).obj I)) := inferInstance
  exact IsIso.of_isIso_fac_right (h := (Γ.mapHomotopyCategory (.up ℤ) ⋙ Qh).map
    ((HomotopyCategory.quotient A (.up ℤ)).map ι) ≫ Γ.rightDerivedFunctorUnit.app _)
    (Γ.rightDerivedFunctorUnit.naturality _).symm

/-- The unit `Q(Γ T) ⟶ RΓ(Q T)` is an isomorphism at a bounded below complex `T` of `Γ`-acyclic
objects. -/
lemma isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE (T : CochainComplex A ℤ) (a : ℤ)
    [T.IsStrictlyGE a] (hT : ∀ n, Γ.rightAcyclic (T.X n)) :
    IsIso (Γ.rightDerivedFunctorUnitQ T) := by
  have := Γ.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE T a hT
  dsimp only [rightDerivedFunctorUnitQ]
  infer_instance

end Unit

open DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  {F : ModuleCat.{u + 1} Λ ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  {Γ : D ⥤ ModuleCat.{u + 1} Λ} [Γ.Additive] [PreservesFiniteLimits Γ]
  (adj : F.mapDerivedCategory ⊣ Γ.rightDerivedFunctor)

omit [PreservesFiniteLimits Γ] in
/-- The projection map is an isomorphism at the finite free modules placed in degree `0`, the
finite biproducts of copies of the unit. -/
lemma isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_finsupp (E : DerivedCategory D)
    (k : ℕ) : IsIso ((mapDerivedCategoryProjectionMap adj E).app
      ((singleFunctor _ 0).obj (ModuleCat.of Λ (Fin k →₀ Λ)))) := by
  let τ := Functor.whiskerLeft (singleFunctor (ModuleCat.{u + 1} Λ) 0)
    (mapDerivedCategoryProjectionMap adj E)
  have : (Γ.rightDerivedFunctor).Additive := adj.right_adjoint_additive
  have := DerivedCategory.additive_tensorLeft (Γ.rightDerivedFunctor.obj E)
  have := DerivedCategory.additive_tensorLeft E
  have hunit : IsIso (τ.app (ModuleCat.of Λ Λ)) :=
    (NatTrans.isIso_app_iff_of_iso (mapDerivedCategoryProjectionMap adj E)
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ))).2
        (isIso_mapDerivedCategoryProjectionMap_app_tensorUnit adj E)
  exact (NatTrans.isIso_app_iff_of_iso (mapDerivedCategoryProjectionMap adj E)
    ((singleFunctor _ 0).mapIso (ModuleCat.finsuppIsoBiproduct Λ k))).2
      (NatTrans.isIso_app_biproduct τ _ fun _ ↦ hunit)

/-- If the derived functors of `Γ` commute with filtered colimits, the projection map
`RΓ E ⊗ᴸ M[0] ⟶ RΓ (E ⊗ᴸ D(F) M[0])` is an isomorphism for every bounded below `E` and every
flat module `M`: both sides commute in each degree with filtered colimits of flat modules, and
`M` is a filtered colimit of finite free modules. -/
theorem isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat
    (hΓ : ∀ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (q : ℕ),
      PreservesColimitsOfShape J (Γ.rightDerived q))
    (E : DerivedCategory D) (a : ℤ) [E.IsGE a] (M : ModuleCat.{u + 1} Λ)
    (hM : ObjectProperty.flat M) :
    IsIso ((mapDerivedCategoryProjectionMap adj E).app ((singleFunctor _ 0).obj M)) := by
  have : Module.Flat Λ M := (ModuleCat.flat_iff_flat M).1 hM
  let τ := mapDerivedCategoryProjectionMap adj E
  let L := Q.objPreimage (Γ.rightDerivedFunctor.obj E)
  let eL : Q.obj L ≅ Γ.rightDerivedFunctor.obj E := Q.objObjPreimageIso _
  obtain ⟨I₀, _, ⟨e₀⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  obtain ⟨I, ι, _, hI, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective I₀ a
  have : IsIso (Q.map ι) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  let eI : E ≅ Q.obj I := e₀ ≪≫ asIso (Q.map ι)
  let c := ModuleCat.FinFreeOver.cocone M
  have hc := ModuleCat.FinFreeOver.isColimitCocone M
  have hflat (X : ModuleCat.{u + 1} Λ) [Module.Flat Λ X] : ObjectProperty.flat X :=
    (ModuleCat.flat_iff_flat X).2 inferInstance
  have hflat' (A : ModuleCat.FinFreeOver M) :
      ObjectProperty.flat ((ModuleCat.FinFreeOver.diagram M).obj A) :=
    hflat (ModuleCat.of Λ (Fin A.n →₀ Λ))
  -- the objects `I ⊗ F X` are `Γ`-acyclic for `X` flat
  have hacyc (X : ModuleCat.{u + 1} Λ) (hX : ObjectProperty.flat X) (p : ℤ) :
      Γ.rightAcyclic (((Functor.tensorRightComplex I).obj (F.obj X)).X p) := by
    have : Module.Flat Λ X := (ModuleCat.flat_iff_flat X).1 hX
    exact rightAcyclic_tensorObj_obj_of_flat hΓ (I.X p) X
  have hge (X : ModuleCat.{u + 1} Λ) :
      CochainComplex.IsStrictlyGE ((Functor.tensorRightComplex I).obj (F.obj X)) a :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun p hp ↦
      (tensorRight (F.obj X)).map_isZero (CochainComplex.isZero_of_isStrictlyGE I a p hp)
  have : PreservesColimitsOfShape (ModuleCat.FinFreeOver M) Γ := by
    have := hΓ (ModuleCat.FinFreeOver M) 0
    exact preservesColimitsOfShape_of_natIso Γ.rightDerivedZeroIsoSelf
  have : PreservesColimitsOfShape (ModuleCat.FinFreeOver M)
      (Γ.mapHomologicalComplex (ComplexShape.up ℤ)) :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun p ↦
      preservesColimitsOfShape_of_natIso (F := HomologicalComplex.eval _ _ p ⋙ Γ)
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp))
  rw [DerivedCategory.isIso_iff]
  intro n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n
  let P := singleFunctor (ModuleCat.{u + 1} Λ) 0 ⋙
    (curriedTensor _).obj (Γ.rightDerivedFunctor.obj E) ⋙ H
  let R := singleFunctor (ModuleCat.{u + 1} Λ) 0 ⋙
    ((F.mapDerivedCategory ⋙ (curriedTensor _).obj E) ⋙ Γ.rightDerivedFunctor) ⋙ H
  let τn : P ⟶ R := Functor.whiskerLeft (singleFunctor _ 0) (Functor.whiskerRight τ H)
  -- the source commutes with the filtered colimit
  let βP : P ⟶ Functor.tensorRightComplex L ⋙ Q ⋙ H :=
    Functor.whiskerLeft (singleFunctor _ 0)
      (Functor.whiskerRight ((curriedTensor _).map eL.inv) H) ≫
    Functor.whiskerRight (tensorSingleToTensorRightComplex L) H
  have hβP (X : ModuleCat.{u + 1} Λ) (hX : ObjectProperty.flat X) : IsIso (βP.app X) := by
    have := isIso_tensorSingleToTensorRightComplex_app L X hX
    dsimp only [βP, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have hP : IsColimit (P.mapCocone c) :=
    isColimitMapCoconeOfNatTrans βP c (fun A ↦ hβP _ (hflat' A)) (hβP M hM)
      (IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft _
        (DerivedCategory.homologyFunctorFactors _ n)).symm (isColimitOfPreserves _ hc))
  -- the target commutes with the filtered colimit
  let T := F ⋙ Functor.tensorRightComplex I ⋙ Q ⋙ Γ.rightDerivedFunctor ⋙ H
  let β₂ : F ⋙ Functor.tensorRightComplex I ⋙ Γ.mapHomologicalComplex _ ⋙ Q ⋙ H ⟶ T :=
    { app X := H.map (Γ.rightDerivedFunctorUnitQ ((Functor.tensorRightComplex I).obj (F.obj X)))
      naturality X Y f := by
        dsimp [T]
        rw [← H.map_comp, ← H.map_comp, rightDerivedFunctorUnitQ_naturality] }
  have hβ₂ (X : ModuleCat.{u + 1} Λ) (hX : ObjectProperty.flat X) : IsIso (β₂.app X) := by
    have := hge X
    have := Γ.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE _ a (hacyc X hX)
    exact Functor.map_isIso H
      (Γ.rightDerivedFunctorUnitQ ((Functor.tensorRightComplex I).obj (F.obj X)))
  let β₃ : R ⟶ T :=
    Functor.whiskerRight (F.mapDerivedCategorySingleFunctor 0).hom
      ((curriedTensor _).obj E ⋙ Γ.rightDerivedFunctor ⋙ H) ≫
    Functor.whiskerLeft (F ⋙ singleFunctor D 0)
      (Functor.whiskerRight ((curriedTensor _).map eI.hom) (Γ.rightDerivedFunctor ⋙ H)) ≫
    Functor.whiskerLeft F (Functor.whiskerRight (tensorSingleToTensorRightComplex I)
      (Γ.rightDerivedFunctor ⋙ H))
  have hβ₃ (X : ModuleCat.{u + 1} Λ) (hX : ObjectProperty.flat X) : IsIso (β₃.app X) := by
    have := isIso_tensorSingleToTensorRightComplex_app I (F.obj X)
      (Functor.PreservesFlat.flat_obj (F := F) hX)
    dsimp only [β₃, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have hT : IsColimit (T.mapCocone c) :=
    isColimitMapCoconeOfNatTrans' β₂ c (fun A ↦ hβ₂ _ (hflat' A)) (hβ₂ M hM)
      (IsColimit.mapCoconeEquiv (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
        (Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors _ n)))).symm
        (isColimitOfPreserves _ hc))
  have hR : IsColimit (R.mapCocone c) :=
    isColimitMapCoconeOfNatTrans β₃ c (fun A ↦ hβ₃ _ (hflat' A)) (hβ₃ M hM) hT
  exact NatTrans.isIso_app_of_isColimit_mapCocone τn c hP hR fun A ↦
    have := isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_finsupp adj E A.n
    Functor.map_isIso H
      (τ.app ((singleFunctor _ 0).obj (ModuleCat.of Λ (Fin A.n →₀ Λ))))

end CategoryTheory.Functor
