/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.IntegralTowerScalarPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization

/-! # Derived quotient extension and the integral unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private theorem single_transpose
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ((adj.mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
        (CochainComplex.singleFunctor D 0).map f)) ≫
      (G.mapCochainComplexSingleFunctor 0).hom.app Y =
        (CochainComplex.singleFunctor C 0).map (adj.homEquiv _ _ f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [Adjunction.homEquiv_unit, Functor.mapCochainComplexSingleFunctor,
      CochainComplex.singleFunctor,
      Adjunction.mapHomologicalComplex, HomologicalComplex.singleMapHomologicalComplex,
      HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatIso.ofComponents_hom_app,
      dite_eq_left, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, eqToHom_refl,
      Functor.map_comp, Category.id_comp]
    change (adj.unit.app X ≫ G.map (𝟙 (F.obj X)) ≫ G.map f ≫ G.map (𝟙 Y)) ≫
      𝟙 _ = (adj.unit.app X ≫ 𝟙 _) ≫ G.map f ≫ 𝟙 _
    simp
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi).eq_of_src

private theorem normalize_single
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension F G) {X : C} {Y : D} (b : F.obj X ≅ Y)
    (h : IsIso (r.epsilon.app ((CochainComplex.singleFunctor C 0).obj X))) :
    ∃ a : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
        (DerivedCategory.singleFunctor D 0).obj Y,
      r.sourceNormalization a (r.adjunction.homEquiv _ _ b.hom) := by
  let := h
  let f : (F.mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj X) ⟶
        (CochainComplex.singleFunctor D 0).obj Y :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
    (CochainComplex.singleFunctor D 0).map b.hom
  let a : r.derived.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj Y :=
    asIso (r.epsilon.app ((CochainComplex.singleFunctor C 0).obj X)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X) ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso b
  have ha : a.hom = r.epsilon.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      DerivedCategory.Q.map f := by
    simp only [a, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom]
    change _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = _
    rw [← DerivedCategory.Q.map_comp]
  refine ⟨a, ?_⟩
  unfold DerivedExtension.sourceNormalization
  rw [ha]
  change (r.derivedAdjunction.homEquiv
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor D 0).obj Y)))
        (r.epsilon.app _ ≫ DerivedCategory.Q.map f) ≫
          (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map _)
  have ht := r.transpose ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor D 0).obj Y) f
  have hg : (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
      G.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor D 0).obj Y) ≫
        DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app Y) := by
    apply (cancel_epi
      (G.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor D 0).obj Y))).1
    simpa only [Iso.inv_hom_id_app_assoc, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors] using
      G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y
  rw [hg, ← Category.assoc, ht, ← DerivedCategory.Q.map_comp]
  change DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  exact congrArg DerivedCategory.Q.map (single_transpose r.adjunction b.hom)

private theorem derivedExtension_of_equivalence
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {A : Type u₂} [Category.{v₂} A] [Abelian A]
    {D : Type u₃} [Category.{v₃} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (e : C ≌ A) [e.functor.Additive] [e.inverse.Additive]
    (E : A ⥤ D) [E.Additive] (G : D ⥤ C) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : e.functor ⋙ E ⊣ G) (P : CochainComplex A ℤ → Prop)
    (hres : ∀ X : CochainComplex A ℤ,
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X), P Y ∧ QuasiIso s)
    (hpres : ∀ {X Y : CochainComplex A ℤ} (f : X ⟶ Y),
      P X → P Y → QuasiIso f →
        QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ r : DerivedExtension (e.functor ⋙ E) G, r.adjunction = adj ∧
      ∀ (X : CochainComplex C ℤ) (K : CochainComplex A ℤ),
        P K → Nonempty ((e.mapHomologicalComplex (.up ℤ)).functor.obj X ≅ K) →
          IsIso (r.epsilon.app X) := by
  let ec := e.mapHomologicalComplex (.up ℤ)
  let H := E.mapHomologicalComplex (.up ℤ)
  let P' : CochainComplex C ℤ → Prop := fun X ↦
    ∃ K : CochainComplex A ℤ, P K ∧ Nonempty (ec.functor.obj X ≅ K)
  have hres' : ∀ X : CochainComplex C ℤ,
      ∃ (Y : CochainComplex C ℤ) (s : Y ⟶ X), P' Y ∧ QuasiIso s := by
    intro X
    obtain ⟨K, s, hK, hs⟩ := hres (ec.functor.obj X)
    let := hs
    let : QuasiIso (ec.inverse.map s) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology s e.inverse
    refine ⟨ec.inverse.obj K, ec.inverse.map s ≫ ec.unitIso.inv.app X,
      ⟨K, hK, ⟨ec.counitIso.app K⟩⟩, ?_⟩
    infer_instance
  have hpres' : ∀ {X Y : CochainComplex C ℤ} (f : X ⟶ Y),
      P' X → P' Y → QuasiIso f →
      QuasiIso (((e.functor ⋙ E).mapHomologicalComplex (.up ℤ)).map f) := by
    rintro X Y f ⟨K, hK, ⟨a⟩⟩ ⟨L, hL, ⟨b⟩⟩ hf
    let := hf
    let : QuasiIso (ec.functor.map f) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology f e.functor
    let g := a.inv ≫ ec.functor.map f ≫ b.hom
    have hg : QuasiIso g := by
      dsimp only [g]
      infer_instance
    have hEg : QuasiIso (H.map g) := hpres g hK hL hg
    change QuasiIso (H.map (ec.functor.map f))
    apply (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (H.mapIso a) (H.mapIso b) ?_)).2 hEg
    simp [g, Functor.map_comp]
  obtain ⟨_, L, ε, huniv, hcomp, d, hd⟩ :=
    Adjunction.exists_leftDerived_adjunction (e.functor ⋙ E) G adj P' hres' hpres'
  refine ⟨{ adjunction := adj
            derived := L
            epsilon := ε
            universal := huniv
            derivedAdjunction := d
            transpose := ?_ }, rfl, ?_⟩
  · intro X Y f
    rw [hd]
    simp
  · intro X K hK he
    exact hcomp X ⟨K, hK, he⟩

/-- Any ring system admits derived extension from abelian towers, with its unit comparison
normalized by the actual integer generator.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
and NormalizedKummerReduction proof steps 1--2.
(blueprint: lem-sfb-integral-unit-reduction).

Proof: regard abelian towers as sheaves of modules over the constant integer ring on
`coefficientSequenceTopology`. Forgetting the action of the system ring is restriction
along its unique integer-ring map, and retains exactly the sections, restrictions,
transitions and morphisms required by Forget. Sheafified extension of scalars is left
adjoint to this functor. The K-flat change-of-rings construction gives its universal
cochain derived pair; derive the adjunction against exact restriction. The ordinary
unit on a representative is the tensor generator x mapped to 1 tensor x. Therefore the
derived adjunction has the representative transpose formula required by Reduction.
The integer unit concentrated in degree zero is K-flat. Its comparison counit is
invertible, and multiplication identifies its ordinary scalar extension with the system
ring's unit module. Composing these two comparisons gives a. The representative
transpose formula identifies its adjunct with the ordinary integer-ring map. On every
constant integer section this map is integer multiplication of one, so uniqueness in
integerGenerator_existsUnique identifies it with integerGenerator. These constructions
also apply to the empty scheme and to ring systems with zero rings. -/
theorem exists_integralUnitReduction (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    ∃ (r : Reduction T B)
      (a : r.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj (integers T)) ≅
        unit T B),
      r.model.sourceNormalization a (integerGenerator T B r.forget) := by
  classical
  let J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology T)
  obtain ⟨R, φ, e, he, ⟨z⟩, F, hord⟩ := exists_integralTowerScalarPresentation T B
  let A := ringedSiteModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let : e.functor.Additive := he
  let : e.inverse.Additive := e.inverse_additive
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  obtain ⟨M⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u + 1, u, u + 1} φ
  obtain ⟨adj, b, hb⟩ := hord M.E M.obj_eq M.map_eq
  have hres : ∀ X : CochainComplex A ℤ,
      ∃ (Y : CochainComplex A ℤ) (s : Y ⟶ X),
        Y.IsKFlatIndependentCoefficients (R := R) ∧ QuasiIso s := by
    intro X
    obtain ⟨K, s, hK, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    exact ⟨K, s, hK, hs⟩
  obtain ⟨model, hmAdj, hcomp⟩ := derivedExtension_of_equivalence e M.E F.F adj
    (fun K ↦ K.IsKFlatIndependentCoefficients (R := R)) hres M.preserves
  let U : A := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  have hk : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((CochainComplex.singleFunctor A 0).obj U) := by
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    have hlim : PreservesFiniteLimits (MonoidalCategory.tensorRight U) :=
      preservesFiniteLimits_of_natIso (MonoidalCategory.rightUnitorNatIso A).symm
    have hcol : PreservesFiniteColimits (MonoidalCategory.tensorRight U) :=
      preservesFiniteColimits_of_natIso (MonoidalCategory.rightUnitorNatIso A).symm
    let := hlim
    let := hcol
    have hsiteLim : PreservesFiniteLimits
        (SheafOfModules.siteSheafTensorRight (A := R) U) :=
      preservesFiniteLimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R U).symm
    have hsiteCol : PreservesFiniteColimits
        (SheafOfModules.siteSheafTensorRight (A := R) U) :=
      preservesFiniteColimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R U).symm
    have hflat : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := J) (R := R) U := by
      change PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight (A := R) U) ∧
        PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight (A := R) U)
      exact ⟨hsiteLim, hsiteCol⟩
    exact (SheafOfModules.FlatSingleDerivedNormalization.flat_single_derived_normalization
      R U hflat).choose
  have hu : (e.mapHomologicalComplex (.up ℤ)).functor.obj
      ((CochainComplex.singleFunctor (Ab T) 0).obj (integers T)) ≅
        (CochainComplex.singleFunctor A 0).obj U :=
    (HomologicalComplex.singleMapHomologicalComplex e.functor (.up ℤ) 0).app
      (integers T) ≪≫ (CochainComplex.singleFunctor A 0).mapIso z
  let r : Reduction T B :=
    { forget := F
      ordinary := e.functor ⋙ M.E
      model := model }
  obtain ⟨a, ha⟩ := normalize_single model b
    (hcomp ((CochainComplex.singleFunctor (Ab T) 0).obj (integers T))
      ((CochainComplex.singleFunctor A 0).obj U) hk ⟨hu⟩)
  refine ⟨r, a, ?_⟩
  change model.sourceNormalization a (integerGenerator T B F)
  rw [hmAdj, hb] at ha
  exact ha

end AlgebraicGeometry.ProEtale.SpTowerClasses
