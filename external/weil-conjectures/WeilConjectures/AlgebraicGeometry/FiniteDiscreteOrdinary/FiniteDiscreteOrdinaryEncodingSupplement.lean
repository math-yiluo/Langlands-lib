/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding

/-! # Finite discrete internal and ordinary coefficients

Source: blueprint main-20261015, chap-Construction-of-f,
theorem-f-shriek-finite-coefficients, coefficient-identification step
(blueprint: lem-sf-finite-discrete-normalized-encoding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- The canonical shift comparison on the actual termwise derived functor.
Source: blueprint proof step 4 and Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
instance Encoding.fixedDerivedShift {T : Scheme.{u}} (e : Encoding A T) :
    e.fixedDerived.functor.CommShift ℤ := by
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  change (e.ordinary.trans e.fixed).functor.mapDerivedCategory.CommShift ℤ
  infer_instance

/-- The ordinary bounded constructible finite-Tor predicate, without a fixed Tor bound.
Source: definition-constructible-sheaves, final paragraph, and blueprint proof steps 7 and 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryCtf (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  ordinaryBoundedConstructible A T ⊓ fun K ↦ DerivedCategory.finiteTorAmplitude _ K

private instance pointConstants_locallySurjective [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (pointConstants A) where
  imageSieve_mem {S} s := by
    let f : C(S, A) := s.down
    have hclosed (a : A) : IsClosed {x : S | f x = a} :=
      isClosed_singleton.preimage f.continuous
    let (a : A) : CompactSpace {x : S // f x = a} :=
      isCompact_iff_compactSpace.mp (hclosed a).isCompact
    let := Fintype.ofFinite A
    let e := (Fintype.equivFin A).symm
    let U (i : Fin (Fintype.card A)) : Profinite.{u} :=
      Profinite.of {x : S // f x = e i}
    let incl (i : Fin (Fintype.card A)) : U i ⟶ S :=
      CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtype_val⟩
    have hι : EffectiveEpiFamily U incl :=
      Profinite.effectiveEpiFamily_of_jointly_surjective U incl
        (fun x ↦ ⟨e.symm (f x), ⟨x, (e.apply_symm_apply (f x)).symm⟩, rfl⟩)
    refine coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
      ⟨Fin (Fintype.card A), inferInstance, U, incl, hι, ?_⟩
    intro i
    refine ⟨ULift.up (e i), ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact x.property.symm

private instance pointConstants_locallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (pointConstants A) where
  equalizerSieve_mem {S} a b h := by
    by_cases hab : a = b
    · subst b
      exact (coherentTopology Profinite).superset_covering
        (fun _ _ _ ↦ rfl) ((coherentTopology Profinite).top_mem _)
    · have : IsEmpty S.unop := ⟨fun x ↦ hab (ULift.ext (congrArg
        (fun t : ULift.{u + 1} C(S.unop, A) ↦ t.down x) h))⟩
      let U : PEmpty → Profinite.{u} := PEmpty.elim
      let incl : ∀ i, U i ⟶ S.unop := fun i ↦ i.elim
      have hι : EffectiveEpiFamily U incl :=
        Profinite.effectiveEpiFamily_of_jointly_surjective U incl (fun x ↦ isEmptyElim x)
      exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily _
        ⟨PEmpty, inferInstance, U, incl, hι, fun i ↦ i.elim⟩

private theorem canonicalAbelianMap_isIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    IsIso (canonicalAbelianMap A T) := by
  let J := coherentTopology Profinite.{u}
  have hφ : J.W (A := Ab.{u + 1}) (pointConstants A) :=
    J.W_of_isLocallyBijective (pointConstants A)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map (pointConstants A)) :=
    (J.W_iff _).mp hφ
  have h : ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ (coefficient A)).symm
      (pointConstants A) =
      (presheafToSheaf J Ab.{u + 1}).map (pointConstants A) ≫
        (sheafificationAdjunction J Ab.{u + 1}).counit.app (coefficient A) := rfl
  unfold canonicalAbelianMap
  rw [h]
  infer_instance

private def pointRingConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A)) ⟶
      Profinite.continuousCoefficientRingPresheaf A where
  app S := RingCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantPresheafMonObj :
    (Functor.const Profinite.{u}ᵒᵖ).monObjObj (AddCommGrpCat.of (ULift.{u + 1} A)) =
      Functor.monObjCompForget₂
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) := by
  apply MonObj.ext
  ext S
  rfl

private theorem monHomInvExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (e : M ≅ N)
    (h : @IsMonHom _ _ _ M N mM mN e.hom) :
    @IsMonHom _ _ _ N M mN mM e.inv := by
  let := mM
  let := mN
  let := h
  infer_instance

private theorem monHomCompExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N O : C} (mM : MonObj M) (mN : MonObj N) (mO : MonObj O)
    (f : M ⟶ N) (g : N ⟶ O)
    (hf : @IsMonHom _ _ _ M N mM mN f)
    (hg : @IsMonHom _ _ _ N O mN mO g) :
    @IsMonHom _ _ _ M O mM mO (f ≫ g) := by
  let := mM
  let := mN
  let := mO
  let := hf
  let := hg
  infer_instance

private theorem canonicalAbelianMap_isMonHom (T : Scheme.{u}) :
    IsMonHom (canonicalAbelianMap A T) := by
  let J := coherentTopology Profinite.{u}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))
  let ψ := (presheafToSheaf J Ab.{u + 1}).map
    (Functor.whiskerRight (pointRingConstants A) (forget₂ RingCat Ab)) ≫
      (Sheaf.sheafifyRingPresheafIso J (Profinite.continuousCoefficientRingSheaf A)).hom
  have hψ : IsMonHom ψ := by dsimp only [ψ]; infer_instance
  have hm : (constantSheaf J Ab.{u + 1}).monObjObj
      (AddCommGrpCat.of (ULift.{u + 1} A)) =
      Sheaf.monObj_presheafToSheaf_obj J
        (P ⋙ forget₂ RingCat Ab) := by
    have h := Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
      (presheafToSheaf J Ab.{u + 1}) (AddCommGrpCat.of (ULift.{u + 1} A))
    refine h.trans ?_
    exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf J Ab.{u + 1}) _ _ m) (constantPresheafMonObj A)
  have hψ' : @IsMonHom _ _ _ _ _
      ((constantSheaf J Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of (ULift.{u + 1} A))) _ ψ :=
    IsMonHom.of_eq ψ hm.symm rfl (hf := hψ)
  have heq : ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
      (coefficient A)).symm (pointConstants A) = ψ := rfl
  unfold canonicalAbelianMap
  rw [heq]
  let := hψ'
  have hi := Functor.isMonHom_compAlgHom
    (constantSheaf J Ab.{u + 1}) (upperStarFromPoint T) (constantSchemeIso T).inv
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let mP := (upperStarFromPoint T).monObjObj
    ((constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
  let mQ := (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  have hh := monHomInvExplicit mP mQ
    ((constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} A))).symm hi
  have hmap : @IsMonHom _ _ _ _ _ mP _ ((upperStarFromPoint T).map ψ) := by
    infer_instance
  exact monHomCompExplicit mQ mP _ _ _ hh hmap

private def schemeConstants (T : Scheme.{u}) :
    (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (condensedRingObj (coefficient A) T).obj :=
  toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (canonicalAbelianMap A T).hom

private local instance schemeConstantsTargetMonObj (T : Scheme.{u}) :
    MonObj (condensedRingObj (coefficient A) T).obj :=
  (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}).monObjObj
    (condensedRingObj (coefficient A) T)

private theorem monHomMapExplicit {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (f : M ⟶ N)
    (hf : @IsMonHom _ _ _ M N mM mN f) :
    let := mM
    let := mN
    IsMonHom (F.map f) := by
  let := mM
  let := mN
  let := hf
  infer_instance

private theorem schemeConstants_isMonHom (T : Scheme.{u}) :
    IsMonHom (schemeConstants A T) := by
  let J := Scheme.ProEt.topology T
  let X := AddCommGrpCat.of (ULift.{u + 1} A)
  let P := (Functor.const T.ProEtᵒᵖ).obj X
  let mP := (Functor.const T.ProEtᵒᵖ).monObjObj X
  let mS := (presheafToSheaf J Ab.{u + 1}).monObjObj P
  have hm : (constantSheaf J Ab.{u + 1}).monObjObj X = mS :=
    Functor.monObjObj_comp _ _ X
  have hc := IsMonHom.of_eq (canonicalAbelianMap A T) hm rfl
    (hf := canonicalAbelianMap_isMonHom A T)
  have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
  have hf := monHomMapExplicit (sheafToPresheaf J Ab.{u + 1}) mS _
    (canonicalAbelianMap A T) hc
  exact monHomCompExplicit mP _ _ _ _ hu hf

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory in
private def constantSectionRingMapAux
    {C : Type*} [Category.{v} C] (J : GrothendieckTopology C)
    [UnivLE.{_, u + 1}] [HasSheafify J Ab.{u + 1}]
    [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (B : Type (u + 1)) [CommRing B]
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (φ : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B) ⟶ R.obj)
    [@IsMonHom _ _ _ _ _
      ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ] :
    (Functor.const Cᵒᵖ).obj (CommRingCat.of B) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf J R).obj where
  app U := by
    letI := CommRingCat.commRing
      ((InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U)
    refine CommRingCat.ofHom
      (R := B) (S := (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U) ?_
    refine
      { toFun := fun a ↦ φ.app U a
        map_zero' := map_zero _
        map_add' := map_add _
        map_one' := ?_
        map_mul' := ?_ }
    · have h := @IsMonHom.one_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ inferInstance
      convert! ConcreteCategory.congr_hom (congr_app h U) (ULift.up 1) using 1
      simp only [Functor.const_obj_obj, Monoidal.tensorUnit_obj, ObjectProperty.ι_obj,
        Functor.obj.η_def, Category.assoc, NatTrans.comp_app, Functor.const_map_app,
        AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change (φ.app U) (1 : B) = (φ.app U) ((η[AddCommGrpCat.of B]).hom (ULift.up 1))
      rw [AddCommGrpCat.ringMonObj_one_apply]
      simp
    · intro a b
      have h := @IsMonHom.mul_hom _ _ _ _ _
        ((Functor.const Cᵒᵖ).monObjObj (AddCommGrpCat.of B))
        ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ inferInstance
      have he := ConcreteCategory.congr_hom (congr_app h U) (a ⊗ₜ[ℤ] b)
      convert! he using 1
  naturality U V f := by
    ext a
    exact ConcreteCategory.congr_hom (φ.naturality f) a

private def constantSectionRingMap (T : Scheme.{u}) :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (sectionRing A T).obj := by
  let := schemeConstants_isMonHom A T
  exact constantSectionRingMapAux (Scheme.ProEt.topology T) (ULift.{u + 1} A)
    (condensedRingObj (coefficient A) T) (schemeConstants A T)

private def canonicalRingMap (T : Scheme.{u}) :
    realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ⟶ sectionRing A T :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ (sectionRing A T)).symm (constantSectionRingMap A T)

private theorem canonicalRingMap_normalization (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a : ULift.{u + 1} A) :
    (canonicalRingMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ (sectionRing A T)).apply_symm_apply (constantSectionRingMap A T)
  change _ = (constantSectionRingMap A T).app U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

private theorem canonicalRingMap_isIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    IsIso (canonicalRingMap A T) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let F := sheafCompose J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of B)
  let g : F.obj (realizationRing J B) ⟶ condensedRingObj (coefficient A) T :=
    F.map (canonicalRingMap A T)
  have hg : e.inv ≫ g = canonicalAbelianMap A T := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (condensedRingObj (coefficient A) T).property
    have he : toSheafify J
        ((Functor.const T.ProEtᵒᵖ).obj (V.obj (CommRingCat.of B))) ≫ e.inv.hom =
        Functor.whiskerRight
          (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of B))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of B) V).inv ≫
        (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact canonicalRingMap_normalization A T U a
  have : IsIso (canonicalAbelianMap A T) := canonicalAbelianMap_isIso A T
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (canonicalRingMap A T) F

private def scalarEquivalence (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1}} (e : S ≅ R) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S := by
  let eqv : T.ProEt ≌ T.ProEt :=
    ⟨𝟭 _, 𝟭 _, Iso.refl _, Iso.refl _, fun _ ↦ Category.id_comp _⟩
  letI : eqv.functor.IsContinuous (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  letI : eqv.inverse.IsContinuous (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) :=
    inferInstanceAs (Functor.IsContinuous (𝟭 _) _ _)
  exact SheafOfModules.pushforwardPushforwardEquivalence eqv e.hom e.inv
    (by ext V : 2
        exact (R.obj.map_id V).trans
          (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) e.inv_hom_id) V).symm)
    (by ext V : 2
        exact (congrArg (fun f ↦ e.hom.hom.app V ≫ e.inv.hom.app V ≫ f)
          (S.obj.map_id V)).trans ((Category.comp_id _).trans
            (congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) e.hom_inv_id) V)))

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
