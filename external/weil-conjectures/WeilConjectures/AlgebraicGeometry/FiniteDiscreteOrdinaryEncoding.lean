/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence

/-! # Finite discrete internal and ordinary coefficients

(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj TensorProduct

-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The already defined continuous condensed coefficient ring.
Source: blueprint coefficient identification
(auxiliary; not a blueprint node). -/
abbrev coefficient := Profinite.continuousCoefficientRingObj A

/-- The pulled-back internal module category, without boundedness or completion.
Source: blueprint coefficient identification
(auxiliary; not a blueprint node). -/
abbrev Internal (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (coefficient A) T)

/-- Ordinary modules over the constant commutative ring sheaf, in the scalar universe.
Source: blueprint coefficient identification
(auxiliary; not a blueprint node). -/
abbrev Ordinary (T : Scheme.{u}) :=
  realizationModules (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- The reconstructed commutative section-ring sheaf of the pulled-back coefficients.
Source: Stacks 00YV, section-action equivalence
(auxiliary; not a blueprint node). -/
abbrev sectionRing (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)

/-- Constant functions, as a map into the actual continuous condensed sheaf.
Source: blueprint proof step 1, constant-section normalization
(auxiliary; not a blueprint node). -/
def pointConstants :
    (Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (coefficient A).obj where
  app S := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const S.unop a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

/-- The canonical constant-coefficient map: sheafify constant functions on the point,
then apply the monoidal inverse image and its constant-sheaf comparison.
Source: blueprint proof step 1
(auxiliary; not a blueprint node). -/
def canonicalAbelianMap (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ condensedRingObj (coefficient A) T :=
  (constantSchemeIso T).hom.app (AddCommGrpCat.of (ULift.{u + 1} A)) ≫
    (upperStarFromPoint T).map
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ (coefficient A)).symm (pointConstants A))

/-- The intrinsic-to-fixed coefficient functor restricts to constant scalar sections.
The commutative-ring/underlying-ring constant-sheaf comparison is canonical.
Source: blueprint proof step 3, Stacks 03CY
(auxiliary; not a blueprint node). -/
def fixedRestriction (T : Scheme.{u}) :
    Ordinary A T ⥤ Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} A))) ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology T) (ULift.{u + 1} A)

/-- Restrict the section-action equivalence along the specified coefficient isomorphism.
Source: blueprint proof step 2, Stacks 00YV
(auxiliary; not a blueprint node). -/
def sectionEncoding (T : Scheme.{u})
    (c : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T) :
    Internal A T ⥤ Ordinary A T :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
    (condensedRingObj (coefficient A) T)).functor ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)

/-- The two coefficient presentations and their actual section-action functors.
The ring isomorphism is normalized by the canonical constant-function map; the
forward intrinsic functor is precisely section-action followed by scalar restriction.
The fixed scalar encoding likewise restricts along the constant-sheaf unit.
Source: blueprint proof steps 1--3, Stacks 00YV and 03CY
(auxiliary; not a blueprint node). -/
structure Encoding (T : Scheme.{u}) where
  ringIso : realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T
  normalization : ∀ (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A),
    ringIso.hom.hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a)
  ordinary : Internal A T ≌ Ordinary A T
  ordinary_functor : ordinary.functor = sectionEncoding A T ringIso
  fixed : Ordinary A T ≌
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))
  fixed_functor : fixed.functor = fixedRestriction A T
  [ordinaryAdditive : ordinary.functor.Additive]
  [ordinaryInverseAdditive : ordinary.inverse.Additive]
  [fixedAdditive : fixed.functor.Additive]
  [fixedInverseAdditive : fixed.inverse.Additive]

attribute [instance] Encoding.ordinaryAdditive Encoding.ordinaryInverseAdditive
  Encoding.fixedAdditive Encoding.fixedInverseAdditive

/-- Termwise extension of the specified intrinsic equivalence to unbounded derived categories.
Source: blueprint proof step 4, Stacks 015F
(auxiliary; not a blueprint node). -/
def Encoding.ordinaryDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌ Scheme.proEtaleDerivedCategory T A :=
  letI := HasDerivedCategory.standard (Ordinary A T)
  e.ordinary.mapDerivedCategory

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

private def constantSectionRingMapAux
    {C : Type*} [Category C] (J : GrothendieckTopology C)
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

/-- The normalized finite-discrete coefficient encoding exists.
Source: blueprint coefficient identification, proof steps 1--3; Stacks Tags 00YV and 03CY.
(auxiliary; not a blueprint node).

Proof: the finite clopen fibres of each continuous function give local surjectivity of
constant functions. Equality of constants is local, using the empty cover at the empty
space. Sheafification and inverse image give an isomorphism of abelian sheaves; their
monoidal structures make it a ring map. The sheafification adjunction extends this map
to the section-ring sheaf, with the required normalization. Forgetting to abelian groups
reflects its invertibility. Transport the section-action equivalence along this ring
isomorphism. Finally compose the constant-ring comparison with the equivalence between
constant-ring module sheaves and fixed scalar sheaves. All maps retain the original
additive maps, so the equivalences and their inverses are additive. -/
theorem encoding_exists [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    Nonempty (Encoding A T) := by
  let := canonicalRingMap_isIso A T
  let c := asIso (canonicalRingMap A T)
  let eo := (InternalAbelianSheafModule.sectionModuleEquivalence
      (Scheme.ProEt.topology T) (condensedRingObj (coefficient A) T)).trans
    (scalarEquivalence T ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c))
  have ho : eo.functor = sectionEncoding A T c := by
    rfl
  let : eo.functor.Additive := by
    rw [ho]
    unfold sectionEncoding
    infer_instance
  obtain ⟨ec, hc, ha, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology T) (ULift.{u + 1} A)).1
  let : ec.functor.Additive := ha
  let ef := (scalarEquivalence T ((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).symm.app
        (CommRingCat.of (ULift.{u + 1} A)))).trans ec
  have hf : ef.functor = fixedRestriction A T := by
    change SheafOfModules.restrictScalars _ ⋙ ec.functor = _
    rw [hc]
    rfl
  let : ef.functor.Additive := by
    change (SheafOfModules.restrictScalars _ ⋙ ec.functor).Additive
    infer_instance
  exact ⟨{ ringIso := c
           normalization := canonicalRingMap_normalization A T
           ordinary := eo
           ordinary_functor := ho
           fixed := ef
           fixed_functor := hf }⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj TensorProduct
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify


/-- Termwise extension to fixed scalar sheaves, using the same intrinsic equivalence.
Source: blueprint proof steps 3--4, Stacks 015F
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def Encoding.fixedDerived {T : Scheme.{u}} (e : Encoding A T) :
    DerivedCategory (Internal A T) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) :=
  letI : (e.ordinary.trans e.fixed).functor.Additive :=
    inferInstanceAs (e.ordinary.functor ⋙ e.fixed.functor).Additive
  letI : (e.ordinary.trans e.fixed).inverse.Additive :=
    inferInstanceAs (e.fixed.inverse ⋙ e.ordinary.inverse).Additive
  (e.ordinary.trans e.fixed).mapDerivedCategory

/-- The ordinary finite constant local models: on each member of one pro-etale cover
there is a constant finite module. Over a finite ring, finite modules are precisely
finitely presented modules. This is the ordinary side of the source's local-model clause.
Source: blueprint proof step 9 and definition-constructible-sheaves, clause 1
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryLocalModel (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : C.I₀,
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f i)).obj M ≅
        (constantSheaf (Scheme.ProEt.topology (C.X i))
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P)

/-- The ordinary finite stratification condition in the same scalar presentation.
Source: definition-constructible-sheaves, clause 2, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryStratified (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  ∃ S : Scheme.Stratification T, ∀ a : Fin S.n,
    ordinaryLocalModel A (S.domain a)
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion a)).obj M)

open Classical in
/-- Qcqs schemes use finite constructible stratifications; otherwise use every affine open.
Source: definition-constructible-sheaves, clause 2, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryConstructible (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) : Prop :=
  if CompactSpace T ∧ QuasiSeparatedSpace T then ordinaryStratified A T M
  else ∀ U : T.Opens, IsAffineOpen U → ordinaryStratified A U.toScheme
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι).obj M)

/-- The ordinary bounded constructible predicate in the fixed scalar presentation.
Source: definition-constructible-sheaves, final paragraph, and blueprint proof step 9
(blueprint: lem-sf-finite-discrete-normalized-encoding). -/
def ordinaryBoundedConstructible (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    ordinaryConstructible A T ((DerivedCategory.homologyFunctor _ n).obj K)

end

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
