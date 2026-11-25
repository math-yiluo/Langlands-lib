/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolution
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.AlgebraicGeometry.CompactAdicContinuousIdentification
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletion
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Field.ULift
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!
# Exact scalar realization for admissible continuous coefficients

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; blueprint main-20261015,
internal-Hom stability proof, paragraphs 2--3
(auxiliary; not a blueprint node).

The scalar realization is the existing `FiniteConstantModel.modelFunctor`. The algebraic
closure below uses all continuous functions. Universe lifts of the three standard scalar
rings carry their induced topologies and do not change their rings or sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.MonObj
open scoped TensorProduct Topology

namespace AlgebraicGeometry.ProEtale.AdmissibleScalarRealization

-- In live this instance came globally from the Sheaf copy of InternalSectionTensorComparison;
-- the tip makes it local there.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

open FiniteConstantModel

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Restrict the actual realized module sheaf to the localized site over `U`.
Source: Stacks 00Y0, localization, and 093J, constant modules
(auxiliary; not a blueprint node). -/
def localizedModel (T : Scheme.{u}) (U : T.ProEt) :=
  modelFunctor A T ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ⋙
    SheafOfModules.overFunctor _ U

/-- Noetherian scalars, additive exact realization on all scalar modules, and the same
assertion for the actual restricted coefficient sheaf on every localized site.
Source: Stacks 093J and 093M and the field split-sequence argument
(auxiliary; not a blueprint node). -/
def ScalarAssertions (T : Scheme.{u}) : Prop :=
  IsNoetherianRing A ∧ (modelFunctor A T).Additive ∧
    PreservesFiniteLimits (modelFunctor A T) ∧
    PreservesFiniteColimits (modelFunctor A T) ∧
    ∀ U : T.ProEt, (localizedModel A T U).Additive ∧
      PreservesFiniteLimits (localizedModel A T U) ∧
      PreservesFiniteColimits (localizedModel A T U)

/-- The actual completed coefficient assertion: an isomorphism of ring sheaves with the
positive constant quotient tower, and flatness over constant scalars on all sheaf modules,
also on every localized site. Here `p` is the specified uniformizer.
Source: Stacks 093M and the integral coefficient limit comparison
(auxiliary; not a blueprint node). -/
def CompletedIdentification (T : Scheme.{u}) (p : A) : Prop :=
  (∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
    Scheme.adicLisseCompletedRing T
      (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))))).app U
          (Ideal.Quotient.mk
            ((Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))
            (ULift.up a)))

private local instance constantFunctions_locallySurjective [Finite A] [DiscreteTopology A] :
    Presheaf.IsLocallySurjective (coherentTopology Profinite.{u}) (constantFunctions A) where
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

private local instance constantFunctions_locallyInjective :
    Presheaf.IsLocallyInjective (coherentTopology Profinite.{u}) (constantFunctions A) where
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

private noncomputable local instance localEquivalences (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} (Scheme.ProEt.topology T)

private noncomputable local instance sliceLocalEquivalences (T : Scheme.{u}) (U : T.ProEt) :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective Ab.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1, u + 1,
    u + 2, u + 1, u + 1, u + 1} ((Scheme.ProEt.topology T).over U)

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

private def constantPresheafRingMap (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R).obj := by
  let J := Scheme.ProEt.topology T
  let X := AddCommGrpCat.of (ULift.{u + 1} A)
  let P := (Functor.const T.ProEtᵒᵖ).obj X
  let eta := toSheafify J P
  let : MonObj P := (Functor.const T.ProEtᵒᵖ).monObjObj X
  let : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  let : MonObj ((constantSheaf J Ab.{u + 1}).obj X).obj :=
    (sheafToPresheaf J Ab.{u + 1}).monObjObj ((constantSheaf J Ab.{u + 1}).obj X)
  have hη : @IsMonHom _ _ _ _ _
      ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X)) eta := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have hm := Functor.monObjObj_comp (Functor.const T.ProEtᵒᵖ)
      (presheafToSheaf J Ab.{u + 1}) X
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl
      (congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
        (sheafToPresheaf J Ab.{u + 1}) _ _ m) hm).symm h
  let := hη
  have hpsi : @IsMonHom _ _ _ _ _
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) ψ.hom := by
    exact inferInstanceAs (IsMonHom ((sheafToPresheaf J Ab.{u + 1}).map ψ))
  let := hpsi
  let φ := eta ≫ ψ.hom
  have hphi : @IsMonHom _ _ _ _ _ ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ :=
    FiniteDiscreteOrdinary.monHomCompExplicit
      ((Functor.const T.ProEtᵒᵖ).monObjObj X)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj X))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) eta ψ.hom hη hpsi
  exact @constantSectionRingMapAux _ _ J inferInstance inferInstance inferInstance
      (ULift.{u + 1} A) inferInstance R inferInstance inferInstance φ hphi

private def constantRingMap (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] :
    Scheme.adicLisseConstantRing T (ULift.{u + 1} A) ⟶
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ _).symm (constantPresheafRingMap A T R ψ)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantRingMap_normalization (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ]
    (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (constantRingMap A T R ψ).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    ψ.hom.app U ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) R)).apply_symm_apply (constantPresheafRingMap A T R ψ)
  change _ = (constantPresheafRingMap A T R ψ).app U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constantRingMap_isIso (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ R) [IsMonHom ψ] [IsIso ψ] :
    IsIso (constantRingMap A T R ψ) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let F := sheafCompose J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of B)
  let g : F.obj (realizationRing J B) ⟶ R :=
    F.map (constantRingMap A T R ψ)
  have hg : e.inv ≫ g = ψ := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (R).property
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
    exact constantRingMap_normalization A T R ψ U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (constantRingMap A T R ψ) F

attribute [local irreducible] constantPresheafRingMap constantRingMap

end AlgebraicGeometry.ProEtale.AdmissibleScalarRealization
