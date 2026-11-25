/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import WeilConjectures.AlgebraicGeometry.KoszulDifferential
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Intrinsic Koszul completion over the completed coefficient sheaf

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-intrinsic-completion; Stacks Tag 099M
(blueprint: def-weil-pbc-intrinsic-completion).

Koszul complexes are obtained by scalar extension of the recorded exterior-algebra
construction along the residue-normalized map from the constant ring to A_T. All tensor
products, products and mapping fibres below are in modules over A_T.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

variable {A : Type t} [CommRing A]

attribute [local instance] koszulConstantFunctor_preservesZero

/-- The scalar map to the completed ring is uniquely fixed by all its residue sections.
Source: blueprint, def-weil-pbc-intrinsic-completion, the action of the generators
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: for each positive quotient use the residue homomorphism followed by the constant
sections of its continuous-functions presheaf and sheafification. These maps commute with
quotient transitions. The limit property gives a unique map of ring sheaves, and it is
commutative because both rings are commutative. Maps out of a constant sheaf are fixed by
their constant presheaf sections, so the displayed equation characterizes it uniquely. -/
theorem completedAdicScalar_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    ∃! α : adicConstantRing T A ⟶ completedAdicCommRing T d,
      ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A),
        (completedAdicProjection T d n).hom.app U
          (((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
            ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (ULift.up (Ideal.Quotient.mk (d.ideal ^ (n + 1)) a.down)) := by
  let J := ProEt.topology T
  let F := (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} A))
  let D := completedAdicRingSystem T d
  let E := sheafToPresheaf J RingCat.{t + 1}
  let q (n : ℕ) : ULift.{t + 1} A →+* completedAdicQuotient d n :=
    RingHom.ulift (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
  let σ (n : ℕ) : F ⟶ (completedAdicFiniteRing T d n).obj :=
    (Functor.const T.ProEtᵒᵖ).map (RingCat.ofHom (q n)) ≫
      ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)
  have hσ (n : ℕ) : σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom = σ n := by
    ext U a
    have hs := congrArg
      (fun k ↦ (k.app U).hom
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)))
      (toSheafify_naturality J (completedAdicFinitePresheafStep T d n))
    have hc : (completedAdicFinitePresheafStep T d n).app U
        ((ProEtale.finiteCoefficientConstants T
          (completedAdicQuotient d (n + 1))).app U (q (n + 1) a)) =
      (ProEtale.finiteCoefficientConstants T
        (completedAdicQuotient d n)).app U (q n a) := by
      apply ContinuousMap.ext
      intro x
      rfl
    simp only [NatTrans.comp_app, RingCat.comp_apply] at hs
    rw [hc] at hs
    exact hs.symm
  let c : Cone (D ⋙ E) :=
    { pt := F
      π := NatTrans.ofOpSequence σ (fun n ↦ by
        dsimp only [Functor.const_obj_map, Functor.comp_map, D, E,
          completedAdicRingSystem]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        change 𝟙 F ≫ σ n = σ (n + 1) ≫ (completedAdicFiniteStep T d n).hom
        simpa only [Category.id_comp] using (hσ n).symm) }
  let L := isLimitOfPreserves E (limit.isLimit D)
  let β : F ⟶ (completedAdicRing T d).obj := L.lift c
  let F' := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} A))
  let β' : F' ⟶ (completedAdicCommRing T d).obj :=
    { app := fun U ↦
        letI := completedAdicCommRingStructure T d U
        CommRingCat.ofHom (β.app U).hom
      naturality := fun U V f ↦ (forget₂ CommRingCat RingCat).map_injective
        (β.naturality f) }
  let α : adicConstantRing T A ⟶ completedAdicCommRing T d :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).symm β'
  have hα : toSheafify J F' ≫ α.hom = β' :=
    ((sheafificationAdjunction J CommRingCat.{t + 1}).homEquiv F'
      (completedAdicCommRing T d)).apply_symm_apply β'
  have hnorm (n : ℕ) (U : T.ProEtᵒᵖ) (a : ULift.{t + 1} A) :
      (completedAdicProjection T d n).hom.app U
        (((sheafCompose J (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map α).hom.app U
          ((koszulConstantUnit T A).app U a)) =
        (ProEtale.finiteCoefficientScalarMap T (completedAdicQuotient d n)).app U
          (q n a) := by
    have ha := congrArg (fun k : F' ⟶ (completedAdicCommRing T d).obj ↦
      (k.app U).hom a) hα
    change (α.hom.app U).hom ((toSheafify J F').app U a) = (β.app U).hom a at ha
    change (completedAdicProjection T d n).hom.app U
      ((α.hom.app U).hom ((toSheafify J F').app U a)) = _
    rw [ha]
    exact congrArg (fun k : F ⟶ (completedAdicFiniteRing T d n).obj ↦
      (k.app U).hom a) (L.fac c (op n))
  refine ⟨α, hnorm, ?_⟩
  intro ψ hψ
  have htest : toSheafify J F' ≫ ψ.hom = β' := by
    apply ((Functor.whiskeringRight T.ProEtᵒᵖ CommRingCat RingCat).obj
      (forget₂ CommRingCat RingCat)).map_injective
    change Functor.whiskerRight (toSheafify J F' ≫ ψ.hom)
      (forget₂ CommRingCat RingCat) = β
    apply L.hom_ext
    intro j
    rw [L.fac c j]
    ext U a
    exact hψ j.unop U a
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (completedAdicCommRing T d).property
  exact htest.trans hα.symm

/-- The actual scalar map, with its unique residue normalization.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalar (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    adicConstantRing T A ⟶ completedAdicCommRing T d :=
  (completedAdicScalar_exists T d).exists.choose

set_option linter.defProp false in
/-- The scalar-extension witness with its object and morphism tensor formulas.
Source: blueprint def-weil-pbc-intrinsic-completion; Stacks Tag 06YY
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarExtensionData (T : Scheme.{t}) (d : AdicCoefficientDatum A) :=
  completedAdicChangeData T (completedAdicScalar T d)

/-- Ordinary scalar extension of constant A-module sheaves to A_T-module sheaves.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarExtension (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    SheafOfModules.{t + 1} (adicModuleRing T A) ⥤ CompletedAdicModules T d :=
  completedAdicChange T (completedAdicScalar T d)

/-- Scalar extension is additive, from the normalized change-of-rings witness.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
instance completedAdicScalarExtension_additive (T : Scheme.{t}) (d : AdicCoefficientDatum A) :
    (completedAdicScalarExtension T d).Additive :=
  (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose_spec.choose

/-- The sheafified tensor generator in scalar extension. The equality transport is the
object formula of the scalar-extension witness, not a freely chosen identification.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicScalarTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (M : SheafOfModules.{t + 1} (adicModuleRing T A)) (U : T.ProEtᵒᵖ)
    (s : (completedAdicCommRing T d).obj.obj U) (x : M.val.obj U) :
    ((completedAdicScalarExtension T d).obj M).val.obj U :=
  (eqToHom ((completedAdicScalarExtensionData T d).choose_spec.choose M).symm).val.app U
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (completedAdicScalar T d) M).presheaf).app U
        (s ⊗ₜ[(adicConstantRing T A).obj.obj U,
          ((completedAdicScalar T d).hom.app U).hom] x))

private theorem normalizedScalarTensor_map
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.map f).val.app U ((eqToHom (h M).symm).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) =
      (eqToHom (h N).symm).val.app U
        ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] (f.val.app U x))) := by
  have he : eqToHom (h M).symm ≫ E.map f =
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (h N).symm := by
    rw [hm]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have he' := congrArg (fun k ↦ k.val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))) he
  refine he'.trans (congrArg (fun z ↦ (eqToHom (h N).symm).val.app U z) ?_)
  let g : SheafOfModules.changeOfRingsPresheaf φ M ⟶
      SheafOfModules.changeOfRingsPresheaf φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M f }
  have hn := congrArg (fun k ↦ k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map g))
  change (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (((ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U))
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
    (SheafOfModules.changeOfRingsHom φ M f).val.app U
      ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) at hn
  erw [ModuleCat.ExtendScalars.map_tmul] at hn
  exact hn.symm

attribute [local irreducible] completedAdicRing in
private theorem adicScalarTensor_map (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    {M N : SheafOfModules.{t + 1} (adicModuleRing T A)} (f : M ⟶ N)
    (U : T.ProEtᵒᵖ) (s : (completedAdicCommRing T d).obj.obj U) (x : M.val.obj U) :
    ((completedAdicScalarExtension T d).map f).val.app U
      (completedAdicScalarTensor T d M U s x) =
        completedAdicScalarTensor T d N U s (f.val.app U x) := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  exact normalizedScalarTensor_map (completedAdicScalar T d) (completedAdicScalarExtension T d)
    (completedAdicScalarExtensionData T d).choose_spec.choose
    (fun g ↦ (completedAdicScalarExtensionData T d).choose_spec.choose_spec.choose g) f U s x

/-- The Koszul complex of a_1^(m+1),...,a_r^(m+1) over A_T, in degrees [-r,0].
It is the recorded constant exterior complex followed by actual extension of scalars.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszul (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) : CochainComplex (CompletedAdicModules T d) ℤ :=
  ((completedAdicScalarExtension T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (koszulPowerSheaf T A r a m)

/-- The inverse Koszul transition: multiplication by a_j in degree -1 of each factor,
identity in degree zero. Extension of scalars preserves the recorded exterior map.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    completedAdicKoszul T d r a (m + 1) ⟶ completedAdicKoszul T d r a m :=
  letI := koszulConstantFunctor_preservesZero T A
  ((completedAdicScalarExtension T d).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((koszulConstantFunctor T A).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (koszulPowerTransition A r a m))

attribute [local irreducible] completedAdicRing in
/-- The degree-zero unit is determined by the tensor of the two scalar units.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the displayed section is compatible with restrictions since both its factors are.
The unit-module/global-section equivalence gives the unique module map with that value on
one. In degree zero the constant Koszul unit identifies the rank-one module with degree
zero, and extension of scalars preserves this identification. -/
theorem completedAdicKoszulUnitZero_exists (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    ∃! u : SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0,
      ∀ U : T.ProEtᵒᵖ, u.val.app U (1 : (completedAdicRing T d).obj.obj U) =
        completedAdicScalarTensor T d _ U 1
          ((koszulSheafUnitZero T A r a m).val.app U
            (1 : (adicModuleRing T A).obj.obj U)) := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  let M := (koszulPowerSheaf T A r a m).X 0
  let u := koszulSheafUnitZero T A r a m
  let P := SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
    (completedAdicScalar T d) M
  let N := SheafOfModules.changeOfRings.{t, t + 1, t + 1}
    (completedAdicScalar T d) M
  let η := toSheafify (ProEt.topology T) P.presheaf
  let s₀ : N.sections := PresheafOfModules.sectionsMk
    (fun U ↦ η.app U ((1 : (completedAdicCommRing T d).obj.obj U) ⊗ₜ[
      (adicConstantRing T A).obj.obj U, ((completedAdicScalar T d).hom.app U).hom]
        (u.val.app U (1 : (adicModuleRing T A).obj.obj U)))) (by
    intro U V g
    erw [← NatTrans.naturality_apply η g]
    change η.app V (SheafOfModules.changeOfRingsMap (completedAdicScalar T d) M g
      ((1 : (completedAdicCommRing T d).obj.obj U) ⊗ₜ[(adicConstantRing T A).obj.obj U,
        ((completedAdicScalar T d).hom.app U).hom]
          (u.val.app U (1 : (adicModuleRing T A).obj.obj U)))) = _
    erw [Classical.choose_spec
      (SheafOfModules.exists_changeOfRingsMap (completedAdicScalar T d) M g)]
    erw [← PresheafOfModules.naturality_apply u.val]
    simp only [map_one]
    have h1 : (SheafOfModules.unit (adicModuleRing T A)).val.map g
        (1 : (adicModuleRing T A).obj.obj U) =
          (1 : (adicModuleRing T A).obj.obj V) :=
      ((adicModuleRing T A).obj.map g).hom.map_one
    erw [h1])
  let e : N ⟶ (completedAdicKoszul T d r a m).X 0 :=
    eqToHom ((completedAdicScalarExtensionData T d).choose_spec.choose M).symm
  let s := SheafOfModules.sectionsMap e s₀
  refine ⟨((completedAdicKoszul T d r a m).X 0).unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z ↦ z.val U)
      (((completedAdicKoszul T d r a m).X 0).unitHomEquiv.apply_symm_apply s)
  · intro v hv
    apply ((completedAdicKoszul T d r a m).X 0).unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hv U).trans (congrArg (fun z ↦ z.val U)
      (((completedAdicKoszul T d r a m).X 0).unitHomEquiv.apply_symm_apply s)).symm

/-- The specified degree-zero inclusion A_T[0] to its Koszul complex.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulUnitZero (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (m : ℕ) :
    SheafOfModules.unit (completedAdicRing T d) ⟶ (completedAdicKoszul T d r a m).X 0 :=
  (completedAdicKoszulUnitZero_exists T d r a m).exists.choose

/-- The total tensor C tensor Q_(m+1) over the completed ring.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensor (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  CochainComplex.mapBifunctor C (completedAdicKoszul T d r a m) (curriedTensor _)

/-- The tensor transition 1_C tensor q_(m+2,m+1).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorStep (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    completedAdicKoszulTensor T d r a C (m + 1) ⟶ completedAdicKoszulTensor T d r a C m :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  HomologicalComplex.mapBifunctorMap (𝟙 C) (completedAdicKoszulStep T d r a m)
    (curriedTensor _) (ComplexShape.up ℤ)

/-- In degree p the unit sends c to c tensor 1 in the (p,0) total summand.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorUnitF (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (completedAdicKoszulTensor T d r a C m).X p :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫
    HomologicalComplex.ιMapBifunctor C (completedAdicKoszul T d r a m) (curriedTensor _)
      (ComplexShape.up ℤ) p 0 p (add_zero p)

private theorem adicTensorClosedUnit_comm
    {A : Type*} [Category* A] [Preadditive A] [MonoidalCategory A]
    [(curriedTensor A).PreservesZeroMorphisms]
    [∀ Z, ((curriedTensor A).obj Z).PreservesZeroMorphisms]
    (C D : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor C D (curriedTensor A) (ComplexShape.up ℤ)]
    (u : 𝟙_ A ⟶ D.X 0) (hu : u ≫ D.d 0 1 = 0)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    ((ρ_ (C.X p)).inv ≫ (C.X p ◁ u) ≫
      HomologicalComplex.ιMapBifunctor C D (curriedTensor A)
        (ComplexShape.up ℤ) p 0 p (add_zero p)) ≫
      (HomologicalComplex.mapBifunctor C D (curriedTensor A) (ComplexShape.up ℤ)).d p q =
    C.d p q ≫ (ρ_ (C.X q)).inv ≫ (C.X q ◁ u) ≫
      HomologicalComplex.ιMapBifunctor C D (curriedTensor A)
        (ComplexShape.up ℤ) q 0 q (add_zero q) := by
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hpq 0 q (add_zero q),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p
      (show (ComplexShape.up ℤ).Rel 0 1 by rfl) q]
  dsimp only [curriedTensor_map_app, curriedTensor_obj_map]
  have hs : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, 0) = 1 := rfl
  rw [hs, one_smul]
  have hzero : C.X p ◁ (0 : 𝟙_ A ⟶ D.X 1) = 0 :=
    Functor.map_zero ((curriedTensor A).obj (C.X p)) _ _
  rw [Linear.comp_units_smul, ← whiskerLeft_comp_assoc, hu,
    hzero, zero_comp, smul_zero, comp_zero, add_zero]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

/-- The tensor units are chain maps.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion).
Proof: the differential of the Koszul degree-zero unit is zero, since the complex has no
positive degrees. The total differential on c tensor 1 is therefore dc tensor 1; naturality
of the right unit isomorphism gives the displayed chain-map identity. -/
theorem completedAdicKoszulTensorUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (m : ℕ) (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    completedAdicKoszulTensorUnitF T d r a C m p ≫
        (completedAdicKoszulTensor T d r a C m).d p q =
      C.d p q ≫ completedAdicKoszulTensorUnitF T d r a C m q := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  let : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  let : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  apply adicTensorClosedUnit_comm C (completedAdicKoszul T d r a m)
    (completedAdicKoszulUnitZero T d r a m) _ p q _hpq
  have hd : (koszulPower A r a m).d 0 1 = 0 :=
    HomologicalComplex.extend_d_from_eq_zero _ ComplexShape.embeddingDownNat
      0 1 0 rfl (by simp [ComplexShape.down_Rel])
  let := koszulConstantFunctor_preservesZero T A
  change _ ≫ (completedAdicScalarExtension T d).map
    ((koszulConstantFunctor T A).map ((koszulPower A r a m).d 0 1)) = 0
  rw [hd, Functor.map_zero, Functor.map_zero, comp_zero]

/-- The actual chain map c ↦ c tensor 1 to each Koszul tensor complex.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulTensorUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    C ⟶ completedAdicKoszulTensor T d r a C m where
  f := completedAdicKoszulTensorUnitF T d r a C m
  comm' := completedAdicKoszulTensorUnitF_comm T d r a C m

/-- The termwise product B(C) of the positive-power Koszul tensor complexes.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulProduct (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :=
  ∏ᶜ (completedAdicKoszulTensor T d r a C)

/-- The chain map 1-s with coordinates z_m - t_m(z_(m+1)).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulOneSubShift (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    completedAdicKoszulProduct T d r a C ⟶ completedAdicKoszulProduct T d r a C :=
  𝟙 _ - Pi.lift (fun m ↦ Pi.π (completedAdicKoszulTensor T d r a C) (m + 1) ≫
    completedAdicKoszulTensorStep T d r a C m)

/-- The mapping fibre with degree i terms B^i and B^(i-1). Taking the cone of -(1-s)
and shifting by -1 gives exactly the differential (dx,(1-s)x-dy), under the canonical
index isomorphisms of the shift. Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulFibre (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    CochainComplex (CompletedAdicModules T d) ℤ :=
  (CochainComplex.mappingCone (-completedAdicKoszulOneSubShift T d r a C))⟦(-1 : ℤ)⟧

/-- The compatible tensor units form the map u_C to B(C).
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulProductUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulProduct T d r a C :=
  Pi.lift (completedAdicKoszulTensorUnit T d r a C)

private theorem adicKoszulPowerUnit_transition (A : Type t) [CommRing A]
    (r : ℕ) (f : Fin r → A) (m : ℕ) :
    ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
        (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun k ↦ ULift.up (f k ^ (m + 1 + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv ≫
      (koszulPowerTransition A r f m).f 0 =
    ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
        (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} A) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
  have hz : ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
        (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap ≫
      ModuleCat.ofHom (exteriorPower.map 0 (koszulPowerGenerator A r f)) =
      ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} A)
        (Fin r →₀ ULift.{t + 1} A)).symm.toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (exteriorPower.zeroEquiv (ULift.{t + 1} A)
      (Fin r →₀ ULift.{t + 1} A)).injective
    exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
      (koszulPowerGenerator A r f)) _
  dsimp only [koszulPowerTransition]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
    (i := 0) (i' := 0) rfl, Iso.inv_hom_id_assoc, ← Category.assoc, hz]

private theorem adicKoszulSheafUnitZero_transition (T : Scheme.{t})
    (r : ℕ) (f : Fin r → A) (m : ℕ) :
    koszulSheafUnitZero T A r f (m + 1) ≫
      (((koszulConstantFunctor T A).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (koszulPowerTransition A r f m)).f 0 = koszulSheafUnitZero T A r f m := by
  dsimp only [koszulSheafUnitZero]
  change (koszulConstantOne T A ≫ _ ≫ _) ≫
    (koszulConstantFunctor T A).map ((koszulPowerTransition A r f m).f 0) = _
  simp only [Category.assoc, ← Functor.map_comp, adicKoszulPowerUnit_transition A]

private theorem adicKoszulUnitZero_transition (T : Scheme.{t})
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A) (m : ℕ) :
    completedAdicKoszulUnitZero T d r a (m + 1) ≫
      (completedAdicKoszulStep T d r a m).f 0 = completedAdicKoszulUnitZero T d r a m := by
  apply ((completedAdicKoszul T d r a m).X 0).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  change ((completedAdicScalarExtension T d).map
    ((((koszulConstantFunctor T A).mapHomologicalComplex (.up ℤ)).map
      (koszulPowerTransition A r a m)).f 0)).val.app U
        ((completedAdicKoszulUnitZero T d r a (m + 1)).val.app U
          (1 : (completedAdicRing T d).obj.obj U)) =
      (completedAdicKoszulUnitZero T d r a m).val.app U
        (1 : (completedAdicRing T d).obj.obj U)
  have hu (n : ℕ) := (completedAdicKoszulUnitZero_exists T d r a n).exists.choose_spec U
  let τ := (((koszulConstantFunctor T A).mapHomologicalComplex (.up ℤ)).map
    (koszulPowerTransition A r a m)).f 0
  calc
    _ = ((completedAdicScalarExtension T d).map τ).val.app U
        (completedAdicScalarTensor T d _ U 1
          ((koszulSheafUnitZero T A r a (m + 1)).val.app U
            (1 : (adicModuleRing T A).obj.obj U))) :=
      congrArg (fun z ↦ ((completedAdicScalarExtension T d).map τ).val.app U z) (hu (m + 1))
    _ = completedAdicScalarTensor T d _ U 1
        (τ.val.app U ((koszulSheafUnitZero T A r a (m + 1)).val.app U
          (1 : (adicModuleRing T A).obj.obj U))) := adicScalarTensor_map T d τ U 1 _
    _ = completedAdicScalarTensor T d _ U 1
        ((koszulSheafUnitZero T A r a m).val.app U
          (1 : (adicModuleRing T A).obj.obj U)) :=
      congrArg (fun z ↦ completedAdicScalarTensor T d _ U 1 z)
        (congrArg (fun k ↦ k.val.app U (1 : (adicModuleRing T A).obj.obj U))
          (adicKoszulSheafUnitZero_transition T r a m))
    _ = _ := (hu m).symm

private theorem adicKoszulTensorUnit_transition (T : Scheme.{t})
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) (m : ℕ) :
    completedAdicKoszulTensorUnit T d r a C (m + 1) ≫
      completedAdicKoszulTensorStep T d r a C m = completedAdicKoszulTensorUnit T d r a C m := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  let := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  apply HomologicalComplex.hom_ext
  intro p
  dsimp only [HomologicalComplex.comp_f, completedAdicKoszulTensorUnit,
    completedAdicKoszulTensorStep, completedAdicKoszulTensorUnitF, completedAdicKoszulTensor]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    id_whiskerRight]
  erw [Category.id_comp]
  rw [← whiskerLeft_comp_assoc, adicKoszulUnitZero_transition]

private theorem adicKoszulProductUnit_oneSubShift (T : Scheme.{t})
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    completedAdicKoszulProductUnit T d r a C ≫
      completedAdicKoszulOneSubShift T d r a C = 0 := by
  dsimp only [completedAdicKoszulOneSubShift, completedAdicKoszulProduct,
    completedAdicKoszulProductUnit]
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, adicKoszulTensorUnit_transition]

private theorem adicShiftedConeUnit_comm {A : Type*} [Category* A] [Preadditive A]
    (C P : CochainComplex A ℤ) (a : C ⟶ P) (φ : P ⟶ P)
    [HomologicalComplex.HasHomotopyCofiber φ] (hz : a ≫ φ = 0)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    (a.f p ≫ HomologicalComplex.homotopyCofiber.inlX φ
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        ((CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧).d p q =
    C.d p q ≫ a.f q ≫ HomologicalComplex.homotopyCofiber.inlX φ
      q (q + (-1)) (by change q + (-1) + 1 = q; omega) := by
  have hp : p = q + (-1) := by
    change p + 1 = q at hpq
    omega
  subst p
  change (a.f (q + (-1)) ≫ _) ≫ ((-1 : ℤ).negOnePow •
    HomologicalComplex.homotopyCofiber.d φ (q + (-1) + (-1)) (q + (-1))) = _
  rw [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    Preadditive.comp_neg, Category.assoc,
    HomologicalComplex.homotopyCofiber.inlX_d φ (q + (-1) + (-1)) (q + (-1)) q
      (by change q + (-1) + (-1) + 1 = q + (-1); omega)
      (by change q + (-1) + 1 = q; omega)]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, neg_add_rev, neg_neg]
  have hz' := congrArg (fun u ↦ u.f (q + (-1))) hz
  change a.f (q + (-1)) ≫ φ.f (q + (-1)) = 0 at hz'
  rw [← Category.assoc, hz', zero_comp, neg_zero, zero_add]
  rw [← a.comm_assoc (q + (-1)) q]

/-- The completion unit c ↦ (u_C(c),0) commutes with the fibre differential.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: lem-weil-pbc-completed-adic-koszul-unit-chain-map).
Proof: the transition on each degree-zero Koszul unit is identity, so (1-s)u_C=0.
The first coordinate of the fibre differential is d_B u_C=u_C d_C and the second
coordinate is zero. Thus inclusion in the first summand is a chain map. -/
theorem completedAdicKoszulUnitF_comm (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ)
    (p q : ℤ) (_hpq : (ComplexShape.up ℤ).Rel p q) :
    ((completedAdicKoszulProductUnit T d r a C).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
        p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        (completedAdicKoszulFibre T d r a C).d p q =
      C.d p q ≫ (completedAdicKoszulProductUnit T d r a C).f q ≫
        HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
          q (q + (-1)) (by change q + (-1) + 1 = q; omega) := by
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T
  apply adicShiftedConeUnit_comm C (completedAdicKoszulProduct T d r a C)
    (completedAdicKoszulProductUnit T d r a C)
    (-completedAdicKoszulOneSubShift T d r a C) _ p q _hpq
  rw [Preadditive.comp_neg, adicKoszulProductUnit_oneSubShift, neg_zero]

/-- The specified chain-level completion unit into the explicit mapping fibre.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicKoszulUnitComplex (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    C ⟶ completedAdicKoszulFibre T d r a C where
  f p := (completedAdicKoszulProductUnit T d r a C).f p ≫
    HomologicalComplex.homotopyCofiber.inlX (-completedAdicKoszulOneSubShift T d r a C)
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)
  comm' := completedAdicKoszulUnitF_comm T d r a C

/-- The Koszul completion of a derived object, using the localization's representative.
No K-flatness or boundedness restriction on that representative is needed: the finite free
Koszul factors preserve quasi-isomorphisms, and exact products compute derived products.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicIntrinsicCompletion (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    DerivedCategory (CompletedAdicModules T d) :=
  DerivedCategory.Q.obj
    (completedAdicKoszulFibre T d r a (DerivedCategory.Q.objPreimage K))

/-- The image of c ↦ (u_C(c),0), transported along the localization representative iso.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def completedAdicIntrinsicUnit (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (K : DerivedCategory (CompletedAdicModules T d)) :
    K ⟶ completedAdicIntrinsicCompletion T d r a K :=
  (DerivedCategory.Q.objObjPreimageIso K).inv ≫
    DerivedCategory.Q.map
      (completedAdicKoszulUnitComplex T d r a (DerivedCategory.Q.objPreimage K))

/-- Derived I-completeness is invertibility of the specified Koszul completion map.
The generator equation is supplied when this predicate is used for the ideal of d.
Source: blueprint def-weil-pbc-intrinsic-completion
(blueprint: def-weil-pbc-intrinsic-completion). -/
def IsCompletedAdicDerivedComplete (T : Scheme.{t}) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (_ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (CompletedAdicModules T d)) : Prop :=
  IsIso (completedAdicIntrinsicUnit T d r a K)

end AlgebraicGeometry.Scheme
