/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientLiftKFlatResolution
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Derived scalar extension of the constant realization of an algebraic complex

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, and 0D6D;
sites-modules.tex, Tag 093J.
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local instance] ULift.algebra'
attribute [local irreducible] ConstantScalarRealization.moduleDerivedExtension
  ConstantScalarRealization.derivedExtension Functor.leftAdjoint

private abbrev coefficientLift (B : Type t) [CommRing B] :
    ModuleCat.{t} B ⥤ ModuleCat.{t + 1} (ULift.{t + 1} B) :=
  ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom

private def liftedTensorIso {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) (M : ModuleCat.{t} A) :
    (coefficientLift B).obj ((ModuleCat.extendScalars q).obj M) ≅
      (ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q)).obj
        ((coefficientLift A).obj M) := by
  letI := q.toAlgebra
  exact (show ULift.{t + 1} (B ⊗[A] M) ≃ₗ[ULift.{t + 1} B]
      (ULift.{t + 1} B ⊗[ULift.{t + 1} A] ULift.{t + 1} M) from
    { (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).toAddEquiv with
      map_smul' := fun b x ↦
        (TensorProduct.AlgebraTensorModule.uliftEquiv A B B M).map_smul b.down x
    }).toModuleIso

private def liftedTensorComparison {A B : Type t} [CommRing A] [CommRing B]
    (q : A →+* B) :
    ModuleCat.extendScalars q ⋙ coefficientLift B ≅
      coefficientLift A ⋙ ModuleCat.extendScalars (RingHom.ulift.{t + 1, t + 1} q) := by
  letI := q.toAlgebra
  refine NatIso.ofComponents (liftedTensorIso q) ?_
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy =>
    have h : (ULift.up (x + y) : ULift.{t + 1} _) = ULift.up x + ULift.up y := rfl
    simpa only [h, map_add] using congrArg₂ (· + ·) hx hy

private def scalarTransportIso {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D) :
    ModuleCat.extendScalars (ρ.toRingHom.comp q) ≅
      ModuleCat.extendScalars q ⋙ ModuleCat.restrictScalars.{t} ρ.symm.toRingHom := by
  let adj := (ModuleCat.extendRestrictScalarsAdj q).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t} ρ.symm).toAdjunction
  exact ((adj.ofNatIsoRight (ModuleCat.restrictScalarsComp q ρ.toRingHom).symm).leftAdjointUniq
    (ModuleCat.extendRestrictScalarsAdj (ρ.toRingHom.comp q))).symm

private theorem liftedDerivedScalarRepresentative
    {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D) (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((ConstantScalarRealization.moduleDerivedExtension
        (RingHom.ulift.{t + 1, t + 1} (ρ.toRingHom.comp q))).obj
          (DerivedCategory.Q.obj (((coefficientLift B).mapHomologicalComplex (.up ℤ)).obj P)) ≅
        DerivedCategory.Q.obj (((coefficientLift D).mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp
  obtain ⟨R, f, hf, hR, hRup⟩ := P.exists_coefficientLift_kFlat_resolution
  let := hf
  let LB := coefficientLift B
  let LD := coefficientLift D
  let T := ModuleCat.restrictScalars.{t} ρ.symm.toRingHom
  let q' := RingHom.ulift.{t + 1, t + 1} (ρ.toRingHom.comp q)
  let R' := ((LB.mapHomologicalComplex (.up ℤ)).obj R)
  let Rq := (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj R)
  have hRcat : (HomologicalComplex.quasiIso (ModuleCat.{t} B) (.up ℤ)).kFlat R := hR
  have hε : IsIso (ε.app ((HomotopyCategory.quotient _ _).obj R)) :=
    ModuleCat.scalarExtensionCounit_isIso_of_kFlat q R
      (ConstantScalarRealization.acyclic_tensor_of_categorical_kFlat R hRcat) L ε hL
  let r : L.obj (DerivedCategory.Q.obj R) ≅ DerivedCategory.Q.obj Rq :=
    L.mapIso ((DerivedCategory.quotientCompQhIso _).symm.app R) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ _).obj R)) ≪≫
      DerivedCategory.Qh.mapIso
        (((ModuleCat.extendScalars q).mapHomotopyCategoryFactors (.up ℤ)).app R) ≪≫
      (DerivedCategory.quotientCompQhIso _).app Rq
  have : IsIso (ConstantScalarRealization.moduleRepresentative q' R') :=
    ConstantScalarRealization.moduleRepresentative_isIso q' R' hRup
  let a : DerivedCategory.Q.obj R ≅ DerivedCategory.Q.obj P :=
    asIso (DerivedCategory.Q.map f)
  let a' : DerivedCategory.Q.obj R' ≅
      DerivedCategory.Q.obj (((LB.mapHomologicalComplex (.up ℤ)).obj P)) :=
    asIso (DerivedCategory.Q.map ((LB.mapHomologicalComplex (.up ℤ)).map f))
  let e : (ConstantScalarRealization.moduleDerivedExtension q').obj
      (DerivedCategory.Q.obj R') ≅
      LD.mapDerivedCategory.obj (T.mapDerivedCategory.obj (L.obj (DerivedCategory.Q.obj P))) :=
    asIso (ConstantScalarRealization.moduleRepresentative q' R') ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso
          (liftedTensorComparison (ρ.toRingHom.comp q)) (.up ℤ)).app R).symm ≪≫
      (LD.mapDerivedCategoryFactors.app _).symm ≪≫
      LD.mapDerivedCategory.mapIso
        (DerivedCategory.Q.mapIso
          ((NatIso.mapHomologicalComplex (scalarTransportIso q ρ) (.up ℤ)).app R) ≪≫
          (T.mapDerivedCategoryFactors.app Rq).symm ≪≫
          T.mapDerivedCategory.mapIso (r.symm ≪≫ L.mapIso a))
  exact ⟨(ConstantScalarRealization.moduleDerivedExtension q').mapIso a'.symm ≪≫ e ≪≫
    LD.mapDerivedCategory.mapIso
      (T.mapDerivedCategory.mapIso
        (DerivedCategory.Q.objObjPreimageIso (L.obj (DerivedCategory.Q.obj P))).symm ≪≫
        T.mapDerivedCategoryFactors.app _) ≪≫ LD.mapDerivedCategoryFactors.app _⟩

/-- Constant realization intertwines algebraic and sheaf derived scalar extension,
including transport of the output ring by a ring equivalence. This is independent
of adic data, local charts, and completed-coefficient objects.

Source: Stacks Project, sites-cohomology.tex, lemma-derived-base-change (06YY),
lemma-pullback-K-flat (0G7E), lemma-derived-pullback-composition (0D6D);
sites-modules.tex, lemma-constant-exact (093J).
(blueprint: lem-weil-pbc-finite-model-derived-scalar-comparison).

Proof: choose a flat-term K-flat resolution in the small module universe.
The coefficient lift preserves flat objects and integer-indexed colimits, so the
lifted resolution is K-flat too. Ordinary tensor commutes with coefficient lift
by its natural pure-tensor isomorphism. On the resolution, the canonical lifted
derived representative and the specified small universal counit are invertible.
Restricting along rho inverse transports the scalar-extended resolution to D;
uniqueness of left adjoints identifies this with extension along rho composed
with q. Transport the resulting isomorphism along the resolution augmentation
and the canonical representative of L(Q(P)). Finally identify the sheaf scalar
adjunctions by uniqueness of left adjoints, apply the existing generic derived
constant-realization comparison, and use the exact localization factors.
No ordinary-tensor computation is asserted for P itself. The statement includes
unbounded complexes, zero rings and empty sites. -/
theorem finiteModel_derivedScalarComparison
    (X : Scheme.{t}) {B C D : Type t} [CommRing B] [CommRing C] [CommRing D]
    (q : B →+* C) (ρ : C ≃+* D)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X D).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ)
    (L : DerivedCategory (ModuleCat.{t} B) ⥤ DerivedCategory (ModuleCat.{t} C))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (ModuleCat.extendScalars q)
        (ModuleCat.extendRestrictScalarsAdj q).left_adjoint_additive
        (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    let K := ((ModuleCat.restrictScalars.{t} ρ.symm.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj (DerivedCategory.Q.objPreimage (L.obj (DerivedCategory.Q.obj P)))
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X (ρ.toRingHom.comp q))).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        DerivedCategory.Q.obj (finiteModelConstantComplex X D K)) := by
  dsimp
  let J := ProEt.topology X
  let q' := RingHom.ulift.{t + 1, t + 1} (ρ.toRingHom.comp q)
  let P' := ((coefficientLift B).mapHomologicalComplex (.up ℤ)).obj P
  let s : completedAdicDerivedChange X (adicConstantMap X (ρ.toRingHom.comp q)) ≅
      ConstantScalarRealization.derivedExtension J q' :=
    (pbcDerivedScalarAdjunction (adicConstantMap X (ρ.toRingHom.comp q))).leftAdjointUniq
      (ConstantScalarRealization.derivedAdjunction J q')
  let cB := commutativeSiteConstantModuleFunctor J (ULift.{t + 1} B)
  let e₀ := (completedAdicDerivedChange X (adicConstantMap X (ρ.toRingHom.comp q))).mapIso
    (cB.mapDerivedCategoryFactors.app P').symm ≪≫ s.app _
  obtain ⟨e₁⟩ := liftedDerivedScalarRepresentative q ρ P L ε hL
  let c := commutativeSiteConstantModuleFunctor J (ULift.{t + 1} D)
  exact ⟨e₀ ≪≫ (ConstantScalarRealization.comparisonIso J q').app
    (DerivedCategory.Q.obj P') ≪≫
    (commutativeSiteDerivedConstantModuleFunctor J (ULift.{t + 1} D)).mapIso e₁ ≪≫
    c.mapDerivedCategoryFactors.app _⟩

end AlgebraicGeometry.Scheme
