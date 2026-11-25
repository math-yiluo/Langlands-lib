/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Module.Projective
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction

/-!
# Completed constant sheaves and finite reduction

Source: Stacks Project, Modules on Sites, Tags 093J--093M;
Cohomology on Sites, Tags 06YN and 06YU
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.CompletedConstantReduction

open AdicCoefficients

/-- The completed coefficient sheaf as a module over the constant coefficient sheaf.
Source: Stacks Tag 093M (blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def completedModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map (base T I))).obj
    (SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I)))

section

private local instance completedConstantReductionSupplementRestrictedModule (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars (((adicLisseForget T).obj A).obj.map i).hom).obj
        (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} c M i) s m

end

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((adicLisseForget T).obj
    S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv T c M H)

private theorem tensorHomEquiv_tmul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R))
    (H : SheafOfModules.{u + 1} ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      s • (@id (H.val.obj U) ((tensorHomEquiv T φ M H f).val.app U m)) := by
  let k := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((adicLisseForget T).obj S).obj) f
  change k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
    s • k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  let k' : (ModuleCat.extendScalars (φ.hom.app U).hom).obj (M.val.obj U) ⟶
      H.val.obj U := k.app U
  have hh := k'.hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at hh
  exact hh

/-- A direct summand of a finite sum of copies of the completed coefficient ring.
The zero-fold sum is included. Source: Stacks Tag 093J, split finite-projective argument
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def IsFiniteRetract (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseCompletedRing T I))) : Prop :=
  ∃ r : ℕ,
    ∃ i : M ⟶ ∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I))),
    ∃ s : (∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I)))) ⟶ M,
      i ≫ s = 𝟙 M

set_option backward.isDefEq.respectTransparency false in
private theorem constant_exact (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules T A) ∧
      PreservesFiniteColimits (adicLisseConstantModules T A) := by
  let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P
    (PresheafOfModules.sheafification (adicLisseConstantUnit T A)),
    comp_preservesFiniteColimits P
      (PresheafOfModules.sheafification (adicLisseConstantUnit T A))⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def constantChange_unit (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A]
    {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (c : adicLisseConstantRing T A ⟶ S) :
    (completedAdicChange T c).obj ((adicLisseConstantModules T A).obj (ModuleCat.of A A)) ≅
      SheafOfModules.unit ((adicLisseForget T).obj S) := by
  let P : _root_.PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    (siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).obj
          (ModuleCat.of A A)
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A A)
  let H := SheafOfModules.unit ((adicLisseForget T).obj S)
  let N := (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H
  let q := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  let X := SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M
  let η₀ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (adicLisseConstantUnit T A)).unit.app P
  let η (U : T.ProEtᵒᵖ) (a : A) : M.val.obj U := η₀.app U a
  let e (U : T.ProEtᵒᵖ) : A →+* S.obj.obj U :=
    (c.hom.app U).hom.comp ((adicLisseConstantUnit T A).app U).hom
  let g₀ : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val :=
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val).obj U)
        { toFun := fun a ↦ e U a
          map_add' := (e U).map_add
          map_smul' := fun a b ↦ (e U).map_mul a b }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        change e V (show A from a) = S.obj.map f (e U a)
        dsimp only [e, RingHom.comp_apply]
        rw [← NatTrans.naturality_apply]
        exact congrArg (c.hom.app V) (ConcreteCategory.congr_hom
          ((adicLisseConstantUnit T A).naturality f) a) }
  let g : M ⟶ N := (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit T A) (P := P) (F := N)).symm g₀
  let r : X ⟶ H := (tensorHomEquiv T c M H).symm g
  have hr (U : T.ProEtᵒᵖ) (b : S.obj.obj U) (a : A) :
      r.val.app U ((toSheafify (ProEt.topology T) q.presheaf).app U
        (b ⊗ₜ[(adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom]
          (η U a))) = b * e U a := by
    rw [tensorHomEquiv_tmul]
    have he : tensorHomEquiv T c M H r = g :=
      (tensorHomEquiv T c M H).apply_symm_apply g
    rw [he]
    have hg := congrArg (fun (k : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val) ↦
        (k.app U).hom a)
      ((PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) (P := P) (F := N)).apply_symm_apply g₀)
    change g.val.app U (η U a) = e U a at hg
    rw [hg]
    rfl
  let t (U : T.ProEtᵒᵖ) : X.val.obj U :=
    (toSheafify (ProEt.topology T) q.presheaf).app U
      ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
        (c.hom.app U).hom] (η U (1 : A)))
  let z : X.sections := PresheafOfModules.sectionsMk t (by
    intro U V f
    have hη := ConcreteCategory.congr_hom (η₀.naturality f) (1 : A)
    change η V (1 : A) = M.val.map f (η U (1 : A)) at hη
    have ht := ConcreteCategory.congr_hom
      ((toSheafify (ProEt.topology T) q.presheaf).naturality f)
        ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
          (c.hom.app U).hom] (η U (1 : A)))
    change (toSheafify (ProEt.topology T) q.presheaf).app V
      (q.map f ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
        (c.hom.app U).hom] (η U (1 : A)))) = X.val.map f (t U) at ht
    rw [tensorRestriction_tmul T, map_one, ← hη] at ht
    exact ht.symm)
  let s : H ⟶ X := X.unitHomEquiv.symm z
  have hs (U : T.ProEtᵒᵖ) (b : S.obj.obj U) : s.val.app U b = b • t U := rfl
  let j : X ≅ H :=
    { hom := r
      inv := s
      hom_inv_id := by
        apply (tensorHomEquiv T c M X).injective
        apply (PresheafOfModules.sheafificationHomEquiv.{u + 1}
          (adicLisseConstantUnit T A) (P := P) (F :=
            (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj X)).injective
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        have hl := tensorHomEquiv_tmul T c M X (r ≫ s) U 1 (η U a)
        have hi := tensorHomEquiv_tmul T c M X (𝟙 X) U 1 (η U a)
        simp only [one_smul, id_eq] at hl hi
        change (tensorHomEquiv T c M X (r ≫ s)).val.app U (η U a) =
          (tensorHomEquiv T c M X (𝟙 X)).val.app U (η U a)
        rw [← hl, ← hi]
        change s.val.app U (r.val.app U (_)) = _
        rw [hr, one_mul, hs]
        let κ := (PresheafOfModules.sheafificationAdjunction.{u + 1}
          (𝟙 ((adicLisseForget T).obj S).obj)).unit.app q
        change e U a • (@id (X.val.obj U) (κ.app U _)) = κ.app U _
        change (e U a) • ((κ.app U).hom _) = (κ.app U).hom _
        rw [← (κ.app U).hom.map_smul]
        congr 1
        have hη := (η₀.app U).hom.map_smul (show A from a) (1 : A)
        change η U ((show A from a) * 1) =
          ((adicLisseConstantUnit T A).app U a) • (η U (1 : A)) at hη
        rw [mul_one] at hη
        rw [hη]
        let : Module ((adicLisseConstantRing T A).obj.obj U) (S.obj.obj U) :=
          Module.compHom _ (c.hom.app U).hom
        change ((e U a) * 1) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
          (c.hom.app U).hom] (η U (1 : A)) =
            (1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
              (c.hom.app U).hom]
                (((adicLisseConstantUnit T A).app U a) • (η U (1 : A)))
        exact TensorProduct.smul_tmul
          (R := (adicLisseConstantRing T A).obj.obj U)
          (show (adicLisseConstantRing T A).obj.obj U from
            (adicLisseConstantUnit T A).app U a) (1 : S.obj.obj U) (η U (1 : A))
      inv_hom_id := by
        apply H.unitHomEquiv.injective
        ext U
        change r.val.app U (s.val.app U (1 : S.obj.obj U)) = (1 : S.obj.obj U)
        rw [hs, one_smul]
        change r.val.app U ((toSheafify (ProEt.topology T) q.presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[(adicLisseConstantRing T A).obj.obj U,
            (c.hom.app U).hom] (η U (1 : A)))) = _
        rw [hr, map_one, one_mul] }
  exact (eqToIso ((completedAdicChangeData T c).choose_spec.choose M)) ≪≫ j

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] constantChange_unit

private theorem constantChange_retract (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (N : ModuleCat.{u + 1} A) [IsNoetherianRing A]
    [Module.Finite A N] [Module.Projective A N] :
    IsFiniteRetract T I
      ((completedAdicChange T (base T I)).obj ((adicLisseConstantModules T A).obj N)) := by
  let K := adicLisseConstantModules T A
  let E := completedAdicChange T (base T I)
  have : K.Additive := constant_additive T A
  have : PreservesFiniteColimits K := (constant_exact T A).2
  have : PreservesFiniteColimits E := by
    exact ((exactFunctor_iff E).1
      (completed_constant_algebra_flat_quotients T I _ (Iso.refl _) (base T I)
        (fun n ↦ by simpa [base] using (base_exists T I).choose_spec.1 n)).2.1).2
  let G := K ⋙ E
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A N
  let V := fun _ : Fin r ↦ ModuleCat.of A A
  let j : ModuleCat.of A (Fin r → A) ≅ ∐ V :=
    (ModuleCat.piIsoPi V).symm ≪≫ biproductIso V
  let i := G.map (ModuleCat.ofHom g ≫ j.hom)
  let p := G.map (j.inv ≫ ModuleCat.ofHom f)
  have hip : i ≫ p = 𝟙 (G.obj N) := by
    rw [← G.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have h : ModuleCat.ofHom g ≫ ModuleCat.ofHom f = 𝟙 N :=
      ModuleCat.hom_ext hfg
    rw [h, G.map_id]
  let v : G.obj (∐ V) ≅ ∐ (fun _ : Fin r ↦
      SheafOfModules.unit ((adicLisseForget T).obj (adicLisseCompletedRing T I))) :=
    PreservesCoproduct.iso G V ≪≫ Sigma.mapIso
      (fun _ ↦ constantChange_unit T (base T I))
  change ∃ r, ∃ i : G.obj N ⟶ _, ∃ p, i ≫ p = 𝟙 (G.obj N)
  exact ⟨r, i ≫ v.hom, v.inv ≫ p, by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hip⟩

/-- The augmentation of the constant sheaf resolution, with the standard degree-zero
comparison. Source: Stacks Tag 093J
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def constantAugmentation (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor _ 0).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1)))) :=
  letI := constant_additive T A
  (constantComplex T A).map f ≫
    ((adicLisseConstantModules T A).mapCochainComplexSingleFunctor 0).hom.app _

set_option backward.isDefEq.respectTransparency false in
/-- Flatness, the canonical derived reduction, and its bounded finite-projective model.
Source: Stacks Tags 093J--093M and 06YU
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: (1) Constant quotient sections are flat over their Noetherian quotient rings and have
surjective transitions (`lem-weil-pbc-constant-module-section-properties`). Apply
`lem-weil-pbc-limit-flat-modules` sectionwise, then
`lem-pc-sites-modules-sheafification-flat`, obtaining flatness over the constant ring sheaf.
(2) The tensor-limit comparison for the finite module A/I^(n+1) is eventually constant;
its projection-and-multiplication formula is precisely `reduction`, hence it is invertible.
(3) Exact scalar extension preserves quasi-isomorphisms, so on every K-flat resolution
its canonical reduction is a quasi-isomorphism and represents the required derived iso.
(4) Finite projectives split off finite free modules. Constant sheafification and scalar
extension preserve the splitting. Their exactness preserves the augmented resolution,
and termwise application retains the given two bounds. -/
theorem completed_constant_sheaf_reduction (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlatOnSite (completedModule T I) ∧
    (∀ n : ℕ, IsIso (reduction T I n)) ∧
    (∀ (n : ℕ) (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
      (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))),
      CochainComplex.IsAcyclicTensorKFlat (R := adicLisseConstantRing T A) P → QuasiIso f →
        QuasiIso (reductionComplex T I n P f)) ∧
    (∀ (n : ℕ) (F : CochainComplex (ModuleCat.{u + 1} A) ℤ)
      (f : F ⟶ (CochainComplex.singleFunctor _ 0).obj
        (ModuleCat.of A (A ⧸ I ^ (n + 1)))) (a b : ℤ),
      QuasiIso f →
      (∀ i : ℤ, Module.Finite A (F.X i) ∧ Module.Projective A (F.X i)) →
      (∀ i : ℤ, i < a ∨ b < i → IsZero (F.X i)) →
      QuasiIso (reductionComplex T I n ((constantComplex T A).obj F)
        (constantAugmentation T I n F f)) ∧
      (∀ i : ℤ, IsFiniteRetract T I
        ((completedAdicChange T (base T I)).obj (((constantComplex T A).obj F).X i))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero
        ((completedAdicChange T (base T I)).obj (((constantComplex T A).obj F).X i)))) := by
  have h := completed_constant_algebra_flat_quotients T I _ (Iso.refl _) (base T I)
    (fun n ↦ by simpa [base] using (base_exists T I).choose_spec.1 n)
  have he := (exactFunctor_iff (completedAdicChange T (base T I))).1 h.2.1
  have : PreservesFiniteLimits (completedAdicChange T (base T I)) := he.1
  have : PreservesFiniteColimits (completedAdicChange T (base T I)) := he.2
  have hr (n : ℕ) : IsIso (reduction T I n) := by
    refine h.2.2 n _ (Iso.refl _) (limit.π (adicLisseRingSystem T I) (op n))
      (by
        change limit.π (adicLisseRingSystem T I) (op n) =
          𝟙 _ ≫ limit.π (adicLisseRingSystem T I) (op n) ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]) (reduction T I n) ?_
    exact (reduction_exists T I n).choose_spec.1
  refine ⟨h.1, hr, ?_, ?_⟩
  · intro n P f _ hf
    have := hf
    have := hr n
    unfold reductionComplex
    infer_instance
  · intro n F f a b hf hF hb
    have : (adicLisseConstantModules T A).Additive := constant_additive T A
    have : PreservesFiniteLimits (adicLisseConstantModules T A) := (constant_exact T A).1
    have : PreservesFiniteColimits (adicLisseConstantModules T A) := (constant_exact T A).2
    have := hf
    have := hr n
    refine ⟨?_, ?_, ?_⟩
    · unfold reductionComplex constantAugmentation constantComplex
      infer_instance
    · intro i
      have := (hF i).1
      have := (hF i).2
      exact constantChange_retract T I (F.X i)
    · intro i hi
      exact (completedAdicChange T (base T I)).map_isZero
        ((adicLisseConstantModules T A).map_isZero (hb i hi))

/-- Constants-to-functions comparisons commute with every quotient transition.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: both presheaf composites send a constant value to the constant function of its quotient
image. Sheafification preserves this equality, and composites give every tower transition. -/
theorem systemComparison_naturality (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1)))
    (m n : ℕᵒᵖ) (f : m ⟶ n) :
    (adicLisseRingSystem T I).map f ≫
      @constantComparison _ _ _ (hf n.unop) =
    @constantComparison _ _ _ (hf m.unop) ≫ (ringSystem T I hf).map f := by
  let := hf
  let c : adicLisseRingSystem T I ⟶ ringSystem T I hf :=
    NatTrans.ofOpSequence (fun n ↦ constantComparison T (A ⧸ I ^ (n + 1))) (by
      intro k
      simp only [adicLisseRingSystem, ringSystem, Functor.ofOpSequence_map_homOfLE_succ,
        constantComparison, constantSheaf, Functor.comp_map, coefficientMap,
        ← Functor.map_comp]
      congr 1)
  exact c.naturality f

/-- The canonical comparison of quotient ring diagrams, retaining the quotient maps.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def systemComparison (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    adicLisseRingSystem T I ⟶ ringSystem T I hf where
  app n := @constantComparison T (A ⧸ I ^ (n.unop + 1)) _ (hf n.unop)
  naturality m n f := systemComparison_naturality T I hf m n f

/-- The canonical comparison of inverse-limit coefficient rings.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def completedComparison (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    adicLisseCompletedRing T I ⟶ completedRing T I hf :=
  lim.map (systemComparison T I hf)

/-- The quotient function sheaf as a module over completed function coefficients.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteResidue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :=
  AdicCoefficients.residue T I hf n

/-- The finite-coefficient reduction is fixed by projection and the image of each constant
quotient value. Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: the specified formula is balanced over the constant A action. Its restrictions commute
with the formula, so it sheafifies. Constant module generators and local tensor generators
prove uniqueness. This is the transport of the ordinary reduction along the ring comparisons. -/
theorem finiteReduction_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :
    ∃! r : (completedAdicChange T (base T I ≫ completedComparison T I hf)).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
          finiteResidue T I hf n,
      ∀ (U : T.ProEtᵒᵖ) (b : (completedRing T I hf).obj.obj U)
        (x : A ⧸ I ^ (n + 1)),
        r.val.app U (tensorSection T (base T I ≫ completedComparison T I hf) _ U b
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
            (limit.π (ringSystem T I hf) (op n)).hom.app U b *
              ((systemComparison T I hf).app (op n)).hom.app U
                (@id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
                  ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x)) := by
  let Q := A ⧸ I ^ (n + 1)
  let H := (ringSystem T I hf).obj (op n)
  let d : adicLisseConstantRing T Q ⟶ H := (systemComparison T I hf).app (op n)
  let c := base T I ≫ completedComparison T I hf
  let e (U : T.ProEtᵒᵖ) : Q →+* H.obj.obj U :=
    (d.hom.app U).hom.comp ((adicLisseConstantUnit T Q).app U).hom
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A Q)
  let N := (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj
    (finiteResidue T I hf n)
  let P : _root_.PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    (siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).obj
        (ModuleCat.of A Q)
  let g₀ : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val :=
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val).obj U)
        { toFun := fun (x : Q) ↦ (e U) x
          map_add' := fun (x y : Q) ↦ map_add (e U) x y
          map_smul' := by
            intro a x
            have hb : c ≫ limit.π (ringSystem T I hf) (op n) =
                (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
                  (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) ≫ d := by
              change (base T I ≫ limMap (systemComparison T I hf)) ≫ _ = _
              rw [Category.assoc, limMap_π, ← Category.assoc]
              exact congrArg (fun z ↦ z ≫ d) ((base_exists T I).choose_spec.1 n)
            change (e U) (a • x) =
              @id (H.obj.obj U)
                ((limit.π (ringSystem T I hf) (op n)).hom.app U
                  (c.hom.app U ((adicLisseConstantUnit T A).app U a))) *
                    @id (H.obj.obj U)
                      ((e U) x)
            have h := congrArg (fun k ↦ (k.hom.app U) ((adicLisseConstantUnit T A).app U a)) hb
            change (limit.π (ringSystem T I hf) (op n)).hom.app U
                (c.hom.app U ((adicLisseConstantUnit T A).app U a)) = _ at h
            dsimp only [id_eq]
            rw [h]
            have hn := toSheafify_naturality (ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
            have hn' := congrArg (fun k ↦ (k.app U).hom (show A from a)) hn
            change (adicLisseConstantUnit T Q).app U
                ((Ideal.Quotient.mk (I ^ (n + 1))) a) =
              ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U
                  ((adicLisseConstantUnit T A).app U a) at hn'
            change e U (a • x) = (d.hom.app U).hom
              (((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U
                  ((adicLisseConstantUnit T A).app U a)) * e U x
            rw [← hn']
            change e U ((Ideal.Quotient.mk (I ^ (n + 1))) a * (show Q from x)) = _
            exact map_mul (e U) ((Ideal.Quotient.mk (I ^ (n + 1))) a) x }
      naturality := by
        intro U V f
        ext x
        change e V (show Q from x) = H.obj.map f (e U x)
        change (d.hom.app V) ((adicLisseConstantUnit T Q).app V x) =
          H.obj.map f ((d.hom.app U) ((adicLisseConstantUnit T Q).app U x))
        have hu := ConcreteCategory.congr_hom
          ((adicLisseConstantUnit T Q).naturality f) x
        change (adicLisseConstantUnit T Q).app V (show Q from x) =
          (adicLisseRing T Q).obj.map f ((adicLisseConstantUnit T Q).app U x) at hu
        rw [hu]
        exact NatTrans.naturality_apply d.hom f
          ((adicLisseConstantUnit T Q).app U x) }
  let g : M ⟶ N := (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit T A) (P := P) (F := N)).symm g₀
  let h := (completedAdicChangeData T c).choose_spec.choose M
  let r₀ := (tensorHomEquiv T c M (finiteResidue T I hf n)).symm g
  let r := eqToHom h ≫ r₀
  have hc : eqToHom h.symm ≫ r = r₀ := by simp [r]
  refine ⟨r, ?_, ?_⟩
  · intro U b x
    change (eqToHom h.symm ≫ r).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf c M).presheaf).app U
          (b ⊗ₜ[(adicLisseConstantRing T A).obj.obj U, (c.hom.app U).hom]
            ((toSheafify (ProEt.topology T) P.presheaf).app U x))) = _
    rw [hc]
    refine (tensorHomEquiv_tmul T c M (finiteResidue T I hf n) r₀ U b
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)).trans ?_
    have he : tensorHomEquiv T c M (finiteResidue T I hf n) r₀ = g :=
      (tensorHomEquiv T c M (finiteResidue T I hf n)).apply_symm_apply g
    rw [he]
    have hg₀ : PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) g = g₀ :=
      (PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) (P := P) (F := N)).apply_symm_apply g₀
    have hg := congrArg (fun (k : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val) ↦
        (k.app U).hom x) hg₀
    change g.val.app U ((toSheafify (ProEt.topology T) P.presheaf).app U x) =
      (e U) x at hg
    rw [hg]
    rfl
  · intro s hs
    apply (cancel_epi (eqToHom h.symm)).mp
    rw [hc]
    apply (tensorHomEquiv T c M (finiteResidue T I hf n)).injective
    have he : tensorHomEquiv T c M (finiteResidue T I hf n) r₀ = g :=
      (tensorHomEquiv T c M (finiteResidue T I hf n)).apply_symm_apply g
    refine Eq.trans ?_ he.symm
    apply (PresheafOfModules.sheafificationHomEquiv.{u + 1}
      (adicLisseConstantUnit T A) (P := P) (F := N)).injective
    have hg : PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) g = g₀ :=
      (PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) (P := P) (F := N)).apply_symm_apply g₀
    refine Eq.trans ?_ hg.symm
    ext U x
    have ht := tensorHomEquiv_tmul T c M (finiteResidue T I hf n)
      (eqToHom h.symm ≫ s) U 1
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)
    have hx := hs U 1 (show Q from x)
    simp only [one_smul] at ht
    change (tensorHomEquiv T c M (finiteResidue T I hf n)
      (eqToHom h.symm ≫ s)).val.app U
        ((toSheafify (ProEt.topology T) P.presheaf).app U x) =
          (e U) x
    refine ht.symm.trans ?_
    change s.val.app U (tensorSection T c M U 1
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)) = _
    simp only [map_one, id_eq, one_mul] at hx
    convert hx using 1
    rfl

/-- The finite-coefficient reduction map, specified uniquely on tensor generators.
Source: blueprint finite-coefficient interpretation, Stacks Tag 093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ) :=
  (finiteReduction_exists T I hf n).choose

/-- The canonical derived finite reduction on a chosen K-flat representative of the quotient.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-completed-constant-sheaf-reduction). -/
def finiteReductionComplex (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) (n : ℕ)
    (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
    (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))) :=
  ((completedAdicChange T
    (base T I ≫ completedComparison T I hf)).mapHomologicalComplex (.up ℤ)).map f ≫
    ((completedAdicChange T
      (base T I ≫ completedComparison T I hf)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map (finiteReduction T I hf n)

set_option backward.isDefEq.respectTransparency false in
private theorem constantComparison_isIso (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] : IsIso (constantComparison T Λ) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let J := ProEt.topology T
  let F := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let g := (finiteRingComparison_exists T Λ).choose
  have hg := (finiteRingComparison_exists T Λ).choose_spec.1
  have : IsIso g := hg.1
  let η := Functor.whiskerRight
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ))) F
  let k := Functor.whiskerRight (constantComparison T Λ).hom F ≫ g.hom
  have hk : η ≫ k = ProEtale.finiteCoefficientScalarMap T Λ := by
    dsimp only [η, k]
    rw [← Category.assoc, ← Functor.whiskerRight_comp]
    change Functor.whiskerRight
      (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)) ≫
        sheafifyMap J (constants T Λ)) F ≫ g.hom = _
    rw [← toSheafify_naturality, Functor.whiskerRight_comp, Category.assoc, hg.2]
    rfl
  have : Presheaf.IsLocallyInjective J (η ≫ k) := hk.symm ▸ inferInstance
  have : Presheaf.IsLocallySurjective J (η ≫ k) := hk.symm ▸ inferInstance
  have : Presheaf.IsLocallyInjective J η :=
    (Presheaf.isLocallyInjective_forget_iff J η).1
      (inferInstanceAs (Presheaf.IsLocallyInjective J (Functor.whiskerRight
        (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))
  have : Presheaf.IsLocallySurjective J η :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J η).2
      (inferInstanceAs (Presheaf.IsLocallySurjective J (Functor.whiskerRight
        (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ)))
          (CategoryTheory.forget CommRingCat.{u + 1}))))
  have : Presheaf.IsLocallyInjective J k :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J η k
  have : Presheaf.IsLocallySurjective J k :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J η k
  let z : (adicLisseForget T).obj (adicLisseConstantRing T Λ) ⟶
      finiteRingPresentation T Λ := ⟨k⟩
  have : IsIso z := (Sheaf.isLocallyBijective_iff_isIso z).1
    ⟨inferInstance, inferInstance⟩
  have : IsIso ((adicLisseForget T).map (constantComparison T Λ) ≫ g) :=
    inferInstanceAs (IsIso z)
  have : IsIso ((adicLisseForget T).map (constantComparison T Λ)) :=
    IsIso.of_isIso_comp_right _ g
  exact isIso_of_reflects_iso (constantComparison T Λ) (adicLisseForget T)

set_option backward.isDefEq.respectTransparency false in
/-- Finite function coefficients are precisely constant finite quotient sheaves, naturally
in the quotient system, and the canonical reduction agrees after this identification.
Source: blueprint finite-coefficient interpretation; Stacks Tags 093J--093M
(blueprint: lem-weil-pbc-completed-constant-sheaf-reduction).
Proof: a continuous function to a finite discrete ring has finitely many clopen fibres in the
underlying scheme. These form a pro-etale cover. Gluing the constant values on that cover
proves the universal property of the constant sheafification. The empty object is handled by
its empty covering. Postcomposition with ring maps respects those gluings, so the quotient
comparisons are compatible. Limits preserve these natural isomorphisms. On local tensor
generators the transported reduction is exactly the formula defining finiteReduction.
The ordinary reduction and every K-flat representative are thus isomorphic by the first
four clauses of completed_constant_sheaf_reduction. -/
theorem finite_coefficient_identification (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hf : ∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))) :
    (∀ n : ℕ, IsIso ((systemComparison T I hf).app (op n))) ∧
    IsIso (completedComparison T I hf) ∧
    (∀ n : ℕ, IsIso (finiteReduction T I hf n)) ∧
    (∀ (n : ℕ) (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
      (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))),
      CochainComplex.IsAcyclicTensorKFlat (R := adicLisseConstantRing T A) P → QuasiIso f →
        QuasiIso (finiteReductionComplex T I hf n P f)) := by
  have hc (n : ℕ) : IsIso ((systemComparison T I hf).app (op n)) :=
    @constantComparison_isIso T (A ⧸ I ^ (n + 1)) _ (hf n)
  have (n : ℕᵒᵖ) : IsIso ((systemComparison T I hf).app n) := hc n.unop
  have : IsIso (systemComparison T I hf) := NatIso.isIso_of_isIso_app _
  have hl : IsIso (completedComparison T I hf) :=
    inferInstanceAs (IsIso (lim.map (systemComparison T I hf)))
  have := hl
  let e := asIso (completedComparison T I hf)
  let c := base T I ≫ completedComparison T I hf
  have h := completed_constant_algebra_flat_quotients T I _ e c (by
    intro n
    simp only [c, e, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
    exact (base_exists T I).choose_spec.1 n)
  have he := (exactFunctor_iff (completedAdicChange T c)).1 h.2.1
  have : PreservesFiniteLimits (completedAdicChange T c) := he.1
  have : PreservesFiniteColimits (completedAdicChange T c) := he.2
  have hr (n : ℕ) : IsIso (finiteReduction T I hf n) := by
    have := hc n
    refine h.2.2 n _ (asIso ((systemComparison T I hf).app (op n)))
      (limit.π (ringSystem T I hf) (op n)) ?_ (finiteReduction T I hf n) ?_
    · apply (cancel_epi (completedComparison T I hf)).1
      simp only [IsIso.hom_inv_id_assoc, e, asIso_inv]
      exact limMap_π (systemComparison T I hf) (op n)
    · exact (finiteReduction_exists T I hf n).choose_spec.1
  refine ⟨hc, hl, hr, ?_⟩
  intro n P f _ hf'
  have := hf'
  have := hr n
  unfold finiteReductionComplex
  infer_instance

end AlgebraicGeometry.Scheme.CompletedConstantReduction
