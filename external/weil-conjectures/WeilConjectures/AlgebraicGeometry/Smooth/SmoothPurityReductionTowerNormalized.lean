/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
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
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerDescent
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerAdjunct
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTorIntervals
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionLevelConstructible

set_option linter.privateModule false

/-! # The reduction tower is normalized

Source: blueprint latest, chap-Smooth-purity, normalized-towers-reduction
(blueprint: proposition-sp-integral-towers--1).

The data declarations are re-exported unchanged from SmoothPurityReductionTowerData.
The proof assembles strict descent, the actual reduction adjuncts, the Tor interval
comparison and finite-level constructibility. Positive level n+1 is indexed by n.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

/-- Reconstruct the section-ring isomorphism from its multiplicative abelian map.
Source: IntegralCriterionReductions.liftSectionRingIso, Stacks 00YV. -/
private theorem ringPresheafMon_eq
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (R : Sheaf J RingCat.{u + 1}) :
    (sheafToPresheaf J Ab.{u + 1}).monObjObj
      ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R) =
        R.obj.monObjCompForget₂ := by
  apply MonObj.ext
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : MonObj A.obj := R.obj.monObjCompForget₂
  exact Sheaf.μ_comp_map_mul A

private theorem liftSectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (A : Sheaf J Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (S : Sheaf J CommRingCat.{u + 1})
    (a : A ≅ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    [IsMonHom a.hom] :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S,
      (sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.hom = a.hom := by
  let F := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor
  let h := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.hom)))
    InternalAbelianSheafModule.monToRing
  let k := Functor.whiskerRight
    (F.map ((sheafToPresheaf J Ab.{u + 1}).mapMon.map (Mon.ofHom a.inv)))
    InternalAbelianSheafModule.monToRing
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let B := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj B = R.obj.monObjCompForget₂ :=
    ringPresheafMon_eq J R
  let BP := F.obj ((sheafToPresheaf J Ab.{u + 1}).mapMon.obj (Mon.mk B)) ⋙
    InternalAbelianSheafModule.monToRing
  let b : BP ≅ R.obj := by
    refine NatIso.ofComponents (fun U ↦ ?_) (fun _ ↦ ?_)
    · refine @RingEquiv.toRingCatIso (BP.obj U) (R.obj.obj U)
        (RingCat.ring _) (RingCat.ring _) ?_
      refine { toEquiv := Equiv.refl _, map_add' := fun _ _ ↦ rfl, map_mul' := ?_ }
      intro x y
      change (((sheafToPresheaf J Ab.{u + 1}).monObjObj B).mul.app U).hom
        (TensorProduct.tmul ℤ x y) = _
      have hh := congrArg (fun m : MonObj B.obj ↦ m.mul) hmon
      rw [hh]
      rfl
    · ext x
      rfl
  let d : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A ≅ S :=
    { hom := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    (S.obj.obj U) _ _ ((h ≫ b.hom).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (h ≫ b.hom).naturality f }⟩
      inv := ⟨{ app := fun U ↦
                  @CommRingCat.ofHom (S.obj.obj U)
                    ((InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj U)
                    _ _ ((b.inv ≫ k).app U).hom
                naturality := fun U V f ↦ by
                  apply (forget₂ CommRingCat RingCat).map_injective
                  exact (b.inv ≫ k).naturality f }⟩
      hom_inv_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) a.hom_inv_id) U
        exact ConcreteCategory.congr_hom hh x
      inv_hom_id := by
        ext U x
        have hh := congr_app (congrArg (fun f : B ⟶ B ↦ f.hom) a.inv_hom_id) U
        exact ConcreteCategory.congr_hom hh x }
  have hd : (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map d.hom = a.hom := by
    ext U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
      forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  exact he.trans hd.symm

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale
