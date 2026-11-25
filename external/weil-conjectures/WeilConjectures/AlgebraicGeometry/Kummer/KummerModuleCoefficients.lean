/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Module coefficients for the Kummer sheaf

The twist is the sheafification of the sectionwise tensor of the existing roots-of-unity
module presheaf with a constant module presheaf. This is the sheaf tensor product with the
constant sheaf. Insertion of a coefficient is defined on sections before sheafification.

## References

* Stacks, Tags 03PK and 03EK
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- The existing root module presheaf with a universe lift of its coefficient ring. -/
def kummerRootModulePresheaf (X : Scheme.{u}) (m : ℕ) :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) :=
  finiteEtaleMuModulePresheaf X m ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- The coefficient functor `A ↦ μ_m ⊗ A_C`, by sectionwise tensor and sheafification. -/
def kummerModuleTwist (X : Scheme.{u}) (m : ℕ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :=
  Functor.const X.Etaleᵒᵖ ⋙ tensorLeft (kummerRootModulePresheaf X m) ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))

/-- The underlying abelian coefficient functor. -/
def kummerAbelianTwist (X : Scheme.{u}) (m : ℕ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kummerModuleTwist X m ⋙
    sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat)

/-- Insertion of a coefficient into a local pure tensor, followed by sheafification. -/
def kummerCoefficientInsertionApp (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) (U : X.Etaleᵒᵖ) :
    (X.rootsOfUnitySheaf m).obj.obj U →+
      ((kummerAbelianTwist X m).obj A).obj.obj U :=
  ((toSheafify X.smallEtaleTopology
    (kummerRootModulePresheaf X m ⊗ (Functor.const X.Etaleᵒᵖ).obj A)).app U).hom.toAddMonoidHom.comp
      ((TensorProduct.mk (ULift.{u + 1} (ZMod m))
        ((kummerRootModulePresheaf X m).obj U) A).flip a).toAddMonoidHom

/-- The insertion maps commute with restrictions. -/
theorem kummerCoefficientInsertion_naturality (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) (U V : X.Etaleᵒᵖ) (f : U ⟶ V) :
    (X.rootsOfUnitySheaf m).obj.map f ≫
        AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a V) =
      AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a U) ≫
        ((kummerAbelianTwist X m).obj A).obj.map f := by
  ext x
  let P := kummerRootModulePresheaf X m ⊗ (Functor.const X.Etaleᵒᵖ).obj A
  have h := congrArg (fun g ↦ g.hom (TensorProduct.tmul _ x a))
    ((toSheafify X.smallEtaleTopology P).naturality f)
  change ((toSheafify X.smallEtaleTopology P).app V).hom
      ((P.map f).hom (TensorProduct.tmul _ x a)) =
    ((sheafify X.smallEtaleTopology P).map f).hom
      (((toSheafify X.smallEtaleTopology P).app U).hom (TensorProduct.tmul _ x a)) at h
  have hp : (P.map f).hom
      (TensorProduct.tmul _ (x : (kummerRootModulePresheaf X m).obj U) a) =
      TensorProduct.tmul _
        ((kummerRootModulePresheaf X m).map f x) a := by
    rfl
  rw [hp] at h
  exact h

/-- The canonical map `i_a: μ_m → μ_m ⊗ A_C`, `x ↦ x ⊗ a`. -/
def kummerCoefficientInsertion (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) :
    X.rootsOfUnitySheaf m ⟶ (kummerAbelianTwist X m).obj A :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a U)
     naturality := kummerCoefficientInsertion_naturality X m A a }⟩

end AlgebraicGeometry.Scheme
