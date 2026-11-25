/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Exactness of restricted associated sheaves of a resolution

## References

* Stacks Project, Tag 01I6 (associated sheaf) and Tag 09T2
* Stacks Project, Tag 0A6T (proof of Lemma 51.2.1)
-/

@[expose] public noncomputable section

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Associate a module sheaf, restrict it to `W`, and forget its scalar action. -/
def puncturedRestrictedAbelianFunctor (R : Type u) [CommRing R]
    (W : (Spec (.of R)).Opens) :
    ModuleCat.{u} R ⥤
      Sheaf (Opens.grothendieckTopology W.toScheme.carrier)
        AddCommGrpCat.{u} :=
  tilde.functor (.of R) ⋙ Modules.restrictFunctor W.ι ⋙
    SheafOfModules.toSheaf W.toScheme.ringCatSheaf

/-- The restricted associated-sheaf functor sends zero maps to zero. -/
instance puncturedRestrictedAbelianFunctor_preservesZeroMorphisms
    (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens) :
    (puncturedRestrictedAbelianFunctor R W).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    change (SheafOfModules.toSheaf W.toScheme.ringCatSheaf).map
      ((Modules.restrictFunctor W.ι).map (tilde.map (0 : M ⟶ N))) = 0
    rw [tilde.map_zero]
    rfl

/-- Restricting the associated sheaves of a module resolution gives an exact
augmented abelian-sheaf complex on `W`. -/
theorem punctured_tilde_resolution_exact
    (R : Type u) [CommRing R] (W : (Spec (.of R)).Opens)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) :
    ∃ ι : (CochainComplex.single₀ _).obj
        ((SheafOfModules.toSheaf W.toScheme.ringCatSheaf).obj
          (SheafOfModules.unit W.toScheme.ringCatSheaf)) ⟶
        ((puncturedRestrictedAbelianFunctor R W).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex,
      QuasiIso ι := by
  let T := tilde.functor (.of R)
  let : T.IsLeftAdjoint := (tilde.adjunction (R := .of R)).isLeftAdjoint
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let : Limits.PreservesFiniteLimits T := tilde_preserves_finite_limits R
  let S := Modules.restrictFunctor W.ι
  let : S.Additive := Functor.additive_of_preserves_binary_products S
  let A := SheafOfModules.toSheaf W.toScheme.ringCatSheaf
  have : A.Additive := ⟨by intros; rfl⟩
  let F := puncturedRestrictedAbelianFunctor R W
  have : F.Additive := inferInstanceAs ((T ⋙ S ⋙ A).Additive)
  have : Limits.PreservesFiniteColimits T := inferInstance
  have : Limits.PreservesFiniteLimits S := inferInstance
  have : Limits.PreservesFiniteColimits S := inferInstance
  have : Limits.PreservesFiniteLimits A := inferInstance
  have : Limits.PreservesFiniteColimits A := inferInstance
  have : Limits.PreservesFiniteLimits (S ⋙ A) := Limits.comp_preservesFiniteLimits S A
  have : Limits.PreservesFiniteColimits (S ⋙ A) := Limits.comp_preservesFiniteColimits S A
  have : Limits.PreservesFiniteLimits F := Limits.comp_preservesFiniteLimits T (S ⋙ A)
  have : Limits.PreservesFiniteColimits F := Limits.comp_preservesFiniteColimits T (S ⋙ A)
  have : F.PreservesHomology := inferInstance
  let e : F.obj (ModuleCat.of R R) ≅ A.obj (SheafOfModules.unit W.toScheme.ringCatSheaf) :=
    A.mapIso (S.mapIso (tildeSelf (R := .of R)) ≪≫ Modules.restrictUnitIso W.ι)
  let ι := (CochainComplex.single₀ _).map e.inv ≫
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app
      (ModuleCat.of R R) ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := inferInstance
  exact ⟨ι, inferInstance⟩

end AlgebraicGeometry.Scheme
