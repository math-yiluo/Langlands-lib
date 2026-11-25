/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison

/-! # Tensor compatibility of derived pro-etale pullback composition

The proof is the pro-etale counterpart of the source library's etale composition proof.

## References

* Stacks 03EL and 07A4
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u' u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
universe v₁ v₂ v₃

attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.leftDerivedTensorComparison
  Functor.leftDerivedFunctorNatIso Functor.leftDerivedFunctorCompIso

private theorem derived_tensor_compositor
    {C : Type v₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasFunctorialFlatResolution C]
    {D : Type v₂} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasFunctorialFlatResolution D]
    {E : Type v₃} [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E]
    [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    [HasFunctorialFlatResolution E]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]
    (e : H ≅ F ⋙ G) [NatTrans.IsMonoidal e.inv]
    (d : H.leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ G.leftDerivedFunctor)
    (hd : d = H.leftDerivedFunctorNatIso e ≪≫ F.leftDerivedFunctorCompIso G)
    (mF : F.leftDerivedDerivedTensor ⟶ F.derivedTensorLeftDerived)
    (mG : G.leftDerivedDerivedTensor ⟶ G.derivedTensorLeftDerived)
    (mH : H.leftDerivedDerivedTensor ⟶ H.derivedTensorLeftDerived)
    (hF : mF = F.leftDerivedTensorComparison)
    (hG : mG = G.leftDerivedTensorComparison)
    (hH : mH = H.leftDerivedTensorComparison)
    (K M : DerivedCategory C) :
    (mH.app K).app M ≫
      (d.hom.app K ⊗ₘ
        d.hom.app M) =
    d.hom.app (K ⊗ M) ≫
      G.leftDerivedFunctor.map ((mF.app K).app M) ≫
        (mG.app (F.leftDerivedFunctor.obj K)).app
          (F.leftDerivedFunctor.obj M) := by
  subst d mF mG mH
  let : NatTrans.IsMonoidal e.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.inv)
  let : NatTrans.IsMonoidal e.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.symm.inv)
  rw [Functor.map_leftDerivedTensorComparison_app_app_comp F G K M]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← tensorHom_comp_tensorHom]
  have hn := Functor.leftDerivedTensorComparison_naturality_app e K M
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t ↦ t ≫
      ((F.leftDerivedFunctorCompIso G).hom.app K ⊗ₘ
        (F.leftDerivedFunctorCompIso G).hom.app M)) hn.symm).trans
      (Category.assoc _ _ _))

namespace AlgebraicGeometry.ProEtale
open Scheme _root_.DerivedCategory

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [HasFunctorialFlatResolution A]
  [ProEtale.UpperStarPreservesFlat A]
open Functor.LaxMonoidal Functor.OplaxMonoidal
attribute [local irreducible] upperStar Functor.mapDerivedCategory
variable {T S R : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R)

/-- The derived pullback compositor preserves the canonical tensor comparison. -/
theorem leftDerivedUpperStarTensorComparison_comp
    [NatTrans.IsMonoidal (upperStarComp A f g).inv]
    (K M : DerivedCategory (Sheaf (Scheme.ProEt.topology R) A)) :
    (leftDerivedUpperStarComp A f g).hom.app (((derivedTensor A R).obj K).obj M) ≫
        L((f)^*[A]).map (leftDerivedUpperStarTensorIso A g K M).hom ≫
        (leftDerivedUpperStarTensorIso A f (L((g)^*[A]).obj K)
          (L((g)^*[A]).obj M)).hom =
      (leftDerivedUpperStarTensorIso A (f ≫ g) K M).hom ≫
        ((derivedTensor A T).map ((leftDerivedUpperStarComp A f g).hom.app K)).app
          (L((f ≫ g)^*[A]).obj M) ≫
        ((derivedTensor A T).obj (L((f)^*[A]).obj (L((g)^*[A]).obj K))).map
          ((leftDerivedUpperStarComp A f g).hom.app M) := by
  have hh := derived_tensor_compositor
    (upperStar A g) (upperStar A f)
    (upperStar A (f ≫ g))
    (upperStarComp A f g)
    (leftDerivedUpperStarComp A f g) rfl
    (leftDerivedUpperStarTensorComparison A g)
    (leftDerivedUpperStarTensorComparison A f)
    (leftDerivedUpperStarTensorComparison A (f ≫ g))
    (leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison _ g)
    (leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison _ f)
    (leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison _ (f ≫ g)) K M
  simpa only [leftDerivedUpperStarTensorIso_hom, derivedTensor, Functor.comp_obj,
    MonoidalCategory.curriedTensor_obj_obj, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc] using hh.symm

end AlgebraicGeometry.ProEtale
