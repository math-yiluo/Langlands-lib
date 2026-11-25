/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.AlgebraicGeometry.MixedRepForward.FiniteCoefficientInstances
import WeilConjectures.AlgebraicGeometry.MixedRepForward.ForwardTransportGeneral
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeInverse

/-!
# The mixed representative equation for general coefficients

This is the coefficient-generic form of clause (3) of
`AlgebraicGeometry.ProEtale.finiteOpenMixedTensorRepresentative`, normalized as in
`SheafOfModules.OpenTensorNormalization.mixed_representation_normalized`.

## Implementation details

Stating it for an abstract coefficient category keeps elaboration and kernel checking cheap;
the finite coefficient statements are obtained by instantiation.
-/

@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.MixedRepForward
open AlgebraicGeometry Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

omit [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A] in
private theorem cochain_tensor_obj_general
    (P Q : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    P ⊗ Q = HomologicalComplex.mapBifunctor P Q
      (curriedTensor (Sheaf (ProEt.topology X) A)) (.up ℤ) := rfl

/-- The mixed inverse representative square for general coefficients: clause (3) of
`finiteOpenMixedTensorRepresentative`. -/
theorem mixed_inverse_transport_general
    (P Q : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    (((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.inv.app
        ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj P)) ⊗ₘ 𝟙 _) ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso A j).inv.app
        ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj P)).app
        ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj Q) ≫
      (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (((-⊗ᴸ-(X)[A]).obj
          ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj P)).obj
          ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj Q)) ≫
      (j)^*[A].mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)) P Q) ≫
      (j)^*[A].mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q
          (curriedTensor (Sheaf (ProEt.topology X) A)) (.up ℤ)) =
      ((j)^*[A].mapDerivedCategoryFactors.hom.app P ⊗ₘ
        ((j)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)).obj Q) ≫
          (j)^*[A].mapDerivedCategoryFactors.hom.app Q)) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := Sheaf (ProEt.topology U) A))
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
        (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      inv ((DerivedCategory.Q (C := Sheaf (ProEt.topology U) A)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (j)^*[A]).app P).app Q)) := by
  have hf := forward_transport_general A j P Q
  apply CategoryTheory.mixedTensor_inverse_transport
    L((j)^*[A]) (j)^*[A].mapDerivedCategory
    (j)^*[A].leftDerivedFunctorIsoMapDerivedCategory
    (((leftDerivedUpperStarTensorNatIso A j).app
      (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q))
    (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)) P Q)
    ((j)^*[A].mapDerivedCategoryFactors.hom.app P)
    ((j)^*[A].mapDerivedCategoryFactors.hom.app Q)
    ((j)^*[A].mapDerivedCategoryFactors.hom.app
      (HomologicalComplex.mapBifunctor P Q (curriedTensor (Sheaf (ProEt.topology X) A)) (.up ℤ)))
    (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (ProEt.topology U) A))
      (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj P)
      (((j)^*[A].mapHomologicalComplex (.up ℤ)).obj Q))
    (asIso ((DerivedCategory.Q (C := Sheaf (ProEt.topology U) A)).map
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
        (j)^*[A]).app P).app Q)))
  simpa only [derivedTensor,
    leftDerivedUpperStarDerivedTensor, Functor.postcompose₂_obj_obj_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj, cochain_tensor_obj_general,
    Category.assoc, Iso.app_hom, asIso_hom] using hf

/-- The normalized mixed representative equation for general coefficients, stated with
`mapDerivedCategoryUpperStarDerivedTensorIso`. -/
theorem mixed_representation_general
    (P Q : CochainComplex (Sheaf (ProEt.topology X) A) ℤ) :
    let F := (j)^*[A]
    let a := F.mapDerivedCategoryFactors.hom
    let muX := Functor.LaxMonoidal.μ
      (DerivedCategory.Q (C := Sheaf (ProEt.topology X) A)) P Q
    let fc := F.mapHomologicalComplex (.up ℤ)
    let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Sheaf (ProEt.topology U) A))
      (fc.obj P) (fc.obj Q)
    let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app
      (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)
    let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj Q) ≫ a.app Q)
    delta ≫ F.mapDerivedCategory.map muX ≫ a.app (HomologicalComplex.mapBifunctor P Q
      (curriedTensor (Sheaf (ProEt.topology X) A)) (.up ℤ)) =
      n ≫ muU ≫ DerivedCategory.Q.map (inv c) := by
  dsimp only
  let F := (j)^*[A]
  let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app
    (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)
  have hdelta : delta =
      ((ProEtale.derivedTensor A U).map
        ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app
          (DerivedCategory.Q.obj P))).app
          (F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) ≫
      ((ProEtale.leftDerivedUpperStarTensorNatIso A j).inv.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app
        (((ProEtale.derivedTensor A X).obj
          (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) := by
    rfl
  have hdelta' : delta =
      (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Q.obj P) ⊗ₘ
        𝟙 (F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q))) ≫
      ((ProEtale.leftDerivedUpperStarTensorNatIso A j).inv.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) := by
    rw [hdelta]
    simp only [ProEtale.leftDerivedUpperStarIsoMapDerivedCategory,
      ProEtale.derivedTensor, curriedTensor_map_app, tensorHom_id]
    rfl
  change delta ≫ _ = _
  rw [hdelta', Functor.map_inv]
  simp only [Category.assoc]
  exact mixed_inverse_transport_general A j P Q

end AlgebraicGeometry.ProEtale.MixedRepForward
