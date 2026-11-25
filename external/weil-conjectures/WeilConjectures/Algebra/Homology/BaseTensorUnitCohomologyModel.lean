/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizationModelSemilinear
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.MixedTotalTensorScalarExtension
import WeilConjectures.Algebra.Homology.BalancedTensorUnitModelComparison

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology
variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Compute the coefficient-unit map using a balanced complex, before any localization.
Source: Stacks Project, Tags 064L and 06Y6, balanced computation of derived tensor.
(blueprint: new-lem-pc-base-tensor-unit-cohomology-model).

Proof: take a K-flat R-resolution F of the complex B concentrated in degree zero,
and put C = Tot(Q tensor_R F), with its termwise A-action. Tensor associativity
identifies Aq tensor_A C with Tot((Aq tensor_A Q) tensor_R F), and identifies the
extension unit with the map induced by Q -> Aq tensor_A Q. This does not require
Aq to be flat. The balanced derived tensor computation identifies their
cohomology with the two universal derived-functor models. The universal counits
fix these identifications, so their naturality identifies the map with
localizationModelMap. Multiplication by a on Q induces multiplication by a on C;
cohomologyIso_smul therefore makes the first identification A-linear. The same
argument on Aq tensor_A Q makes the second identification A-linear after
restriction along A -> Aq -> Aq tensor_R B. Forgetting the B-action gives the
displayed A-module isomorphisms and the commuting equation. No assertion about
the kernel or exactness of scalar extension is used here. -/
theorem exists_baseTensorUnitCohomologyModel (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) :
    ∃ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeft (S := R) : A →ₐ[R] A ⊗[R] B).toRingHom).obj
          (L.cohomology i) ≅ C.homology i)
      (e' : (ModuleCat.restrictScalars
        ((Algebra.TensorProduct.includeLeft (S := R) : Aq →ₐ[R] Aq ⊗[R] B).toRingHom.comp
          (algebraMap A Aq))).obj (K.cohomology i) ≅
          ((restrict A Aq).obj ((extend A Aq).obj C)).homology i),
      ∀ x : L.cohomology i,
        e'.hom (localizationModelMap R A Aq B D i Q L K uQ x) =
          (HomologicalComplex.homologyMap
            (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
              (.up ℤ)).unit.app C) i) (e.hom x) := by
  classical
  let E := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R B)
  let Λ := flatResolution R
  let F := Λ.resolutionFunctor.obj E
  let f := Λ.resolutionNatTrans.app E
  have hf : QuasiIso f := inferInstance
  have hF := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le E
  obtain ⟨θ, hθ⟩ := exists_mixedTotalTensor_scalarExtension R A Aq Q F
  obtain ⟨e, eq, he⟩ :=
    exists_balancedTensorUnitModelComparison R A Aq B D i Q L K uQ huQ F f hf hF θ hθ
  let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) i
  let t := H.mapIso ((restrict A Aq).mapIso θ)
  refine ⟨C, e, eq ≪≫ t.symm, ?_⟩
  intro x
  have hx := he x
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  change t.inv (eq.hom (localizationModelMap R A Aq B D i Q L K uQ x)) = _
  rw [hx, HomologicalComplex.homologyMap_comp]
  change t.inv (t.hom
    ((HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
        (.up ℤ)).unit.app C) i) (e.hom x))) = _
  exact congrArg (fun k ↦ k
    ((HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
        (.up ℤ)).unit.app C) i) (e.hom x))) t.hom_inv_id

end RingTensorCohomology
