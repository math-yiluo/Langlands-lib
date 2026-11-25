/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTestComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleTensor
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTotalization
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Acyclic tensor tests for étale sum extension

Source: Stacks Project, More on Étale Cohomology, Tag 0GKF, and the unbounded
totalization expansion of lem-pur-etale-sum-tensor-totalization.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

private def tensorComparisonCurried {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (E : C ⥤ D)
    (e : E.prod E ⋙ tensor D ≅ tensor C ⋙ E) :
    (Functor.postcompose₂.obj E).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ D).obj E).obj E).obj (curriedTensor D) := by
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ (e.app (M, N)).symm) ?_) ?_
  · intro N N' g
    simpa using e.inv.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, g)
  · intro M M' f
    ext N
    simpa using e.inv.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N)

private theorem tensorTestTotalRealization (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A]
    (P Q : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    Nonempty (etaleSumTensorTestTotal T A
      ((etaleSumTensorTestRealizationComplex T A).obj P)
      ((etaleSumTensorTestRealizationComplex T A).obj Q) ≅
      (etaleSumTensorTestRealizationComplex T A).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _))) := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  obtain ⟨e⟩ := etaleConstantModule_tensor_comparison T A
  let E := etaleSumTensorTestRealization T A
  let := etaleSumTensorTestRealization_isEquivalence T A
  let := Functor.additive_of_preserves_binary_products E
  let τ := (tensorComparisonCurried E e).hom
  let : IsIso τ := by dsimp only [τ]; infer_instance
  let c := HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q
  exact ⟨(asIso c).symm⟩

end AlgebraicGeometry.Scheme
