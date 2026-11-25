/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Natural tensor comparison with a fixed K-flat model
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-kflat-tensor-model-natural-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

-- The natural comparison specializes the unbounded total-tensor bifunctor.
/-- The localization comparison is a natural isomorphism for a fixed K-flat
first complex and arbitrary second complexes.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-kflat-tensor-model-natural-comparison).

Proof: apply the K-flat bifunctor comparison to the constant singleton family
with value P and the identity family of all cochain complexes. The K-flatness
hypothesis on the first family is precisely hP. Evaluation at the singleton
object gives the displayed natural isomorphism. Its components are the
localization tensor maps, and their naturality is inherited from the bifunctor
comparison. No K-flatness or boundedness of the second complex is used;
the zero complexes and the empty scheme cause no exceptions. -/
theorem kFlat_tensorModel_naturalComparison (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    Nonempty
      (DerivedCategory.Q ⋙ (curriedTensor (schemeDerivedCategory X)).obj
        (DerivedCategory.Q.obj P) ≅
        ((curriedTensor
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace))).map₂CochainComplex.obj P) ⋙
            DerivedCategory.Q) := by
  classical
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso.{uX, wD} X
    ((Functor.const (Discrete PUnit.{1})).obj P) (𝟭 (CochainComplex C ℤ)) (fun _ ↦ hP)
  exact ⟨e.app ⟨PUnit.unit⟩⟩

end AlgebraicGeometry.Scheme
