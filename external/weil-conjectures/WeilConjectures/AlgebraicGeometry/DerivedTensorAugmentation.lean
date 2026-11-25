/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal

/-! # Derived tensor augmentations on schemes

Source: Stacks Project, Cohomology on Sites, Tags 06YS and 06YU; Derived Categories
of Schemes, Tag 08EH (blueprint: def-sc-derived-tensor-augmentation).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 512 in
/-- The morphism `β : B ⟶ A` is `id_A ⊗ᴸ u`, followed by the right unitor, for some
`u : I ⟶ 𝒪_X`, and `B` is `A ⊗ᴸ I`. We express this using K-flat representatives
`P` of `A` and `J` of `I`, a chain augmentation `J ⟶ 𝒪_X[0]`, and the canonical
right unitor of total tensor. The isomorphisms merely transport these models to
`A`, `I`, and `B`. Every derived augmentation admits such a K-flat roof, so the
existential model imposes no condition beyond the stated derived tensor description.
Source: Stacks Project, Tags 06YS, 06YU and 08EH
(blueprint: def-sc-derived-tensor-augmentation). -/
def IsDerivedTensorAugmentation (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A I B : schemeDerivedCategory X) (β : B ⟶ A) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := (SheafOfModules.tensorClosed X.sheaf).1.some
  ∃ P J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    CochainComplex.IsKFlatTensor (R := X.sheaf) P ∧
    CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧
    ∃ (eA : DerivedCategory.Q.obj P ≅ A) (_eI : DerivedCategory.Q.obj J ≅ I)
      (eB : DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _)) ≅ B)
      (u : J ⟶ HomologicalComplex.tensorUnit
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)),
      β = eB.inv ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom

end AlgebraicGeometry.Scheme
