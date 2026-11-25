/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.UnitProjection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The projection map of extension and restriction of scalars

For an `R`-algebra `S`, the unit projection map `K ⊗_R S ⟶ S ⊗_R K` of the monoidal adjunction
between extension and restriction of scalars
(`CategoryTheory.Adjunction.unitProjection`) is the isomorphism
`ModuleCat.tensorEquivRestrictScalarsExtendScalars` sending `k ⊗ s` to `s ⊗ k`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The `R`-module `S` underlying the unit `S`-module is the `R`-module `S` of the algebra
structure. -/
noncomputable def restrictScalarsObjUnitIso :
    (restrictScalars (algebraMap R S)).obj (𝟙_ (ModuleCat.{u} S)) ≅ ModuleCat.of R S :=
  LinearEquiv.toModuleIso (X₁ := (restrictScalars (algebraMap R S)).obj (𝟙_ (ModuleCat.{u} S)))
    (X₂ := S)
    { toFun s := s
      invFun s := s
      map_add' _ _ := rfl
      map_smul' r s := (Algebra.smul_def r (id s : S)).symm
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The unit projection map `K ⊗_R S ⟶ S ⊗_R K` of extension and restriction of scalars is the
inverse of `ModuleCat.extendScalarsCompRestrictScalarsIso'`, sending `k ⊗ s` to `s ⊗ k`. -/
lemma extendRestrictScalarsAdj_unitProjection (K : ModuleCat.{u} R) :
    (extendRestrictScalarsAdj (algebraMap R S)).unitProjection K =
      (K ◁ (restrictScalarsObjUnitIso R S).hom) ≫
        (extendScalarsCompRestrictScalarsIso' R S).inv.app K := by
  refine MonoidalCategory.tensor_ext (fun k s ↦ ?_)
  refine (?_ : _ = (TensorProduct.tmul R ((1 : S) * @id S s * (1 * 1)) k :
    (extendScalars (algebraMap R S)).obj K)).trans ?_
  · rfl
  · rw [one_mul, one_mul, mul_one]
    rfl

/-- The unit projection map `K ⊗_R S ⟶ S ⊗_R K` of extension and restriction of scalars is an
isomorphism. -/
instance isIso_extendRestrictScalarsAdj_unitProjection (K : ModuleCat.{u} R) :
    IsIso ((extendRestrictScalarsAdj (algebraMap R S)).unitProjection K) := by
  rw [extendRestrictScalarsAdj_unitProjection]
  infer_instance

end ModuleCat
