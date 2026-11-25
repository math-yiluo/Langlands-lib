/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily

/-!
# Integer tensor powers under monoidal functors

Let `F : C ⥤ D` be a strong monoidal functor, `L ∈ C` with a tensor inverse `e` and `L' ∈ D` with
a tensor inverse `e'`. An isomorphism `F L ≅ L'` induces isomorphisms
`F(L^{⊗ m}) ≅ L'^{⊗ m}` for all `m ∈ ℤ`
(`CategoryTheory.MonoidalCategory.TensorInverse.zpowMapIso`): for `m ≥ 0` through the monoidal
structure of `F`, and for `m < 0` through the uniqueness of tensor inverses
(`CategoryTheory.MonoidalCategory.TensorInverse.objIso`), `F` sending the tensor inverse `e` of
`L` to a tensor inverse of `F L` (`CategoryTheory.MonoidalCategory.TensorInverse.map`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory.TensorInverse

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Tensor inverses are unique up to isomorphism:
`M ≅ M ⊗ 𝟙 ≅ M ⊗ (L ⊗ M') ≅ (M ⊗ L) ⊗ M' ≅ 𝟙 ⊗ M' ≅ M'`. -/
noncomputable def objIso {L : C} (e e' : TensorInverse L) : e.obj ≅ e'.obj :=
  (ρ_ e.obj).symm ≪≫ whiskerLeftIso e.obj e'.rightIso.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso e.leftIso e'.obj ≪≫ λ_ e'.obj

/-- A tensor inverse of `L` is a tensor inverse of every object isomorphic to `L`. -/
noncomputable def ofIso {L L' : C} (e : TensorInverse L) (h : L ≅ L') : TensorInverse L' where
  obj := e.obj
  rightIso := whiskerRightIso h.symm e.obj ≪≫ e.rightIso
  leftIso := whiskerLeftIso e.obj h.symm ≪≫ e.leftIso

/-- A strong monoidal functor sends a tensor inverse `M` of `L` to the tensor inverse `F M` of
`F L`. -/
noncomputable def map {L : C} (e : TensorInverse L) (F : C ⥤ D) [F.Monoidal] :
    TensorInverse (F.obj L) where
  obj := F.obj e.obj
  rightIso := Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso e.rightIso ≪≫ (Functor.Monoidal.εIso F).symm
  leftIso := Functor.Monoidal.μIso F _ _ ≪≫ F.mapIso e.leftIso ≪≫ (Functor.Monoidal.εIso F).symm

/-- A monoidal functor sending `L` to `L'` sends the tensor powers of `L` to those of `L'`. -/
noncomputable def tensorPowNatMapIso (F : C ⥤ D) [F.Monoidal] {L : C} {L' : D}
    (h : F.obj L ≅ L') : (n : ℕ) → F.obj (tensorPowNat L n) ≅ tensorPowNat L' n
  | 0 => (Functor.Monoidal.εIso F).symm
  | n + 1 => (Functor.Monoidal.μIso F _ _).symm ≪≫ tensorIso h (tensorPowNatMapIso F h n)

/-- A monoidal functor `F` with `F L ≅ L'` sends the integer tensor powers of `L` to those of
`L'`, for any choice of tensor inverses `e` of `L` and `e'` of `L'`. -/
noncomputable def zpowMapIso {L : C} {L' : D} (e : TensorInverse L) (e' : TensorInverse L')
    (F : C ⥤ D) [F.Monoidal] (h : F.obj L ≅ L') : (m : ℤ) → F.obj (e.zpow m) ≅ e'.zpow m
  | .ofNat n => tensorPowNatMapIso F h n
  | .negSucc n => tensorPowNatMapIso F (((e.map F).ofIso h).objIso e') (n + 1)

end CategoryTheory.MonoidalCategory.TensorInverse
