/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Scalar balance of external cup products

Source: Stacks Project, Varieties, Tag 0BED; Cohomology, Tag 01F7.
(blueprint: lem-sc-external-cup-scalar-balance).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

local instance (A : Scheme.{u}) : MonoidalCategory (KSheaf A k) :=
  Sheaf.monoidalCategory _ _
local instance (A : Scheme.{u}) : HasExt.{u + 1} (KSheaf A k) :=
  HasExt.standard (KSheaf A k)

private theorem ext_map_comp_smul
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [Linear k C] [Linear k D] [HasExt C] [HasExt D]
    (T : C ⥤ D) [T.Additive] [T.Linear k]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {A B : C} {A' B' : D} {n : ℕ}
    (α : Abelian.Ext A' (T.obj A) 0) (β : Abelian.Ext (T.obj B) B' 0)
    (x : Abelian.Ext A B n) (r : k) :
    (α.comp ((r • x).mapExactFunctor T) (zero_add n)).comp β (add_zero n) =
      r • (α.comp (x.mapExactFunctor T) (zero_add n)).comp β (add_zero n) := by
  rw [Functor.mapExactFunctor_smul, Abelian.Ext.comp_smul, Abelian.Ext.smul_comp]

private theorem ext_tensor_balance
    {C : Type*} [Category C] [Abelian C] [Linear k C] [HasExt C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    {A B : C} {p q : ℕ}
    [PreservesFiniteLimits (tensorRight (𝟙_ C))]
    [PreservesFiniteColimits (tensorRight (𝟙_ C))]
    [PreservesFiniteLimits (tensorLeft A)] [PreservesFiniteColimits (tensorLeft A)]
    (a : Abelian.Ext (𝟙_ C) A p) (b : Abelian.Ext (𝟙_ C) B q) (r : k) :
    ((Abelian.Ext.mk₀ (λ_ (𝟙_ C)).inv).comp
      (a.mapExactFunctor (tensorRight (𝟙_ C))) (zero_add p)).comp
        ((r • b).mapExactFunctor (tensorLeft A)) rfl =
      ((Abelian.Ext.mk₀ (λ_ (𝟙_ C)).inv).comp
        ((r • a).mapExactFunctor (tensorRight (𝟙_ C))) (zero_add p)).comp
          (b.mapExactFunctor (tensorLeft A)) rfl := by
  simp only [Functor.mapExactFunctor_smul, Abelian.Ext.comp_smul, Abelian.Ext.smul_comp]

private theorem cohomologyExt_smul (f : X ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (n : ℕ) (r : k) (a : scalarCohomology f F n) :
    scalarCohomologyExtEquiv f F n (r • a) = r • scalarCohomologyExtEquiv f F n a := by
  unfold scalarCohomologyExtEquiv
  exact scalarCohomologyExtMap_smul f F n r a

private theorem inverseImage_linear (a : Y ⟶ X) :
    (scalarInverseImage (k := k) a).Linear k := by
  let : ((Opens.map a.base).sheafPushforwardContinuous (ModuleCat.{u} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).Linear k :=
    ⟨by intros; rfl⟩
  let : (scalarInverseImage (k := k) a).Linear k :=
    ((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).left_adjoint_linear
  infer_instance

private theorem pullback_smul (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (a : Y ⟶ X) (h : a ≫ f = g)
    (F : X.Modules) (n : ℕ) (r : k) (x : scalarCohomology f F n) :
    scalarCohomologyPullback f g a h F n (r • x) =
      r • scalarCohomologyPullback f g a h F n x := by
  let := inverseImage_linear (k := k) a
  apply (scalarCohomologyExtEquiv g _ n).injective
  rw [cohomologyExt_smul]
  unfold scalarCohomologyPullback
  simp only [AddEquiv.apply_symm_apply, cohomologyExt_smul]
  exact ext_map_comp_smul _ _ _ _ r

private theorem cup_balance (f : X ⟶ Spec (CommRingCat.of k))
    (F G : X.Modules) (p q : ℕ) (r : k)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a (r • b) =
      scalarCohomologyCup f F G p q (r • a) b := by
  apply (scalarCohomologyExtEquiv f _ (p + q)).injective
  unfold scalarCohomologyCup
  simp only [AddEquiv.apply_symm_apply, cohomologyExt_smul]
  unfold scalarExtCup
  exact congrArg (fun x ↦ x.comp
    (Abelian.Ext.mk₀ (scalarTensorCoefficient f F G)) (add_zero (p + q)))
      (ext_tensor_balance _ _ r)

/-- A scalar may be moved between the two arguments of an external cup product.
Source: Stacks Project, Varieties, Tag 0BED; Cohomology, Tag 01F7.
(blueprint: lem-sc-external-cup-scalar-balance).

Proof: The cohomology-to-Ext comparison is k-linear. Inverse image is k-linear because
its right adjoint is sectionwise precomposition, hence linear. Exact-functor transport
on Ext and Yoneda composition commute with scalars, so both projection pullbacks are
linear. Tensoring sheaves of k-vector spaces is linear in morphisms. The displayed
Yoneda formula for the cup product is thus linear in each input; either scalar gives
scalar multiplication on the same composite. Apply injectivity of the Ext comparison
to transport this equality back, then substitute the two projection pullbacks. -/
theorem external_cup_scalar_balance (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (G : Y.Modules)
    (p q : ℕ) (r : k) (a : scalarCohomology f F p) (b : scalarCohomology g G q) :
    externalCup f g F G p q a (r • b) = externalCup f g F G p q (r • a) b := by
  unfold externalCup
  rw [pullback_smul, pullback_smul]
  exact cup_balance _ _ _ p q r _ _

end
end AlgebraicGeometry.Scheme.Modules
