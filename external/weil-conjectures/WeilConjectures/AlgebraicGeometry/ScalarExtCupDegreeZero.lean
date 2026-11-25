/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison

/-! # ScalarExtCupDegreeZero

Source: Stacks Project, Cohomology, Tag 0FKU.
(blueprint: lem-sc-scalar-ext-cup-degree-zero).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X : Scheme.{u}}
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private theorem ext_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D] [EnoughInjectives C]
    (L R : C ⥤ D) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (α : L ⟶ R) {A B : C} {n : ℕ} (x : Abelian.Ext.{u + 1} A B n) :
    (x.mapExactFunctor L).comp (Abelian.Ext.mk₀ (α.app B)) (add_zero n) =
      (Abelian.Ext.mk₀ (α.app A)).comp (x.mapExactFunctor R) (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective A B).2 x
    simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg Abelian.Ext.mk₀ (α.naturality g)
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι B) (cokernel.π (Injective.ι B))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ A hS x
      (Abelian.Ext.eq_zero_of_injective _) rfl
    let φ : S.map L ⟶ S.map R :=
      { τ₁ := α.app S.X₁
        τ₂ := α.app S.X₂
        τ₃ := α.app S.X₃
        comm₁₂ := (α.naturality S.f).symm
        comm₂₃ := (α.naturality S.g).symm }
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass,
      Abelian.Ext.comp_assoc_of_third_deg_zero]
    rw [(hS.map_of_exact L).extClass_naturality (hS.map_of_exact R) φ]
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, ih]
    rw [Abelian.Ext.comp_assoc, ← Abelian.Ext.mapExactFunctor_extClass,
      ← Abelian.Ext.mapExactFunctor_comp]
    omega

private theorem ext_iso_transport {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] (T : C ⥤ C) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (e : T ≅ 𝟭 C)
    {A B : C} {n : ℕ} (a : Abelian.Ext.{u + 1} A B n) :
    a.mapExactFunctor T = (Abelian.Ext.mk₀ (e.hom.app A)).comp
      (a.comp (Abelian.Ext.mk₀ (e.inv.app B)) (add_zero n)) (zero_add n) := by
  have h := congrArg (fun z : Abelian.Ext.{u + 1} (T.obj A) B n ↦
    z.comp (Abelian.Ext.mk₀ (e.inv.app B)) (add_zero n))
      (Abelian.Ext.exactFunctorIdentityComparison T e a)
  simpa only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app, Abelian.Ext.comp_mk₀_id] using h

/-- Tensoring a degree-one scalar Ext class with a degree-zero morphism is coefficient composition.
Source: Stacks Project, Cohomology, Tag 0FKU, Lemma 20.31.1 and Remark 20.31.2.
(blueprint: lem-sc-scalar-ext-cup-degree-zero).

Proof: Expand scalarExtCup. Exact-functor transport sends mk₀ of a morphism
u to mk₀ of its tensor whiskering. For the right formula the product is
precomposition by the inverse unit unitor, tensorRight-unit transport of a,
and postcomposition by B whiskered with u. Naturality on Ext of the right
unitor identifies the first two factors with a postcomposed by the inverse
right unitor of B; the left and right unitors agree at the tensor unit.
Associativity gives the first formula. For the left formula the first
transport is mk₀ of u whiskered with the unit. Move this whiskering past the
transport of a using naturality on Ext of the transformation tensorLeft-unit
to tensorLeft-A induced by u. The remaining tensorLeft-unit transport is
identified with a by naturality of the left unitor. Associativity and
naturality of the unitors give the displayed coefficient morphism. These
are exact-functor identities in Ext, so they require no geometric assumptions.
The degree-zero factor introduces no sign. The formula holds with zero u or with the zero sheaf.
The naturality argument used below applies in every degree. -/
theorem scalarExtCup_mk₀ {A B : KSheaf X k}
    (a : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) B 1)
    (v : 𝟙_ (KSheaf X k) ⟶ A) :
    scalarExtCup a (Abelian.Ext.mk₀ v) =
      a.comp (Abelian.Ext.mk₀ ((ρ_ B).inv ≫ (B ◁ v))) rfl ∧
    scalarExtCup (Abelian.Ext.mk₀ v) a =
      a.comp (Abelian.Ext.mk₀ ((λ_ B).inv ≫ (v ▷ B)))
        (by omega : 1 + 0 = 0 + 1) := by
  have : EnoughInjectives (KSheaf X k) := inferInstance
  constructor
  · unfold scalarExtCup
    rw [Abelian.Ext.mapExactFunctor_mk₀]
    rw [ext_iso_transport (tensorRight (𝟙_ (KSheaf X k)))
      (rightUnitorNatIso (KSheaf X k)) a]
    simp only [rightUnitorNatIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app, curriedTensor_obj_map]
    simp only [← Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀]
    have hunit : (λ_ (𝟙_ (KSheaf X k))).inv ≫
        (ρ_ (𝟙_ (KSheaf X k))).hom = 𝟙 _ := by
      rw [← unitors_equal]
      simp
    rw [hunit, Abelian.Ext.mk₀_id_comp]
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  · unfold scalarExtCup
    rw [Abelian.Ext.mapExactFunctor_mk₀]
    change ((Abelian.Ext.mk₀ (λ_ (𝟙_ (KSheaf X k))).inv).comp
      (Abelian.Ext.mk₀ (v ▷ (𝟙_ (KSheaf X k)))) (zero_add 0)).comp
      (a.mapExactFunctor (tensorLeft A)) rfl = _
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
    have hn := ext_naturality (tensorLeft (𝟙_ (KSheaf X k))) (tensorLeft A)
      ((tensoringLeft (KSheaf X k)).map v) a
    change (a.mapExactFunctor (tensorLeft (𝟙_ (KSheaf X k)))).comp
        (Abelian.Ext.mk₀ (v ▷ B)) (add_zero 1) =
      (Abelian.Ext.mk₀ (v ▷ (𝟙_ (KSheaf X k)))).comp
        (a.mapExactFunctor (tensorLeft A)) (zero_add 1) at hn
    rw [← hn]
    rw [ext_iso_transport (tensorLeft (𝟙_ (KSheaf X k)))
      (leftUnitorNatIso (KSheaf X k)) a]
    simp only [leftUnitorNatIso, NatIso.ofComponents_hom_app,
      NatIso.ofComponents_inv_app]
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, Iso.inv_hom_id]
    rw [Abelian.Ext.mk₀_id_comp]
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

end
end AlgebraicGeometry.Scheme.Modules
