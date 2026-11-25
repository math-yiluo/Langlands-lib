/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import WeilConjectures.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # ScalarCupCoefficientNaturality

Source: Stacks Project, Cohomology, Tags 01F7, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private local instance (X : Scheme.{w}) (k : Type w) [Field k] :
    MonoidalCategory (KSheaf X k) := Sheaf.monoidalCategory _ _
private local instance (X : Scheme.{w}) (k : Type w) [Field k] :
    HasExt.{w + 1} (KSheaf X k) := HasExt.standard (KSheaf X k)

private local instance (X : Scheme.{w}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf

private local instance (X : Scheme.{w}) (k : Type w) [Field k] :
    EnoughInjectives (KSheaf X k) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ext_map_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt C] [HasExt D] [EnoughInjectives C]
    (T T' : C ⥤ D) [T.Additive] [T'.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits T]
    [CategoryTheory.Limits.PreservesFiniteColimits T]
    [CategoryTheory.Limits.PreservesFiniteLimits T']
    [CategoryTheory.Limits.PreservesFiniteColimits T']
    (η : T ⟶ T') {A B : C} {n : ℕ} (b : Abelian.Ext A B n) :
    (b.mapExactFunctor T).comp (Abelian.Ext.mk₀ (η.app B)) (add_zero n) =
      (Abelian.Ext.mk₀ (η.app A)).comp (b.mapExactFunctor T') (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨β, rfl⟩ := (Abelian.Ext.mk₀_bijective A B).2 b
    simp only [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    exact congrArg Abelian.Ext.mk₀ (η.naturality β)
  | succ n ih =>
    let I : InjectivePresentation B := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (CategoryTheory.Limits.cokernel.π I.f)
      (CategoryTheory.Limits.cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ A hS b
      (Abelian.Ext.eq_zero_of_injective (I := I.J) _) rfl
    change y.comp hS.extClass rfl = b at hy
    rw [← hy, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_extClass, Abelian.Ext.mapExactFunctor_extClass]
    let τ : S.map T ⟶ S.map T' :=
      { τ₁ := η.app S.X₁
        τ₂ := η.app S.X₂
        τ₃ := η.app S.X₃
        comm₁₂ := (η.naturality S.f).symm
        comm₂₃ := (η.naturality S.g).symm }
    have hδ := (hS.map_of_exact T).extClass_naturality (hS.map_of_exact T') τ
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, hδ,
      ← Abelian.Ext.comp_assoc_of_second_deg_zero, ih]
    exact Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem extCup_naturality
    (k : Type w) [Field k] (X : Scheme.{w})
    {A B A' B' : KSheaf X k} (α : A ⟶ A') (β : B ⟶ B') (p q : ℕ)
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A p)
    (b : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B q) :
    (scalarExtCup a b).comp (Abelian.Ext.mk₀ (α ⊗ₘ β)) (add_zero (p + q)) =
      scalarExtCup (a.comp (Abelian.Ext.mk₀ α) (add_zero p))
        (b.comp (Abelian.Ext.mk₀ β) (add_zero q)) := by
  have hn := ext_map_naturality (tensorLeft A) (tensorLeft A')
    ((curriedTensor (KSheaf X k)).map α) b
  change (b.mapExactFunctor (tensorLeft A)).comp (Abelian.Ext.mk₀ (α ▷ B))
    (add_zero q) = (Abelian.Ext.mk₀ (α ▷ (𝟙_ (KSheaf X k)))).comp
      (b.mapExactFunctor (tensorLeft A')) (zero_add q) at hn
  unfold scalarExtCup
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  rw [tensorHom_def, ← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [hn]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorCoefficient_naturality
    (k : Type w) [Field k] (X : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (F G F' G' : X.Modules)
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    (scalarHom f φ ⊗ₘ scalarHom f ψ) ≫ scalarTensorCoefficient f F' G' =
      scalarTensorCoefficient f F G ≫ scalarHom f (@id ((F ⊗ G) ⟶ (F' ⊗ G')) (φ ⊗ₘ ψ)) := by
  let L := presheafToSheaf (Opens.grothendieckTopology X)
    (ModuleCat.{w} k)
  let R := sheafToPresheaf (Opens.grothendieckTopology X)
    (ModuleCat.{w} k)
  let adj := CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) (ModuleCat.{w} k)
  let hs : (scalarPresheaf f F ⟶ scalarPresheaf f F') := (scalarHom f φ).hom
  let ht : (scalarPresheaf f G ⟶ scalarPresheaf f G') := (scalarHom f ψ).hom
  let e : R ⋙ L ≅ 𝟭 _ := NatIso.ofComponents (fun M ↦ asIso (adj.counit.app M))
    (fun α ↦ adj.counit.naturality α)
  have hf (M N : KSheaf X k) :
      (Sheaf.tensorLeftIso M).hom.app N =
        (e.inv.app M ⊗ₘ e.inv.app N) ≫ Functor.LaxMonoidal.μ L M.obj N.obj := by
    simp [Sheaf.tensorLeftIso, Sheaf.presheafToSheafCompTensorLeftIso,
      tensorHom_def, e, L, R, adj]
  have hi : (scalarHom f φ ⊗ₘ scalarHom f ψ) ≫
      (Sheaf.tensorLeftIso (scalarSheaf f F')).hom.app (scalarSheaf f G') =
      (Sheaf.tensorLeftIso (scalarSheaf f F)).hom.app (scalarSheaf f G) ≫
        L.map (hs ⊗ₘ ht) := by
    rw [hf, hf, ← Category.assoc, tensorHom_comp_tensorHom]
    have hφ := e.inv.naturality (scalarHom f φ)
    have hψ := e.inv.naturality (scalarHom f ψ)
    simp only [Functor.id_map, Functor.comp_map] at hφ hψ
    rw [hφ, hψ]
    rw [← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    exact congrArg (fun z ↦ (e.inv.app (scalarSheaf f F) ⊗ₘ
      e.inv.app (scalarSheaf f G)) ≫ z) (Functor.LaxMonoidal.μ_natural L hs ht)
  unfold scalarTensorCoefficient
  rw [← Category.assoc, hi, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun z ↦
    (Sheaf.tensorLeftIso (scalarSheaf f F)).hom.app (scalarSheaf f G) ≫ z)
  apply adj.homEquiv_naturality_right_square
  apply NatTrans.ext
  funext U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  change tmulSection ((φ.val.app U).hom s) ((ψ.val.app U).hom t) =
    ((φ ⊗ₘ ψ).val.app U).hom (tmulSection s t)
  exact (tensorHom_app_tmulSection φ ψ s t).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Cup products are natural in two coefficient morphisms on a fixed scheme.
Source: Stacks Project, Cohomology, Tags 07MB and 0FKV; Tag 01F7 for coefficient maps.
(blueprint: lem-sc-scalar-cup-coefficient-naturality).

Proof: Choose injective resolutions of the four coefficient modules and comparison
chain maps lifting phi and psi. Evaluation at 1 intertwines a comparison chain map
with the global-sections map, since an O-linear map sends the image of 1 to the
image of that section. Thus the moduleExtEquiv comparison intertwines the recorded
right-derived-functor coefficient map with postcomposition in Ext. Restriction to
k and precomposition by scalarUnitMorphism preserve this equality by associativity
of Yoneda composition, giving the same assertion for scalarCohomologyExtEquiv.
For the tensor coefficient, both orders send s tensor t to phi(s) tensor psi(t).
The tensor universal property and sheafification adjunction make this an equality
of sheaf morphisms. Apply this square to the tensor pairing of resolution complexes:
comparison chain maps have degree zero, so the signs of Tag 07MB agree in both
orders. Tag 0FKV identifies its augmentation with the ordinary coefficient tensor
map and the derived cup product. Equivalently, associativity and naturality of
Yoneda composition identify postcomposition of scalarExtCup with the cup of the
two postcompositions. Compose with scalarTensorCoefficient, use its square, and
transport through the injective scalarCohomologyExtEquiv. The comparison with the
recorded coefficient maps proved above gives the displayed equality. No acyclic
cover or quasi-coherence assumption is used. In degree zero this is precisely the
pure-tensor identity; if a morphism or a coefficient is zero both sides are zero.
-/
theorem scalarCup_coefficient_naturality
    (k : Type w) [Field k] (X : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (F G F' G' : X.Modules)
    (φ : F ⟶ F') (ψ : G ⟶ G') (p q : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyMap f (@id ((F ⊗ G) ⟶ (F' ⊗ G')) (φ ⊗ₘ ψ))
        (p + q) (scalarCohomologyCup f F G p q a b) =
      scalarCohomologyCup f F' G' p q
        (scalarCohomologyMap f φ p a) (scalarCohomologyMap f ψ q b) := by
  apply (scalarCohomologyExtEquiv f _ (p + q)).injective
  rw [scalarCohomologyExtEquiv_map]
  simp only [scalarCohomologyCup, AddEquiv.apply_symm_apply]
  rw [scalarCohomologyExtEquiv_map, scalarCohomologyExtEquiv_map]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    ← tensorCoefficient_naturality k X f F G F' G' φ ψ,
    ← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_third_deg_zero,
    extCup_naturality]

end
end AlgebraicGeometry.Scheme.Modules
