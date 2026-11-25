/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.KFlat

/-! # Natural computation of derived tensor on K-flat first models

Source: Stacks Project, Tag 06YH, construction of the derived tensor product.
(blueprint: lem-pc-kflat-derived-tensor-comparison).
-/

@[expose] public section

universe u w vI uI vJ uJ

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance comparisonTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The derived tensor counit is a natural isomorphism on any family of K-flat first
models and any family of second models. Source: Stacks Project, Tag 06YH.
(blueprint: lem-pc-kflat-derived-tensor-comparison).

Proof: equip sheaves of modules with the recorded symmetric, closed, additive tensor
structure and functorial flat resolutions. For a K-flat complex P, the defining
acyclicity criterion implies the categorical K-flat criterion in the homotopy
category: right tensor preserves acyclic objects, and the braiding gives the left
criterion. Thus the derived tensor counit Qh(P) tensor Qh(N) to Qh(P tensor N) is
invertible for every N, by the K-flat left derivability structure. Precompose that
counit by F and G followed by the homotopy quotient. Transport along the natural
quotientCompQhIso to obtain the displayed comparison for Q. The quotient tensor
comparison identifies the right side with Q of the total tensor complex. The counit
and the quotient comparisons are natural, so the componentwise invertibility gives
an isomorphism of the curried bifunctors. -/
theorem kFlat_derivedTensor_comparison_natIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : I ⥤ CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (G : J ⥤ CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ P, CochainComplex.IsKFlatTensor (R := X.sheaf) (F.obj P)) :
    Nonempty
      (F ⋙ DerivedCategory.Q ⋙ curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringLeft J (schemeDerivedCategory X)
          (schemeDerivedCategory X)).obj (G ⋙ DerivedCategory.Q) ≅
        F ⋙ (curriedTensor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace))).map₂CochainComplex ⋙
          (Functor.whiskeringLeft J
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)).obj G ⋙
          (Functor.whiskeringRight J
            (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
            (schemeDerivedCategory X)).obj DerivedCategory.Q) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} C :=
    Limits.hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have hk (i : I) : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj (F.obj i)) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have h := hF i N hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj (F.obj i)) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso
      (β_ _ _) hright, hright⟩
  have hμ (i : I) (j : J) :
      IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := C)) (F.obj i) (G.obj j)) := by
    have hq := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
      (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C (.up ℤ)).obj (F.obj i))
      ((HomotopyCategory.quotient C (.up ℤ)).obj (G.obj j)) (hk i)
    have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
        ((HomotopyCategory.quotient C (.up ℤ)).obj (F.obj i))
        ((HomotopyCategory.quotient C (.up ℤ)).obj (G.obj j))) := hq
    change IsIso (_ ≫ _ ≫ _)
    change IsIso (_ ≫ (_ ≫ _) ≫ _)
    infer_instance
  have (i : I) (j : J) := hμ i j
  refine ⟨NatIso.ofComponents (fun i ↦ NatIso.ofComponents
    (fun j ↦ asIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      (F.obj i) (G.obj j))) ?_) ?_⟩
  · intro j j' f
    exact Functor.LaxMonoidal.μ_natural_right DerivedCategory.Q (F.obj _) (G.map f)
  · intro i i' f
    ext j
    exact Functor.LaxMonoidal.μ_natural_left DerivedCategory.Q (F.map f) (G.obj j)

end AlgebraicGeometry
