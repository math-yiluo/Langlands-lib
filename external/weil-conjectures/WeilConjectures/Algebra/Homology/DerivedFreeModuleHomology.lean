/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Derived maps out of a free module
Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

private theorem projective_single_to_negative_eq_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) [E.IsLE (-1)]
    (f : (DerivedCategory.singleFunctor C 0).obj P ⟶ E) : f = 0 := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E (-1)
  let := hK
  have h : f ≫ e.hom = 0 :=
    DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (f ≫ e.hom) (-1) (by omega)
  simpa using (cancel_mono e.hom).1 (by simpa using h)

set_option backward.isDefEq.respectTransparency false in
private theorem projective_single_homology_bijective
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C) [Projective P] (E : DerivedCategory C) :
    Function.Bijective (fun f : (DerivedCategory.singleFunctor C 0).obj P ⟶ E ↦
      (DerivedCategory.homologyFunctor C 0).map f) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let S := (DerivedCategory.singleFunctor C 0).obj P
  let T := (t.triangleLTGE 0).obj E
  have hT := t.triangleLTGE_distinguished 0 E
  have : t.IsLE T.obj₁ (-1) := by
    change t.IsLE ((t.truncLT 0).obj E) (0 - 1)
    infer_instance
  have hv (f : S ⟶ T.obj₁) : f = 0 := projective_single_to_negative_eq_zero P _ f
  have hv' (f : S ⟶ T.obj₁⟦(1 : ℤ)⟧) : f = 0 := by
    have : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) := by
      have : t.IsLE T.obj₁ (-1) := inferInstance
      have := t.isLE_shift T.obj₁ (-1) 1 (-2) (by omega)
      exact t.isLE_of_le _ (-2) (-1) (by omega)
    exact projective_single_to_negative_eq_zero P _ f
  have hpost : Function.Bijective (fun f : S ⟶ E ↦ f ≫ T.mor₂) := by
    constructor
    · intro f g h
      obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hT (f - g) (by simp [h])
      rw [hv a, Limits.zero_comp] at ha
      exact sub_eq_zero.mp ha
    · intro g
      obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT g (hv' (g ≫ T.mor₃))
      exact ⟨f, hf.symm⟩
  let H := DerivedCategory.homologyFunctor C 0
  have hH : Function.Bijective (fun f : S ⟶ T.obj₃ ↦ H.map f) :=
    DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE 0
  have hπ : IsIso (H.map T.mor₂) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E 0 0 le_rfl
  constructor
  · intro f g h
    apply hpost.1
    apply hH.1
    simpa only [Functor.map_comp] using
      congrArg (fun a ↦ a ≫ H.map T.mor₂) h
  · intro g
    obtain ⟨a, ha⟩ := hH.2 (g ≫ H.map T.mor₂)
    obtain ⟨f, hf⟩ := hpost.2 a
    refine ⟨f, (cancel_mono (H.map T.mor₂)).1 ?_⟩
    change f ≫ T.mor₂ = a at hf
    change H.map a = g ≫ H.map T.mor₂ at ha
    rw [← H.map_comp, hf, ha]

/-- Maps from the free rank-one module in degree zero compute zeroth cohomology.
Source: Stacks Project, Tag 09M1, proof, first paragraph (the affine module calculation).
(blueprint: lem-pc-derived-free-module-hom-homology).
Proof: Maps from a projective module in degree zero to any strictly negative
complex vanish, by Mathlib's projective-source vanishing theorem and a strictly
bounded-above representative. In the canonical truncation triangle
τ<0(E) → E → τ≥0(E), maps from A[0] to both τ<0(E) and its shift by 1 vanish.
The exact Hom sequence therefore makes postcomposition with E → τ≥0(E) bijective.
Zeroth homology is bijective on maps A[0] → τ≥0(E), by the shifted-heart homology
comparison, and H^0(E) → H^0(τ≥0(E)) is an isomorphism. Hence H^0 is bijective on
maps A[0] → E for arbitrary, possibly unbounded E. This is an additive map, so it
is an additive equivalence. Precompose with the inverse of H^0(A[0]) ≅ A, then
evaluate the resulting A-linear map at 1. The composite sends g to
(ε.inv ≫ H^0(g))(1). The composition law for H^0 gives naturality for every derived
morphism, independently of representatives. The argument covers the zero ring. -/
theorem derivedFreeModule_hom_homology (A : Type u) [Ring A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat
    ∃ e : ∀ E : DerivedCategory (ModuleCat.{u} A),
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A A)) ⟶ E) ≃+ H.obj E,
      ∀ (E E' : DerivedCategory (ModuleCat.{u} A)) (f : E ⟶ E')
        (g : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A A) ⟶ E),
        e E' (g ≫ f) = H.map f (e E g) := by
  classical
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} A) 0).app (ModuleCat.of A A)
  let c (E : DerivedCategory (ModuleCat.{u} A)) :
      (H.obj S ⟶ H.obj E) ≃+ (ModuleCat.of A A ⟶ H.obj E) :=
    { toEquiv := Iso.homCongr ε (Iso.refl _)
      map_add' := by intro f g; simp [Iso.homCongr] }
  let e (E : DerivedCategory (ModuleCat.{u} A)) :=
    (AddEquiv.ofBijective (H.mapAddHom (X := S) (Y := E))
      (projective_single_homology_bijective (ModuleCat.of A A) E)).trans
      ((c E).trans (ModuleCat.homAddEquiv.trans
        (LinearMap.ringLmapEquivSelf A ℤ (H.obj E)).toAddEquiv))
  refine ⟨e, ?_⟩
  intro E E' f g
  change (ε.inv ≫ H.map (g ≫ f)).hom (1 : A) =
    (H.map f).hom ((ε.inv ≫ H.map g).hom (1 : A))
  rw [H.map_comp, ← Category.assoc]
  rfl

end AlgebraicGeometry
