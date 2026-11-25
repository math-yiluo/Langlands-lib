/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting

/-! # Naturality of a boundary computed by compatible resolutions

Source: Stacks Project, Tags 015B and 01DZ.
(blueprint: lem-sc-resolved-boundary-naturality).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
universe v₁ v₂ u₁ u₂ w₁ w₂

set_option backward.isDefEq.respectTransparency false in
/-- A compatible resolution computes the natural derived connecting map.
Source: Stacks Project, Tags 015B and 01DZ.
(blueprint: lem-sc-resolved-boundary-naturality).
Proof: Obtain the cohomological delta-functor and both comparison identities from
rightDerived_triangle_connecting. Eliminate the equality identifying its functors with
rightDerived. Its first comparison identifies the source delta with the boundary of the
supplied compatible resolutions; short exactness witnesses are equal by proof irrelevance.
Use delta-functor naturality for the supplied short-complex morphism. Its second comparison
identifies the target delta with the canonical triangle boundary after postcomposition with
the homology/right-derived comparison. Cancel that comparison with its inverse. -/
private theorem resolvedBoundary_naturality_aux
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v]
    (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    (IC.isoRightDerivedObj v 0).hom ≫ hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj v 1).inv ≫ (v.rightDerived 1).map φ.τ₁ =
      (v.rightDerived 0).map φ.τ₃ ≫
        (v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.app T.X₃ ≫
        DerivedCategory.HomologySequence.δ
          ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
            hT.singleTrianglePlus) 0 1 (by norm_num) ≫
        (v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 1).hom.app T.X₁ := by
  obtain ⟨G, hF, hs, ht⟩ := rightDerived_triangle_connecting v
  rcases G with ⟨F, add, delta, mono, exm, exr, exl, nat⟩
  dsimp only at hF
  subst F
  dsimp only at hs ht nat
  obtain ⟨hv, hd⟩ := hs S hS IA IB IC α β hαβ hιA hιB hH
  have heq : hv = hΓ := Subsingleton.elim _ _
  subst hv
  have hd0 := hd 0
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hd0
  have hc := ht T hT 0
  simp only [eqToHom_refl, Category.id_comp] at hc
  have hn := nat S T hS hT φ 0
  rw [hd0] at hn
  simp only [Category.assoc] at hn
  erw [hn]
  have hc' := congrArg (fun f ↦ f ≫
    (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso T.X₁ 1).hom) hc
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc'
  erw [hc']
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- The resolved boundary comparison, precomposed with the section comparison and
evaluated on a module element, with the quotient component explicitly identified.
Source: Stacks Project, Tags 015B and 01DZ.
(blueprint: lem-sc-resolved-boundary-naturality).
Proof: Apply the abstract resolution/triangle comparison and delta naturality above.
Precompose by toRightDerivedZero, move it past the third component by its naturality,
and evaluate. Composition of module maps is composition of their linear maps.
Finally substitute the supplied identities for the quotient component, its image
element, and the target boundary composite. These equalities specify the data uniquely. -/
theorem resolvedBoundary_naturality
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    {R : Type u₂} [Ring R]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} (ModuleCat.{u₂} R)]
    (v : A ⥤ ModuleCat.{u₂} R) [v.Additive] [PreservesFiniteLimits v]
    (S T : ShortComplex A) (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (q : S.X₃ ⟶ T.X₃) (hq : φ.τ₃ = q)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ A).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ A).map S.g ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval A (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      (v.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (z : v.obj S.X₃) (z' : v.obj T.X₃)
    (hz : (v.map q).hom z = z')
    (b : v.obj T.X₃ ⟶ (v.rightDerived 1).obj T.X₁)
    (hb : b = v.toRightDerivedZero.app T.X₃ ≫
        (v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).inv.app T.X₃ ≫
        DerivedCategory.HomologySequence.δ
          ((v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
            hT.singleTrianglePlus) 0 1 (by norm_num) ≫
        (v.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 1).hom.app T.X₁) :
    ((v.rightDerived 1).map φ.τ₁).hom
      ((v.toRightDerivedZero.app S.X₃ ≫
        (IC.isoRightDerivedObj v 0).hom ≫ hΓ.δ 0 1 rfl ≫
          (IA.isoRightDerivedObj v 1).inv).hom z) = b.hom z' := by
  have hn := resolvedBoundary_naturality_aux.{_, _, _, _, w₁, w₂}
    v S T hS hT φ IA IB IC α β hαβ hιA hιB hH hΓ
  have hn' := congrArg (fun f ↦ v.toRightDerivedZero.app S.X₃ ≫ f) hn
  rw [← v.toRightDerivedZero.naturality_assoc φ.τ₃] at hn'
  have he := congrArg (fun f ↦ f.hom z) hn'
  rw [hb]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hq, hz] using he

end CategoryTheory
