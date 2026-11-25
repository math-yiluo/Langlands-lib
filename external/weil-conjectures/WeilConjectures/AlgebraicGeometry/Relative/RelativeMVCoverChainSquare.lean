/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopySquareRectification
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageHomotopyComparison
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackConeSquareTransposition
/-! # A strict relative cover comparison before cylinder replacement

## References

* Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Chain representatives for the unrestricted relative Mayer--Vietoris square. -/
theorem relativeMV_cover_chain_square
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ a.left)
      (e₂ : DerivedCategory.Q.obj B ≅ (b U).left ⊞ (b V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (b (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  obtain ⟨A, B, A', B', t, t', α, β, H, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ⟩ :=
    relativeMV_direct_image_homotopy_comparison f f' g g' hpull K K' φ U V hcover
  obtain ⟨C, D, s, a, b, H', d₁, d₂, d₃, ha, hb, hc⟩ :=
    derivedPullback_cone_square_transposition g A B A' B' t t' α β H
  obtain ⟨T, i, c, hcomm, r₂, r₃, hr₂, hr₃⟩ :=
    CochainComplex.homotopy_square_cone_rectification s t' a b H'
  refine ⟨C, T, A', B', i, t', a, c, hcomm,
    d₁ ≪≫ e₁, r₂ ≪≫ d₂ ≪≫ e₂, r₃ ≪≫ d₃ ≪≫ e₃, e₁', e₂', e₃', ?_, ?_, ?_⟩
  · simpa only [Iso.trans_hom, Category.assoc, hα] using
      congrArg (fun k ↦ k ≫ e₁'.hom) ha
  · simpa only [Iso.trans_hom, Category.assoc, hb, hβ] using
      congrArg (fun k ↦ k ≫ e₂'.hom) hr₂
  · simpa only [Iso.trans_hom, Category.assoc, hc, hγ] using
      congrArg (fun k ↦ k ≫ e₃'.hom) hr₃
end AlgebraicGeometry
