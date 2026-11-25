/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageRowsCore

/-! # Resolved relative short exact rows before tensor pullback

## References

* Stacks Project, Cohomology, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A resolved relative comparison of short exact rows, before the cone-to-quotient passage. -/
theorem relativeMV_direct_image_rows
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (P : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
      (P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P'.map F)
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj P.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁) ≫ e₁'.hom =
        e₁.hom ≫ a.hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂) ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
      (adj.homEquiv _ _).symm (DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃) ≫ e₃'.hom =
        e₃.hom ≫ (b (U ⊓ V)).hom := by
  classical
  dsimp only
  obtain ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hα, hβ, hγ, hP, hP'⟩ :=
    relativeMV_direct_image_rows_core f f' g g' hpull K K' φ U V hcover
  refine ⟨P, P', m, e₁, e₂, e₃, e₁', e₂', e₃', hP, hP', ?_, ?_, ?_⟩
  · rw [hα, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hβ, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [hγ, Equiv.symm_apply_apply]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry
