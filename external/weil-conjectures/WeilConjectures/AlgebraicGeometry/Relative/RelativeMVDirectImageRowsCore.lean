/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVHomotopyPullback
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageRowRoof

/-! # Resolved relative rows before the overlap mate

## References

* Stacks Project, Cohomology of Sheaves, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

private lemma roof_mate_transport {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    {X₀ X Y Z : C} {A B Y' : D}
    (p : X₀ ⟶ X) [IsIso p] (u : X ⟶ Z) (v : Y ⟶ Z) [IsIso v]
    (m : X₀ ⟶ Y) (η : Y ⟶ G.obj Y') (e : L.obj X ≅ A) (e' : Y' ≅ B)
    (a : A ⟶ B) (hs : p ≫ u = m ≫ v)
    (hr : u ≫ inv v ≫ η = (adj.homEquiv _ _) (e.hom ≫ a ≫ e'.inv)) :
    m ≫ η = (adj.homEquiv _ _)
      ((L.mapIso (asIso p) ≪≫ e).hom ≫ a ≫ e'.inv) := by
  have hm : m = p ≫ u ≫ inv v := by
    have h := congrArg (fun t => t ≫ inv v) hs
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h.symm
  rw [hm, Category.assoc, Category.assoc, hr]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Category.assoc] using
    (adj.homEquiv_naturality_left p (e.hom ≫ a ≫ e'.inv)).symm

set_option linter.unusedVariables false in
/-- Resolved source and target short exact rows and their vertex comparisons,
before recording the three mate equations. -/
theorem relativeMV_direct_image_rows_core
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
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (b (U ⊓ V)).right)
      (hα : DerivedCategory.Q.map m.τ₁ ≫ η.app P'.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv))
      (hβ : DerivedCategory.Q.map m.τ₂ ≫ η.app P'.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv))
      (hγ : DerivedCategory.Q.map m.τ₃ ≫ η.app P'.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)),
      P.ShortExact ∧ P'.ShortExact := by
  classical
  extract_lets (descend := false) G F η adj a b
  obtain ⟨A, R, B, u, v, e₁, e₂, e₃, e₁', e₂', e₃', hv₁, hv₂, hv₃,
      hA, hR, hB, hBF, hα, hβ, hγ⟩ :=
    relativeMV_direct_image_row_roof f f' g g' hpull K K' φ U V hcover
  have := hv₁
  have := hv₂
  have := hv₃
  obtain ⟨P, p, m, hP, hp₁, hp₂, hp₃, hs₁, hs₂, hs₃⟩ :=
    relativeMV_homotopyPullback_row_strictify A (B.map F) R u v hA hBF hR
  have := hp₁
  have := hp₂
  have := hp₃
  refine ⟨P, B, m,
    (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map p.τ₁)) ≪≫ e₁,
    (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map p.τ₂)) ≪≫ e₂,
    (derivedPullback g).mapIso (asIso (DerivedCategory.Q.map p.τ₃)) ≪≫ e₃,
    e₁', e₂', e₃', ?_, ?_, ?_, hP, hB⟩
  · exact roof_mate_transport adj _ _ _ _ _ e₁ e₁' a.hom hs₁ hα
  · exact roof_mate_transport adj _ _ _ _ _ e₂ e₂'
      (biprod.map (b U).hom (b V).hom) hs₂ hβ
  · exact roof_mate_transport adj _ _ _ _ _ e₃ e₃' (b (U ⊓ V)).hom hs₃ hγ

end AlgebraicGeometry
