/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedRowRoofComparisons

/-! # A normalized roof between resolved Mayer--Vietoris rows

## References

* Stacks Project, Cohomology of Sheaves, Tags 08BV, 08HZ, 08FE and 08HY
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private lemma mapped_split_row_shortExact
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (A : ShortComplex (CochainComplex C ℤ))
    (hA : ∀ n, Nonempty ((A.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting))
    (F : C ⥤ D) [F.Additive] :
    (A.map (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨s⟩ := hA n
  exact (s.map F).shortExact

private lemma mv_row_degreewise_split
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n, Injective (I.X n)) (n : ℤ) :
    Nonempty (((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval _ (.up ℤ) n)).Splitting) := by
  have : Injective (((schemeMayerVietorisComplex X U V I).map
      (HomologicalComplex.eval _ (.up ℤ) n)).X₁) := hI n
  exact ⟨((schemeMayerVietorisComplex_shortExact X U V hcover I hI).map_of_exact
    (HomologicalComplex.eval _ (.up ℤ) n)).splittingOfInjective⟩

/-- A common resolved image row compares the source Mayer--Vietoris row with
its target direct-image row before strictification. -/
theorem relativeMV_direct_image_row_roof
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
    ∃ (A R : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ))
      (B : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (u : A ⟶ R) (v : B.map F ⟶ R)
      (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj B.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right)
      (hv₁ : IsIso (DerivedCategory.Q.map v.τ₁))
      (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₁
      letI := hv₂
      letI := hv₃
      A.ShortExact ∧ R.ShortExact ∧ B.ShortExact ∧ (B.map F).ShortExact ∧
      (DerivedCategory.Q.map u.τ₁ ≫ inv (DerivedCategory.Q.map v.τ₁) ≫ η.app B.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv)) ∧
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv))  := by
  classical
  dsimp -proj only
  let I := schemeMVResolution X K
  let J := schemeMVResolution X' K'
  let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
  let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
  let A := (schemeMayerVietorisComplex X U V I).map Ff
  let R := (schemeMayerVietorisComplex X U V L).map Ff
  let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
  obtain ⟨u, v, e₁, e₂, e₃, e₁', e₂', e₃', hv₁, hv₂, hv₃, hα, hβ, hγ⟩ :=
    relativeMV_resolved_row_roof_comparisons f f' g g' hpull K K' φ U V
  have hcover' : (g' ⁻¹ᵁ U) ⊔ (g' ⁻¹ᵁ V) = ⊤ := by
    simpa only [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_top] using
      congrArg (fun W => g' ⁻¹ᵁ W) hcover
  have hA : A.ShortExact := mapped_split_row_shortExact _
    (mv_row_degreewise_split X U V hcover I (fun n => inferInstance)) _
  have hR : R.ShortExact := mapped_split_row_shortExact _
    (mv_row_degreewise_split X U V hcover L (fun n => inferInstance)) _
  have hJ := mv_row_degreewise_split X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) hcover' J
    (fun n => inferInstance)
  have hB : B.ShortExact := mapped_split_row_shortExact _ hJ _
  have hBF : (B.map
      ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ))).ShortExact :=
    mapped_split_row_shortExact _ hJ
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
  exact ⟨A, R, B, u, v, e₁, e₂, e₃, e₁', e₂', e₃', hv₁, hv₂, hv₃,
    hA, hR, hB, hBF, hα, hβ, hγ⟩

end AlgebraicGeometry
