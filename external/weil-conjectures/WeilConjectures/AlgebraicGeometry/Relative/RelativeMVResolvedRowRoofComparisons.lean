/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedRoofVertexNormalization

/-! # Comparisons of canonical resolved Mayer--Vietoris rows

## References

* Stacks Project, Tags 08FE, 08HY, 08HZ and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private lemma resolution_map_surjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (I J : CochainComplex A ℤ) [J.IsKInjective]
    (φ : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    ∃ r : I ⟶ J, DerivedCategory.Q.map r = φ := by
  let e := DerivedCategory.quotientCompQhIso A
  obtain ⟨t, ht⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj I) J).surjective
      (e.hom.app I ≫ φ ≫ e.inv.app J)
  obtain ⟨r, hr⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective t
  refine ⟨r, ?_⟩
  have hn := e.hom.naturality r
  dsimp only [Functor.comp_map] at hn
  rw [hr, ht] at hn
  apply (cancel_epi (e.hom.app I)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm

attribute [local irreducible] schemeOpenModuleAdjunction schemeOpenModuleImageRestriction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- The row-map equations unfold the three restriction-image complex functors.
private noncomputable def mv_row_map (X : Scheme.{u}) (U V : X.Opens)
    {I J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (r : I ⟶ J) : schemeMayerVietorisComplex X U V I ⟶
      schemeMayerVietorisComplex X U V J where
  τ₁ := r
  τ₂ := biprod.map
    (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
    (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r)
  τ₃ := ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [schemeMayerVietorisComplex, schemeMayerVietorisF,
        Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      apply HomologicalComplex.Hom.ext
      funext n
      change r.f n ≫ (schemeOpenModuleAdjunction X U).unit.app (J.X n) =
        (schemeOpenModuleAdjunction X U).unit.app (I.X n) ≫
          (schemeOpenModuleImage X U).map (r.f n)
      exact (schemeOpenModuleAdjunction X U).unit.naturality (r.f n)
    · simp only [schemeMayerVietorisComplex, schemeMayerVietorisF,
        Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
      apply HomologicalComplex.Hom.ext
      funext n
      change r.f n ≫ (schemeOpenModuleAdjunction X V).unit.app (J.X n) =
        (schemeOpenModuleAdjunction X V).unit.app (I.X n) ≫
          (schemeOpenModuleImage X V).map (r.f n)
      exact (schemeOpenModuleAdjunction X V).unit.naturality (r.f n)
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [schemeMayerVietorisComplex, schemeMayerVietorisG,
        biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (NatTrans.mapHomologicalComplex
        (schemeOpenModuleImageRestriction X (homOfLE (inf_le_left : U ⊓ V ≤ U)))
          (.up ℤ)).naturality r
    · simp only [schemeMayerVietorisComplex, schemeMayerVietorisG,
        biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg
        ((NatTrans.mapHomologicalComplex
          (schemeOpenModuleImageRestriction X (homOfLE (inf_le_right : U ⊓ V ≤ V)))
            (.up ℤ)).naturality r)

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option backward.defeqAttrib.useBackward true

/-- Canonical resolution rows have a normalized direct-image roof. This is a
comparison statement without a cover assumption or any assertion of exactness. -/
theorem relativeMV_resolved_row_roof_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) :
    let I := schemeMVResolution X K
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let A := (schemeMayerVietorisComplex X U V I).map Ff
    let R := (schemeMayerVietorisComplex X U V L).map Ff
    let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (u : A ⟶ R) (v : B.map F ⟶ R)
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
  obtain ⟨r, hr⟩ := resolution_map_surjective I L
    ((schemeMVResolutionIso X K).hom ≫ (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
  obtain ⟨s, hs⟩ := resolution_map_surjective _ L
    ((schemeMVDirectImageLocalization g').app J ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
  let u₀ := mv_row_map X U V r
  exact ⟨_, _,
    relativeMV_resolved_roof_vertex_normalization f f' g g' hpull K K' φ U V
      r s u₀ hr hs rfl rfl rfl⟩

end AlgebraicGeometry
