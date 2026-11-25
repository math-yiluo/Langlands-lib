/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedOpenRoofComparison
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedRoofMiddleMateComparison

/-! # Mate comparisons for the concrete resolved row roof

## References

* Stacks Project, Tags 08FE, 08HY, 08HZ and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.defeqAttrib.useBackward true

/-- Transport a third-component equation through two functors and a fixed tail. -/
private theorem map_third_roof_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (Q : D ⥤ E)
    {A R : ShortComplex C} (u : A ⟶ R)
    {T : E} (t : Q.obj (F.obj R.X₃) ⟶ T)
    (r : A.X₃ ⟶ R.X₃) (h : u.τ₃ = r) :
    Q.map (F.mapShortComplex.map u).τ₃ ≫ t = Q.map (F.map r) ≫ t := by
  exact congrArg (fun a : A.X₃ ⟶ R.X₃ ↦ Q.map (F.map a) ≫ t) h

/-- Compute the third component with the composed row functors kept explicit. -/
private theorem roof_denominator_third
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasZeroMorphisms E] [HasZeroMorphisms T]
    (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (F : D ⥤ E) [F.PreservesZeroMorphisms]
    (H₁ : C ⥤ T) [H₁.PreservesZeroMorphisms]
    (H₂ : T ⥤ E) [H₂.PreservesZeroMorphisms] (c : H₁ ⋙ H₂ ≅ G ⋙ F)
    {J : ShortComplex C} {L : ShortComplex D} (s : J.map G ⟶ L) :
    let v : (J.map H₁).map H₂ ⟶ L.map F :=
      (J.mapNatIso c).hom ≫ F.mapShortComplex.map s
    v.τ₃ = c.hom.app J.X₃ ≫ F.map s.τ₃ := rfl

/-- Equal invertible denominators give the same roof composite. -/
private theorem roof_denominator_transport
    {C : Type*} [Category C] {X Y Z T : C}
    (p : X ⟶ Z) (q q' : Y ⟶ Z) [hq : IsIso q] [hq' : IsIso q']
    (h : q = q') (η : Y ⟶ T) :
    p ≫ inv q ≫ η = p ≫ inv q' ≫ η := by
  cases h
  rfl

/-- Combine two component comparisons after transporting the second equation. -/
private theorem combine_component_comparisons
    {A B C D : Sort*} {P : A → B → Prop} {Q Q' : C → D → Prop}
    (h₂ : ∃ a b, P a b) (h₃ : ∃ c d, Q c d)
    (transport : ∀ c d, Q c d → Q' c d) :
    ∃ a c b d, P a b ∧ Q' c d := by
  obtain ⟨a, b, ha⟩ := h₂
  obtain ⟨c, d, hc⟩ := h₃
  exact ⟨a, c, b, d, ha, transport c d hc⟩

-- The component API keeps proof elaboration within this bound.
-- The two open-vertex types contain fixed complex and derived functor comparisons.
/-- The open and diagonal components of a normalized resolved row roof are the
specified local base-change mates. -/
theorem relativeMV_resolved_roof_open_mate_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (u₀ : schemeMayerVietorisComplex X U V (schemeMVResolution X K) ⟶
      schemeMayerVietorisComplex X U V
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hu₂ : u₀.τ₂ = biprod.map
      (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
      (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r))
    (hu₃ : u₀.τ₃ =
      ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) :
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
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
    let u : A ⟶ R := Ff.mapShortComplex.map u₀
    let v : B.map F ⟶ R := (D.mapNatIso c).hom ≫
      Ff.mapShortComplex.map (schemeMVImageChainMap g' U V J L s)
    ∀ (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₂
      letI := hv₃
    ∃ (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right),
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  (
    -- Reduce the statement aliases without introducing duplicate local data.
    dsimp -proj only
    intro hv₂ hv₃
    have := hv₂
    have := hv₃
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    have hv := roof_denominator_third
      ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
      ((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
      ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)) c
      (schemeMVImageChainMap g' U V (schemeMVResolution X' K')
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')) s)
    dsimp -proj only [c] at hv
    have hvW := (congrArg (fun a ↦ IsIso
      ((DerivedCategory.Q.{w} (C := SheafOfModules.{u}
        (moduleRings S.toRingedSpace))).map a)) hv).mp hv₃
    simp only [Iso.symm_hom] at hvW
    refine combine_component_comparisons
      (relativeMV_resolved_roof_middle_mate_comparison
        f f' g g' hpull K K' φ U V r s u₀ hr hs hu₂ hv₂)
      (relativeMV_resolved_open_roof_comparison
        f f' g g' hpull K K' φ (U ⊓ V) r s hr hs hvW) ?_
    intro e₃ e₃' h₃
    exact (map_third_roof_transport
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
      (DerivedCategory.Q.{w} (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))) u₀
      ((@inv _ _ _ _ _ hv₃) ≫ (schemeMVDirectImageLocalization g).app
        (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj (schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ (U ⊓ V))
            (schemeMVResolution X' K'))))
      (((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) hu₃).trans
      ((roof_denominator_transport
        (DerivedCategory.Q.{w}.map
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).map
            (((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r)))
        _ _ (hq := hv₃) (hq' := hvW)
        (congrArg (DerivedCategory.Q.{w}
          (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))).map hv)
        ((schemeMVDirectImageLocalization g).app
          (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj (schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ (U ⊓ V))
              (schemeMVResolution X' K'))))).trans h₃)
  )

end AlgebraicGeometry
