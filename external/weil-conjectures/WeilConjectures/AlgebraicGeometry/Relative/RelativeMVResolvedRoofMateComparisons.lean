/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVNormalizedCoefficientRoof
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVResolvedRoofOpenMateComparisons

/-! # Mate comparisons for the concrete resolved row roof

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

/-- Transport the first component without rewriting the other two vertices. -/
private theorem map_first_roof_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (Q : D ⥤ E)
    {A R : ShortComplex C} (u : A ⟶ R)
    {T : E} (t : Q.obj (F.obj R.X₁) ⟶ T)
    (r : A.X₁ ⟶ R.X₁) (h : u.τ₁ = r) :
    Q.map (F.mapShortComplex.map u).τ₁ ≫ t = Q.map (F.map r) ≫ t := by
  exact congrArg (fun a : A.X₁ ⟶ R.X₁ ↦ Q.map (F.map a) ≫ t) h

/-- Transport a transposed arrow through the two vertex isomorphisms. -/
private theorem transport_roof_mate
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M T : C} {N T' : D} (e : M ≅ T) (e' : N ≅ T')
    (a : F.obj T ⟶ T') (γ : T ⟶ G.obj T')
    (hγ : adj.homEquiv T T' a = γ) {roof : M ⟶ G.obj N}
    (hroof : roof = e.hom ≫ γ ≫ G.map e'.inv) :
    roof = adj.homEquiv M N ((F.mapIso e).hom ≫ a ≫ e'.inv) := by
  rw [Functor.mapIso_hom, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_right, hγ]
  exact hroof

/-- Compute the first denominator component for arbitrary row functors. -/
private theorem roof_denominator_first
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
    v.τ₁ = c.hom.app J.X₁ ≫ F.map s.τ₁ := rfl

/-- Equal invertible denominators give equal roof composites. -/
private theorem roof_denominator_transport
    {C : Type*} [Category C] {X Y Z T : C}
    (p : X ⟶ Z) (q q' : Y ⟶ Z) [hq : IsIso q] [hq' : IsIso q']
    (h : q = q') (η : Y ⟶ T) :
    p ≫ inv q ≫ η = p ≫ inv q' ≫ η := by
  cases h
  rfl

/-- Assemble the global comparison and the two open comparisons. -/
private theorem combine_mate_comparisons
    {A₁ A₂ A₃ B₁ B₂ B₃ : Sort*}
    {P : A₁ → B₁ → Prop} {Q : A₂ → B₂ → Prop} {R : A₃ → B₃ → Prop}
    (a₁ : A₁) (b₁ : B₁) (h₁ : P a₁ b₁)
    (h₂₃ : ∃ a₂ a₃ b₂ b₃, Q a₂ b₂ ∧ R a₃ b₃) :
    ∃ a₁ a₂ a₃ b₁ b₂ b₃, P a₁ b₁ ∧ Q a₂ b₂ ∧ R a₃ b₃ := by
  obtain ⟨a₂, a₃, b₂, b₃, h₂, h₃⟩ := h₂₃
  exact ⟨a₁, a₂, a₃, b₁, b₂, b₃, h₁, h₂, h₃⟩

private lemma mate_transpose_to
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {K : D} (β : M ⟶ R₁.obj K) (δ : L₂.obj M ⟶ K)
    (h : α.app M ≫ L₁.map β ≫ a₁.counit.app K = δ) :
    β ≫ (conjugateEquiv a₁ a₂ α).app K = a₂.homEquiv M K δ := by
  apply (a₂.homEquiv M K).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc, α.naturality, Category.assoc]
  have hδ : L₂.map ((a₂.homEquiv M K) δ) ≫ a₂.counit.app K = δ := by
    simpa only [Adjunction.homEquiv_symm_apply] using
      (a₂.homEquiv M K).symm_apply_apply δ
  exact h.trans hδ.symm

private lemma square_conjugate_transpose
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {G : C₀ ⥤ C₂} {T : C₂ ⥤ C₀}
    {F' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂} {G' : C₁ ⥤ C₃} {T' : C₃ ⥤ C₁}
    (af : F ⊣ R) (ag : G ⊣ T) (af' : F' ⊣ R') (ag' : G' ⊣ T')
    (α : G ⋙ F' ≅ F ⋙ G') {K : C₁} {K' : C₃} (φ : G'.obj K ⟶ K') :
    ag.homEquiv _ _ (af'.homEquiv _ _
        (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ)) =
      R.map (ag'.homEquiv _ _ φ) ≫
        (conjugateEquiv (af.comp ag') (ag.comp af') α.hom).app K' := by
  have h := mate_transpose_to (af.comp ag') (ag.comp af') α.hom
    (R.map (ag'.homEquiv _ _ φ))
    (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ) ?_
  · rw [Adjunction.comp_homEquiv] at h
    exact h.symm
  · simp only [Functor.comp_map, Adjunction.comp_counit_app]
    have hn := af.counit.naturality (ag'.homEquiv _ _ φ)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← G'.map_comp_assoc, hn]
    simp only [G'.map_comp, Category.assoc]
    have he : G'.map (ag'.homEquiv _ _ φ) ≫ ag'.counit.app K' = φ := by
      simpa only [Adjunction.homEquiv_symm_apply] using
        (ag'.homEquiv _ _).symm_apply_apply φ
    rw [he]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option cleanup.letToHave false
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh RingedSpace.moduleDirectImage
set_option backward.defeqAttrib.useBackward true
set_option linter.all false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem global_arrow_transpose
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : CategoryTheory.IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) hpull.w.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    (relativeMVAdj g).homEquiv _ _
        (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom =
      (schemeDerivedDirectImage f).map ((relativeMVAdj g').homEquiv _ _ φ) ≫
        δ.app K' := by
  intro κ δ
  have he : schemeDerivedBaseChangeMap f f' g g' hpull.w K =
      (relativeMVAdj f').homEquiv _ _
        (κ.hom.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((relativeMVAdj f).counit.app K)) := by
    simp +instances only [schemeDerivedBaseChangeMap, relativeMVAdj, relativeMVComp, κ,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc]
    rfl
  dsimp only [relativeMVGlobalArrow, Arrow.mk, Arrow.hom]
  rw [he]
  rw [← (relativeMVAdj f').homEquiv_naturality_right]
  simpa +instances only [Category.assoc, δ, Arrow.right] using
    square_conjugate_transpose (relativeMVAdj f) (relativeMVAdj g)
      (relativeMVAdj f') (relativeMVAdj g') κ φ

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- The three vertex comparison types include composed derived and complex functors.
/-- Identify the three normalized roof maps with the prescribed base-change
arrows, after their denominator vertices are known invertible. -/
theorem relativeMV_resolved_roof_mate_comparisons
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
    (hu₁ : u₀.τ₁ = r)
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
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
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
    ∀ (hv₁ : IsIso (DerivedCategory.Q.map v.τ₁))
      (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₁
      letI := hv₂
      letI := hv₃
    ∃ (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj B.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right),
      (DerivedCategory.Q.map u.τ₁ ≫ inv (DerivedCategory.Q.map v.τ₁) ≫ η.app B.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv)) ∧
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)) := by
  classical
  dsimp -proj only
  intro hv₁ hv₂ hv₃
  let c := (Functor.mapHomologicalComplexCompIso
      (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
        RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
  let t := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f.toLRSHom.toShHom (schemeMVResolution X K)).symm ≪≫
    (schemeDerivedDirectImage f).mapIso (schemeMVResolutionIso X K)
  let t' := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f'.toLRSHom.toShHom (schemeMVResolution X' K')).symm ≪≫
    (schemeDerivedDirectImage f').mapIso (schemeMVResolutionIso X' K')
  have hvc := roof_denominator_first
    ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    ((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)) c
    (schemeMVImageChainMap g' U V (schemeMVResolution X' K')
      (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')) s)
  dsimp -proj only [c] at hvc
  have hvq := (congrArg (fun a ↦ IsIso
    ((DerivedCategory.Q.{w} (C := SheafOfModules.{u}
      (moduleRings S.toRingedSpace))).map a)) hvc).mp hv₁
  simp only [Iso.symm_hom] at hvq
  refine combine_mate_comparisons ((derivedPullback g).mapIso t) t' ?_
    (relativeMV_resolved_roof_open_mate_comparisons f f' g g' hpull K K' φ U V
      r s u₀ hr hs hu₂ hu₃ hv₂ hv₃)
  refine (map_first_roof_transport
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ))
    (DerivedCategory.Q.{w} (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))) u₀
    ((@inv _ _ _ _ _ hv₁) ≫ (schemeMVDirectImageLocalization g).app
      (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K'))) r hu₁).trans
    (transport_roof_mate (relativeMVAdj g) t t'
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom _
      (global_arrow_transpose f f' g g' hpull K K' φ) ?_)
  refine (roof_denominator_transport
    (DerivedCategory.Q.{w}.map
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).map r)) _ _ (hq := hv₁) (hq' := hvq)
    (congrArg (DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))).map hvc)
    ((schemeMVDirectImageLocalization g).app
      (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K')))).trans ?_
  have hroof := relativeMV_normalized_coefficient_roof f f' g g' hpull.w K K'
    (schemeMVResolution X K)
    (schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (schemeMVResolution X' K') (schemeMVResolutionIso X K)
    (schemeMVResolutionIso X' K')
    (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))
    ((relativeMVAdj g').homEquiv _ _ φ) r s hr hs hvq
  simp only [t, t', Category.assoc, schemeMayerVietorisComplex,
    schemeMVImageChainMap, ShortComplex.homMk] at hroof ⊢
  convert hroof using 1

end AlgebraicGeometry
