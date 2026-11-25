/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import all Mathlib.AlgebraicGeometry.Morphisms.FlatRank  -- for unfolding `Scheme.Hom.finrank`

/-!
# The pushforward of the structure sheaf along a finite morphism

For a finite morphism `g : X ⟶ Y`, the `𝒪_Y`-module `g_* 𝒪_X` is coherent when `Y` is locally
noetherian, and when `Y` is integral it is free on a nonempty open subset of `Y`, of rank the
degree `g.finrank (genericPoint Y)` of `g` at the generic point.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pushforward_unit`: `g_* 𝒪_X` is of
  finite presentation.
- `AlgebraicGeometry.Scheme.Modules.exists_pullback_pushforward_unit_iso_free`: `g_* 𝒪_X` is
  generically free of rank `g.finrank (genericPoint Y)`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward`: the pushforward of a
  finite locally free module along a finite flat morphism of finite presentation is finite
  locally free.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pushforward_unit`: for `g` finite
  locally free of degree `d`, `g_* 𝒪_X` is finite locally free of rank `d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- **The pushforward of the structure sheaf along a finite morphism is coherent.** If
`g : X ⟶ Y` is finite and `Y` is locally noetherian, then `g_* 𝒪_X` is of finite presentation. -/
theorem isFinitePresentation_pushforward_unit [IsLocallyNoetherian Y] (g : X ⟶ Y) [IsFinite g] :
    ((pushforward g).obj (𝟙_ X.Modules)).IsFinitePresentation := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : ((pushforward g).obj (𝟙_ X.Modules)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom g _
  let f (V : Y.affineOpens) : Spec Γ(Y, V) ⟶ Y := V.2.isoSpec.inv ≫ V.1.ι
  have hf (V : Y.affineOpens) : (f V).opensRange = V.1 := by
    simp [f]
  have (V : Y.affineOpens) : IsNoetherianRing Γ(Y, V) :=
    IsLocallyNoetherian.component_noetherian V
  have (V : Y.affineOpens) :
      Module.Finite Γ(Spec Γ(Y, V), ⊤)
        Γ(((pushforward g).obj (𝟙_ X.Modules)).restrict (f V), ⊤) := by
    have h1 := g.finite_app ((f V) ''ᵁ ⊤) (by
      rw [Hom.image_top_eq_opensRange, hf]; exact V.2)
    have h2 := RingHom.Finite.comp h1 (RingHom.Finite.of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f V).appIso ⊤).inv).2))
    let := (CommRingCat.Hom.hom (((f V).appIso ⊤).inv ≫ g.app _)).toAlgebra
    exact (h2 : Module.Finite Γ(Spec Γ(Y, V), ⊤) Γ(X, g ⁻¹ᵁ ((f V) ''ᵁ ⊤)))
  choose P hP using fun V : Y.affineOpens ↦
    have := finite_sections_top_of_finite (((pushforward g).obj (𝟙_ X.Modules)).restrict (f V))
    exists_presentation_isFinite (((pushforward g).obj (𝟙_ X.Modules)).restrict (f V))
  refine isFinitePresentation_of_iSup_opensRange_eq_top _ f ?_ P
  simp only [hf]
  exact iSup_affineOpens_eq_top Y

/-- **The pushforward of the structure sheaf along a finite morphism is generically free.** If
`g : X ⟶ Y` is finite and `Y` is integral, then `g_* 𝒪_X` is free of rank
`d = g.finrank (genericPoint Y)` on a nonempty open subset of `Y`. -/
theorem exists_pullback_pushforward_unit_iso_free [IsIntegral Y] (g : X ⟶ Y) [IsFinite g] :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧
      Nonempty ((Modules.pullback U.ι).obj ((pushforward g).obj (𝟙_ X.Modules)) ≅
        SheafOfModules.free (ULift.{u} (Fin (g.finrank (genericPoint Y))))) := by
  -- The affine chart `C: Spec R ⟶ Y` at the generic point used to define `g.finrank`.
  set η := genericPoint Y
  let k := Y.affineOpenCover.idx η
  let R := Y.affineOpenCover.X k
  let C : Spec R ⟶ Y := Y.affineOpenCover.f k
  set s₀ := (Y.affineOpenCover.covers η).choose
  have hs₀ : C s₀ = η := (Y.affineOpenCover.covers η).choose_spec
  let π := pullback.snd g C
  have h1 : g.finrank η = π.appTop.hom.finrank ((Spec R).isoSpec.hom s₀) := rfl
  have : Nonempty (Spec R) := ⟨s₀⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion C
  have : IsDomain R := (affine_isIntegral_iff R).mp inferInstance
  -- `s₀` is the generic point `(0)` of `Spec R`.
  have hs₀bot : s₀.asIdeal = ⊥ := by
    refine le_bot_iff.mp fun a ha ↦ ?_
    let t : Spec R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    have : s₀ ⤳ t := C.isOpenEmbedding.isInducing.specializes_iff.mp (by
      rw [hs₀]
      exact (genericPoint_spec Y).specializes (Set.mem_univ _))
    exact (PrimeSpectrum.le_iff_specializes (s₀ : PrimeSpectrum R)
      (t : PrimeSpectrum R)).mpr this ha
  -- Compare `Γ(Spec R, g_* 𝒪_X) = Γ(X, g ⁻¹ᵁ V)` with the sections of the pullback of `g`
  -- along `C`, whose rank at `s₀` is `g.finrank η` by definition.
  let F := (pushforward g).obj (𝟙_ X.Modules)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : F.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g _
  let M := F.restrict C
  let V := C ''ᵁ ⊤
  let ι₁ := pullback.fst g C
  have hV : g ⁻¹ᵁ V = ι₁ ''ᵁ ⊤ := by
    simp only [V, ι₁, Hom.image_top_eq_opensRange, Hom.opensRange_pullbackFst]
  have hle : (⊤ : (Limits.pullback g C).Opens) ≤ ι₁ ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    rw [hV, Hom.preimage_image_eq]
  let κ : Γ(X, g ⁻¹ᵁ V) ⟶ Γ(Limits.pullback g C, ⊤) := ι₁.appLE (g ⁻¹ᵁ V) ⊤ hle
  have hκbij : Function.Bijective κ := by
    refine (Hom.appLE_congr ι₁ hle hV rfl (fun f ↦ Function.Bijective f)).mpr ?_
    rw [← Hom.appIso_hom']
    exact ConcreteCategory.bijective_of_isIso _
  have hκ : (C.appIso ⊤).inv ≫ g.app V ≫ κ = π.appTop := by
    have key : ∀ (f₁ f₂ : Limits.pullback g C ⟶ Y), f₁ = f₂ →
        ∀ e₁ e₂, f₁.appLE V ⊤ e₁ = f₂.appLE V ⊤ e₂ := by
      rintro _ _ rfl _ _
      rfl
    rw [Iso.inv_comp_eq, Hom.appIso_hom']
    change (g.app V ≫ ι₁.appLE (g ⁻¹ᵁ V) ⊤ hle) = C.appLE V ⊤ _ ≫ π.app ⊤
    have hle' : (⊤ : (Limits.pullback g C).Opens) ≤ (π ≫ C) ⁻¹ᵁ V := by
      rw [← pullback.condition]
      exact hle
    calc g.app V ≫ ι₁.appLE (g ⁻¹ᵁ V) ⊤ hle = (ι₁ ≫ g).appLE V ⊤ hle :=
          (Hom.comp_appLE ι₁ g V ⊤ hle).symm
      _ = (π ≫ C).appLE V ⊤ hle' := key _ _ pullback.condition _ _
      _ = _ := by
        rw [Hom.app_eq_appLE π, Hom.appLE_comp_appLE]
        rfl
  let i : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let j : Γ(M, ⊤) ≃+ Γ(Limits.pullback g C, ⊤) :=
    AddEquiv.ofBijective κ.hom.toAddMonoidHom hκbij
  let := π.appTop.hom.toAlgebra
  have hj : ∀ (a : R) (x : Γ(M, ⊤)), j (a • x) = i a • j x := by
    intro a x
    rw [smul_Spec_def]
    have : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
      rw [show (⊤ : (Spec R).Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
    rw [this]
    change κ (g.app V ((C.appIso ⊤).inv ((ΓSpecIso R).inv a)) * (show Γ(X, g ⁻¹ᵁ V) from x)) =
      π.appTop ((ΓSpecIso R).inv a) * κ (show Γ(X, g ⁻¹ᵁ V) from x)
    rw [map_mul, ← hκ]
    rfl
  have hcomap : PrimeSpectrum.comap (i : R →+* Γ(Spec R, ⊤)) ((Spec R).isoSpec.hom s₀) = s₀ := by
    rw [isoSpec_Spec_hom, Spec.map_apply]
    apply PrimeSpectrum.ext
    ext a
    change (ΓSpecIso R).hom ((ΓSpecIso R).inv a) ∈ s₀.asIdeal ↔ a ∈ s₀.asIdeal
    rw [Iso.inv_hom_id_apply]
  have hrank : g.finrank η = Module.rankAtStalk (R := R) Γ(M, ⊤) ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [h1, ← (hcomap.trans (PrimeSpectrum.ext (x := s₀) (y := ⟨⊥, Ideal.isPrime_bot⟩) hs₀bot) :)]
    exact (Module.rankAtStalk_comap_ringEquiv i j hj ((Spec R).isoSpec.hom s₀)).symm
  -- Generic freeness of the finite `R`-module `Γ(Spec R, g_* 𝒪_X)`.
  have : Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤) := by
    have h1 := g.finite_app V (by
      change IsAffineOpen (C ''ᵁ ⊤)
      rw [Hom.image_top_eq_opensRange]
      exact isAffineOpen_opensRange C)
    have h2 := RingHom.Finite.comp h1 (RingHom.Finite.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (C.appIso ⊤).inv).2))
    let := (CommRingCat.Hom.hom ((C.appIso ⊤).inv ≫ g.app V)).toAlgebra
    exact (h2 : Module.Finite Γ(Spec R, ⊤) Γ(X, g ⁻¹ᵁ V))
  have := finite_sections_top_of_finite M
  obtain ⟨r, hr, hfree, hfin⟩ :=
    Module.Finite.exists_free_localizedModule_powers_of_isDomain (A := R) (M := Γ(M, ⊤))
  have : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have : Module.Finite (Localization.Away r) (LocalizedModule.Away r Γ(M, ⊤)) :=
    Module.Finite.of_isLocalizedModule (.powers r) (LocalizedModule.mkLinearMap _ _)
  let b := Module.finBasisOfFinrankEq _ _ (hfin.trans hrank.symm)
  obtain ⟨E⟩ := nonempty_restrict_iso_free_of_localizedModule M r
    (b.repr ≪≫ₗ Finsupp.domLCongr Equiv.ulift.symm)
  -- Transport the isomorphism on `D(r) ⊆ Spec R` to the open subscheme `U = C(D(r))` of `Y`.
  let jr := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let f := jr ≫ C
  refine ⟨f.opensRange, ?_, ⟨?_⟩⟩
  · obtain ⟨x⟩ : Nonempty (Spec (.of (Localization.Away r))) := inferInstance
    exact ⟨f x, x, rfl⟩
  · have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin (g.finrank η))))
        (Modules.pullback f.isoOpensRange.inv) := inferInstance
    exact (Modules.pullbackCongr (by simp [f])).app F ≪≫
      ((Modules.pullbackComp f.isoOpensRange.inv f).symm.app F) ≪≫
      (Modules.pullback f.isoOpensRange.inv).mapIso
        ((restrictFunctorIsoPullback f).symm.app F ≪≫ (restrictFunctorComp jr C).app F ≪≫ E) ≪≫
      (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ (Modules.pullback f.isoOpensRange.inv)
        (ULift.{u} (Fin (g.finrank η))) this (pullbackObjUnitIso _).symm).symm

/-- **Pushforward of finite locally free modules along finite flat morphisms.** If `g : X ⟶ Y`
is finite, flat and locally of finite presentation and `ℱ` is a finite locally free
`𝒪_X`-module, then `g_* ℱ` is a finite locally free `𝒪_Y`-module. -/
theorem isFiniteLocallyFree_pushforward (g : X ⟶ Y) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (ℱ : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) ℱ] :
    SheafOfModules.IsFiniteLocallyFree (R := Y.ringCatSheaf) ((pushforward g).obj ℱ) := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree ℱ
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree ℱ
  have := isQuasicoherent_pushforward_of_isAffineHom g ℱ
  refine isFiniteLocallyFree_of_isAffineOpen _ fun V hV ↦ ?_
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections ℱ hV'
  -- `Γ(g_* ℱ, V) = Γ(ℱ, g ⁻¹ᵁ V)` is a module over `Γ(X, g ⁻¹ᵁ V)`, a `Γ(Y, V)`-algebra via `g`.
  let := (g.app V).hom.toAlgebra
  let : Module Γ(X, g ⁻¹ᵁ V) Γ((pushforward g).obj ℱ, V) :=
    inferInstanceAs (Module Γ(X, g ⁻¹ᵁ V) Γ(ℱ, g ⁻¹ᵁ V))
  have : Module.FinitePresentation Γ(X, g ⁻¹ᵁ V) Γ((pushforward g).obj ℱ, V) := hfp
  have : Module.Projective Γ(X, g ⁻¹ᵁ V) Γ((pushforward g).obj ℱ, V) := hproj
  have : IsScalarTower Γ(Y, V) Γ(X, g ⁻¹ᵁ V) Γ((pushforward g).obj ℱ, V) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Finite Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := g.finite_app V hV
  have : Algebra.FinitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := by
    have := g.finitePresentation_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have : Module.Flat Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := by
    have := g.flat_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have : Module.FinitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V) :=
    .of_finite_of_finitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V)
  exact ⟨.trans Γ(Y, V) Γ((pushforward g).obj ℱ, V) Γ(X, g ⁻¹ᵁ V),
    .trans Γ(Y, V) Γ(X, g ⁻¹ᵁ V) Γ((pushforward g).obj ℱ, V)⟩

/-- **The pushforward of the structure sheaf along a finite locally free morphism.** If
`g: X ⟶ Y` is finite locally free of degree `d`, then `g_* 𝒪_X` is a finite locally free
`𝒪_Y`-module of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_pushforward_unit (g : X ⟶ Y) (d : ℕ)
    [g.IsFiniteLocallyFreeOfDegree d] :
    ((pushforward g).obj (𝟙_ X.Modules)).IsFiniteLocallyFreeOfRank d := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : ((pushforward g).obj (𝟙_ X.Modules)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom g _
  refine isFiniteLocallyFreeOfRank_of_isAffineOpen _ fun V hV ↦ ?_
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  let := (g.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := g.finite_app V hV
  have : Algebra.FinitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := by
    have := g.finitePresentation_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have hfl : Module.Flat Γ(Y, V) Γ(X, g ⁻¹ᵁ V) := by
    have := g.flat_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have hfp : Module.FinitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V) :=
    .of_finite_of_finitePresentation Γ(Y, V) Γ(X, g ⁻¹ᵁ V)
  -- `Spec Γ(X, g ⁻¹ᵁ V) ⟶ Spec Γ(Y, V)` is the base change of `g` along `Spec Γ(Y, V) ⟶ Y`.
  have hpb : IsPullback hV'.fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(X, g ⁻¹ᵁ V)))) g hV.fromSpec := by
    refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
    · rw [← IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' le_rfl, ← Hom.app_eq_appLE]
      rfl
    · rw [hV.opensRange_fromSpec, hV'.opensRange_fromSpec]
  refine ⟨hfp, hfl, fun p ↦ ?_⟩
  calc Module.rankAtStalk Γ(X, g ⁻¹ᵁ V) p = p.asIdeal.fiberDegree Γ(X, g ⁻¹ᵁ V) :=
        Module.rankAtStalk_eq p
    _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(X, g ⁻¹ᵁ V)))).fiberDegree p :=
        (Hom.fiberDegree_SpecMap _ _ p).symm
    _ = g.fiberDegree (hV.fromSpec p) := g.fiberDegree_of_isPullback hpb p
    _ = d := Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq _

end AlgebraicGeometry.Scheme.Modules
