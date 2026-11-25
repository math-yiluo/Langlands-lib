/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite locally free modules over affine opens

Let `M` be a finite locally free `𝒪_X`-module and `U` an affine open of the scheme `X`. Then the
sections `Γ(M, U)` form a finitely presented projective `Γ(X, U)`-module, and `M|_U` is a direct
summand of a free module of finite rank.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_mem_over_iso_free`: a finite locally free module is
  free of finite rank on a neighbourhood of every point.
- `AlgebraicGeometry.Scheme.Modules.finitePresentation_projective_sections`: the sections of a
  finite locally free module over an affine open are a finitely presented projective module.
- `AlgebraicGeometry.Scheme.Modules.exists_sum_comp_eq_id_over`: over an affine open `U`, `M|_U`
  is a direct summand of `𝒪_U^n`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isAffineOpen`: conversely, a
  quasi-coherent module whose sections over affine opens are finitely presented and flat is finite
  locally free.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen`: a morphism of
  `𝒪_X`-modules is an isomorphism if it is bijective on sections over affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A finite locally free `𝒪_X`-module is free of finite rank on a neighbourhood of every
point. -/
lemma exists_mem_over_iso_free (M : X.Modules) [M.IsFiniteLocallyFree] (x : X) :
    ∃ (Y : X.Opens) (I : Type u) (_ : Fintype I), x ∈ Y ∧
      Nonempty (M.over Y ≅ SheafOfModules.free I) := by
  obtain ⟨q, hq, hf⟩ := SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hx⟩ := q.coversTop ⊤ x trivial
  have := hf.isFiniteType i
  have := hq.isIso i
  exact ⟨q.X i, (q.generators i).I, Fintype.ofFinite _, g.le hx,
    ⟨(asIso (q.generators i).π).symm⟩⟩

/-- A trivialisation `M.over Y ≅ 𝒪_Y^I` of an `𝒪_X`-module over an open `Y` gives, for every open
`W ≤ Y`, a `Γ(X, W)`-linear isomorphism `Γ(M, W) ≃ Γ(X, W)^I`. -/
noncomputable def sectionsLinearEquivOfOverIsoFree {M : X.Modules} {Y : X.Opens} {I : Type u}
    [Fintype I] [DecidableEq I] (e : M.over Y ≅ SheafOfModules.free I) {W : X.Opens}
    (h : W ≤ Y) : Γ(M, W) ≃ₗ[Γ(X, W)] (I → Γ(X, W)) :=
  SheafOfModules.sectionsLinearEquivOfIsoFree e (op (Over.mk (homOfLE h)))

/-- **Sections of finite locally free modules over affine opens.** The sections `Γ(M, U)` of a
finite locally free `𝒪_X`-module over an affine open `U` form a finitely presented projective
`Γ(X, U)`-module: they localize to the free modules `Γ(M, D(g))` over the basic opens `D(g)` on
which `M` is trivial. -/
theorem finitePresentation_projective_sections (M : X.Modules) [M.IsFiniteLocallyFree]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(M, U) ∧ Module.Projective Γ(X, U) Γ(M, U) := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree M
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree M
  let s : Set Γ(X, U) := {g | ∃ (Y : X.Opens) (I : Type u) (_ : Fintype I),
    X.basicOpen g ≤ Y ∧ Nonempty (M.over Y ≅ SheafOfModules.free I)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨Y, I, _, hxY, ⟨e⟩⟩ := exists_mem_over_iso_free M x
    obtain ⟨g, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, Y, I, inferInstance, hgY, ⟨e⟩⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(M, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen M hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  have hfree (r : s) : Module.Free Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) ∧
      Module.FinitePresentation Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) := by
    obtain ⟨Y, I, _, hY, ⟨e⟩⟩ := r.2
    classical
    let e' := sectionsLinearEquivOfOverIsoFree e hY
    exact ⟨Module.Free.of_equiv e'.symm, Module.FinitePresentation.of_equiv e'.symm⟩
  let ϕ (r : s) : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen r.1) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
      map_add' := map_add _
      map_smul' := map_smul M _ }
  have hfp : Module.FinitePresentation Γ(X, U) Γ(M, U) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun r ↦ Γ(X, X.basicOpen r.1)) ϕ fun r ↦ (hfree r).2
  have : Module.Flat Γ(X, U) Γ(M, U) :=
    Module.flat_of_isLocalized_span Γ(X, U) Γ(M, U) s hs
      (fun r ↦ Γ(M, X.basicOpen r.1)) ϕ fun r ↦ by
        have := (hfree r).1
        have := IsLocalization.flat Γ(X, X.basicOpen r.1) (.powers r.1)
        exact Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

set_option backward.isDefEq.respectTransparency false in
/-- For an affine open `U`, the global sections of the restriction of `M` to `Spec Γ(X, U)` are
`Γ(M, U)`, as `Γ(X, U)`-modules. -/
noncomputable def sectionsRestrictFromSpecLinearEquiv (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) :
    moduleSpecΓFunctor.obj (M.restrict hU.fromSpec) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  have h₁ : U ≤ hU.fromSpec ''ᵁ ⊤ :=
    (hU.opensRange_fromSpec.symm.trans (Hom.image_top_eq_opensRange _).symm).le
  have h₂ : hU.fromSpec ''ᵁ ⊤ ≤ U := hU.fromSpec_image_le ⊤
  have hid (y : Γ(M, U)) :
      M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op y) = y := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have hid' (y : Γ(M, hU.fromSpec ''ᵁ ⊤)) :
      M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op y) = y := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have hr (r : Γ(X, U)) :
      X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op r) = r := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  exact
    { toFun x := M.presheaf.map (homOfLE h₁).op ((M.restrictAppIso hU.fromSpec ⊤).hom x)
      invFun y := (M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (homOfLE h₂).op y)
      map_add' x y := by simp only [map_add]
      map_smul' r x := by
        change M.presheaf.map (homOfLE h₁).op ((M.restrictAppIso hU.fromSpec ⊤).hom
          (r • (x : Γ(M.restrict hU.fromSpec, ⊤)))) = _
        rw [restrictAppIso_fromSpec_smul, Scheme.Modules.map_smul, hr]
        rfl
      left_inv x := by
        dsimp only
        rw [hid']
        exact (M.restrictAppIso hU.fromSpec ⊤).hom_inv_id_apply x
      right_inv y := by
        dsimp only
        rw [Iso.inv_hom_id_apply, hid] }

/-- **Finite locally free modules are summands of free modules on affine opens.** The
restriction of a finite locally free `𝒪_X`-module `M` to the spectrum of an affine open `U` is a
direct summand of a free module of finite rank: there are `ξⱼ : M ⟶ 𝒪` and `mⱼ : 𝒪 ⟶ M` with
`∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. Indeed `M|_U` is `Γ(M, U)^~`, and `Γ(M, U)` is finite projective
(`finitePresentation_projective_sections`). -/
theorem exists_sum_comp_eq_id_restrict_fromSpec (M : X.Modules) [M.IsFiniteLocallyFree]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (ξ : Fin n → (M.restrict hU.fromSpec ⟶ SheafOfModules.unit _))
      (m : Fin n → (SheafOfModules.unit _ ⟶ M.restrict hU.fromSpec)),
      ∑ j, ξ j ≫ m j = 𝟙 _ := by
  have := SheafOfModules.IsFiniteLocallyFree.isLocallyFree M
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree M
  let N := M.restrict hU.fromSpec
  have hiso : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  let e := sectionsRestrictFromSpecLinearEquiv M hU
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections M hU
  have : Module.Finite Γ(X, U) (moduleSpecΓFunctor.obj N) := Module.Finite.equiv e.symm
  have : Module.Projective Γ(X, U) (moduleSpecΓFunctor.obj N) := Module.Projective.of_equiv e.symm
  obtain ⟨n, ξ₀, m₀, h₀⟩ := ModuleCat.exists_sum_comp_eq_id_of_projective (R := Γ(X, U))
    (moduleSpecΓFunctor.obj N)
  exact CategoryTheory.Functor.exists_sum_comp_eq_id_of_iso (tilde.functor Γ(X, U))
    (@asIso _ _ _ _ N.fromTildeΓ hiso) tildeSelf ⟨n, ξ₀, m₀, h₀⟩

/-- A morphism of `𝒪_X`-modules which is bijective on sections over every affine open is an
isomorphism. -/
lemma isIso_of_bijective_app_of_isAffineOpen {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ V : X.Opens, IsAffineOpen V → Function.Bijective (φ.app V)) : IsIso φ := by
  let F : TopCat.Sheaf Ab X := ⟨A.presheaf, A.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨B.presheaf, B.isSheaf⟩
  let ψ : F ⟶ G := Sheaf.homEquiv.symm ((Modules.toPresheaf X).map φ)
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (fun V : X.affineOpens ↦ (V : X.Opens))) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB fun V ↦
    (ConcreteCategory.isIso_iff_bijective _).2 (h V V.2)
  have : IsIso ((Modules.toPresheaf X).map φ) := by
    obtain ⟨g, hg₁, hg₂⟩ := hψ.out
    exact ⟨g.hom, congrArg (fun a ↦ a.hom) hg₁, congrArg (fun a ↦ a.hom) hg₂⟩
  exact isIso_of_reflects_iso φ (Modules.toPresheaf X)

/-- **Finite locally free modules are summands of free modules over affine opens.** The
restriction `M.over U` of a finite locally free `𝒪_X`-module to an affine open `U` is a direct
summand of a free module of finite rank: there are `ξⱼ : M|_U ⟶ 𝒪_U` and `mⱼ : 𝒪_U ⟶ M|_U` with
`∑ⱼ ξⱼ ≫ mⱼ = 𝟙`. -/
theorem exists_sum_comp_eq_id_over (M : X.Modules) [M.IsFiniteLocallyFree] {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (ξ : Fin n → (M.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U))
      (m : Fin n → ((SheafOfModules.unit X.ringCatSheaf).over U ⟶ M.over U)),
      ∑ j, ξ j ≫ m j = 𝟙 _ := by
  have : (restrictFunctor hU.isoSpec.hom).Additive :=
    Functor.additive_of_iso (restrictFunctorIsoPullback _).symm
  have : HasBinaryBiproducts (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts (overEquiv U).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (overEquiv U).inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact Functor.exists_sum_comp_eq_id_of_iso
    (restrictFunctor hU.isoSpec.hom ⋙ (overEquiv U).inverse)
    ((overEquiv U).inverse.mapIso ((restrictCompIso M hU.fromSpec hU.isoSpec.hom U.ι
      hU.isoSpec_hom_fromSpec).symm ≪≫ ((overFunctorEquiv U).app M).symm) ≪≫
        ((overEquiv U).unitIso.app (M.over U)).symm)
    ((overEquiv U).inverse.mapIso (restrictUnitIso hU.isoSpec.hom ≪≫
      overEquivFunctorObjUnitIso U) ≪≫ ((overEquiv U).unitIso.app _).symm)
    (exists_sum_comp_eq_id_restrict_fromSpec M hU)

/-- **Finite local freeness from sections over affine opens.** A quasi-coherent `𝒪_X`-module whose
sections over every affine open `U` form a finitely presented flat `Γ(X, U)`-module is finite
locally free: around a point of `U` some localization `Γ(M, U)_r` is free of finite rank, so `M`
is free of finite rank on the basic open `D(r)`. -/
theorem isFiniteLocallyFree_of_isAffineOpen (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ U : X.Opens, IsAffineOpen U →
      Module.FinitePresentation Γ(X, U) Γ(M, U) ∧ Module.Flat Γ(X, U) Γ(M, U)) :
    M.IsFiniteLocallyFree := by
  have key (x : X) : ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsOpenImmersion f) (κ : Type u)
      (_ : Finite κ), x ∈ f.opensRange ∧ Nonempty (M.restrict f ≅ SheafOfModules.free κ) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    replace hU : IsAffineOpen U := hU
    obtain ⟨hfp, hfl⟩ := h U hU
    let N := M.restrict hU.fromSpec
    have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
    let e := sectionsRestrictFromSpecLinearEquiv M hU
    let S := moduleSpecΓFunctor.obj N
    have : Module.FinitePresentation Γ(X, U) S := Module.FinitePresentation.of_equiv e.symm
    have : Module.Flat Γ(X, U) S := Module.Flat.of_linearEquiv e
    let p := hU.primeIdealOf ⟨x, hxU⟩
    obtain ⟨r, hr, hfree, hfin⟩ :=
      Module.exists_free_localizedModule_powers_of_flat (R := Γ(X, U)) (M := S) p.asIdeal
    let jr := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))
    obtain ⟨E⟩ := nonempty_restrict_iso_free_of_localizedModule N r
      (Module.Free.chooseBasis (Localization.Away r) (LocalizedModule.Away r S)).repr
    refine ⟨_, jr ≫ hU.fromSpec, inferInstance, _, inferInstance, ?_,
      ⟨(restrictFunctorComp jr hU.fromSpec).app M ≪≫ E⟩⟩
    have hp : p ∈ jr.opensRange := by
      rw [Hom.opensRange_localizationAway]
      exact hr
    obtain ⟨q, hq⟩ := hp
    refine ⟨q, (Hom.comp_apply _ _ q).trans ?_⟩
    exact (congrArg hU.fromSpec hq).trans (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)
  choose Y f hf κ hκ hx e using key
  exact isFiniteLocallyFree_of_restrict_iso_free M f
    (eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩) κ e

end AlgebraicGeometry.Scheme.Modules
