/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.Modules.FpqcFullyFaithful
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-!
# Fpqc descent of finite presentation and of finite local freeness

Let `{g i : T' i ⟶ T}` be an fpqc covering and `M` a quasi-coherent module on `T` whose descent
datum relative to the covering is isomorphic to `D`. We show that `M` is of finite presentation
if the components of `D` are, and that `M` is locally free if the components of `D` are of finite
presentation and locally free.

## Main results

- `AlgebraicGeometry.isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent`
- `AlgebraicGeometry.isLocallyFree_of_toDescentData_iso_of_isQuasicoherent`

Along the way we prove, for modules on schemes:

- `AlgebraicGeometry.Scheme.Modules.finitePresentation_sections_of_isFinitePresentation`: the
  sections of a module of finite presentation over an affine open are finitely presented;
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pullback`: stability under pullback;
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_of_isOpenImmersion` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isOpenImmersion`: locality for covers
  by open immersions;
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFinitePresentation_of_isLocallyFree`:
  a locally free module of finite presentation is finite locally free.

## Proofs

The structure follows the proof of fpqc descent of finite local freeness of a fixed rank
(`AlgebraicGeometry.isFiniteLocallyFreeOfRank_of_toDescentData_iso_of_isQuasicoherent`). Over an
affine open `U` of `T`, the covering is refined by finitely many flat affine schemes, whose
disjoint union is `Spec B` for a faithfully flat `Γ(T, U)`-algebra `B`. The global sections of the
pullback of `M` to `Spec B` are `B ⊗ Γ(M, U)`, and finite presentation and flatness descend along
`Γ(T, U) → B`. A quasi-coherent module on an affine scheme with finitely presented global sections
has a finite global presentation, and one with finitely presented flat sections over all affine
opens is finite locally free.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- **Sections of a module with a finite presentation on an affine scheme.** If `M ≅ Γ(M)^~` on
`Spec R` has a finite global presentation, then `Γ(M, ⊤)` is a finitely presented `R`-module:
it is the cokernel of the map `R^J → R^I` corresponding to the relations, since `~` is fully
faithful and preserves cokernels. -/
theorem finitePresentation_sections_top_of_presentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (P : M.Presentation) [P.IsFinite] :
    Module.FinitePresentation R Γ(M, ⊤) := by
  let F := tilde.functor R
  let f := (SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  let f₀ : ModuleCat.of R (P.relations.I →₀ R) ⟶ ModuleCat.of R (P.generators.I →₀ R) :=
    F.preimage ((tildeFinsupp _).hom ≫ f ≫ (tildeFinsupp _).inv)
  let e₁ : F.obj (cokernel f₀) ≅ cokernel (F.map f₀) := PreservesCokernel.iso F f₀
  let e₂ : cokernel (F.map f₀) ≅ cokernel f :=
    cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) (by
      refine (F.map_preimage _ =≫ _).trans ?_
      simp)
  let e₃ : cokernel f ≅ M := (colimit.isColimit _).coconePointUniqueUpToIso P.isColimit
  let e₄ : M ≅ F.obj (moduleSpecΓFunctor.obj M) := (asIso M.fromTildeΓ).symm
  let e : cokernel f₀ ≅ moduleSpecΓFunctor.obj M := F.preimageIso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄)
  have : Module.FinitePresentation R (cokernel (C := ModuleCat R) f₀) := by
    have : Module.FinitePresentation R (_ ⧸ LinearMap.range f₀.hom) :=
      Module.finitePresentation_of_surjective (LinearMap.range f₀.hom).mkQ
        (Submodule.mkQ_surjective _) (by
          rw [Submodule.ker_mkQ]
          exact Module.Finite.iff_fg.mp inferInstance)
    exact .of_equiv (ModuleCat.cokernelIsoRangeQuotient f₀).toLinearEquiv.symm
  exact .of_equiv e.toLinearEquiv

variable {X Y : Scheme.{u}}

/-- **The sections of a module of finite presentation over an affine open are finitely
presented.** Let `F` be an `𝒪_X`-module of finite presentation and `U` an affine open. Then
`Γ(F, U)` is a finitely presented `Γ(X, U)`-module: `U` is covered by basic opens `D(g)` over
which `F` has a finite presentation, so that `Γ(F, D(g))` is finitely presented over
`Γ(X, D(g))`, and finite presentation descends along the localizations `Γ(F, U) → Γ(F, D(g))`. -/
theorem finitePresentation_sections_of_isFinitePresentation (F : X.Modules)
    [F.IsFinitePresentation] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := X.ringCatSheaf) F
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  let s : Set Γ(X, U) :=
    {g | Module.FinitePresentation Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hi⟩ hx
    have hV := hU.basicOpen g
    let P := presentationRestrictOfOver (q.presentation i) hV.fromSpec
      (hV.opensRange_fromSpec.le.trans hgW)
    have : (F.restrict hV.fromSpec).IsQuasicoherent :=
      isQuasicoherent_restrictFunctor hV.fromSpec F
    have : IsIso (F.restrict hV.fromSpec).fromTildeΓ :=
      isIso_fromTildeΓ_of_isQuasicoherent _
    have : Module.FinitePresentation Γ(X, X.basicOpen g)
        (moduleSpecΓFunctor.obj (F.restrict hV.fromSpec)) :=
      finitePresentation_sections_top_of_presentation _ P
    exact Opens.mem_iSup.mpr
      ⟨⟨g, .of_equiv (sectionsRestrictFromSpecLinearEquiv F hV)⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen F hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.FinitePresentation.of_localizationSpan' s hs
    (Rₚ := fun r : s ↦ Γ(X, X.basicOpen r.1)) (fun r ↦
      { toFun := F.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul F _ }) fun r ↦ r.2

end AlgebraicGeometry.Scheme.Modules

namespace Module

/-- Finite presentation can be transported along a ring isomorphism `e : R ≃+* R'` compatible
with the actions of `R` and `R'` on `M`. -/
theorem FinitePresentation.of_ringEquiv {R R' M : Type*} [CommRing R] [CommRing R']
    [AddCommGroup M] [Module R M] [Module R' M] (e : R ≃+* R')
    (he : ∀ (a : R) (m : M), a • m = e a • m) [Module.FinitePresentation R' M] :
    Module.FinitePresentation R M := by
  let := e.toRingHom.toAlgebra
  have : IsScalarTower R R' M := ⟨fun a b m ↦ by
    rw [Algebra.smul_def, mul_smul, he]
    rfl⟩
  let h : R ≃ₐ[R] R' := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have : Module.FinitePresentation R R' := .of_equiv h.toLinearEquiv
  have : IsLocalization (⊥ : Submonoid R) R :=
    IsLocalization.self bot_le
  have : IsLocalization (⊥ : Submonoid R) R' := IsLocalization.isLocalization_of_algEquiv ⊥ h
  have := isLocalizedModule_id (⊥ : Submonoid R) M R'
  exact .trans R M R'

end Module

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Finite presentation of `𝒪_X`-modules is invariant under isomorphism. -/
theorem isFinitePresentation_of_iso {M N : X.Modules} (e : M ≅ N) [M.IsFinitePresentation] :
    N.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e inferInstance

/-- Finite local freeness of `𝒪_X`-modules is invariant under isomorphism. -/
theorem isFiniteLocallyFree_of_iso {M N : X.Modules} (e : M ≅ N) [M.IsFiniteLocallyFree] :
    N.IsFiniteLocallyFree :=
  SheafOfModules.IsFiniteLocallyFree.of_iso (R := X.ringCatSheaf) e

/-- The global sections of a module of finite presentation on `Spec R` are a finitely presented
`R`-module. -/
theorem finitePresentation_sections_top {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsFinitePresentation] : Module.FinitePresentation R Γ(M, ⊤) :=
  have := finitePresentation_sections_of_isFinitePresentation M (isAffineOpen_top (Spec R))
  Module.FinitePresentation.of_ringEquiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv (smul_top_eq M)

/-- The global sections of a finite locally free module on `Spec R` are a finitely presented flat
`R`-module. -/
theorem finitePresentation_flat_sections_top_of_isFiniteLocallyFree {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsFiniteLocallyFree] :
    Module.FinitePresentation R Γ(M, ⊤) ∧ Module.Flat R Γ(M, ⊤) := by
  obtain ⟨_, _⟩ := finitePresentation_projective_sections M (isAffineOpen_top (Spec R))
  obtain ⟨h₁, h₂, -⟩ := Module.finitePresentation_flat_rankAtStalk_of_ringEquiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv (smul_top_eq M)
  exact ⟨h₁, h₂⟩

/-- A quasi-coherent module on `Spec R` whose global sections are a finitely presented `R`-module
has a finite global presentation: it is `M^~` for the module `M` of its global sections. -/
theorem exists_presentation_isFinite_of_finitePresentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Module.FinitePresentation R Γ(M, ⊤)] :
    ∃ P : M.Presentation, P.IsFinite := by
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  have : Module.FinitePresentation R N := ‹Module.FinitePresentation R Γ(M, ⊤)›
  obtain ⟨s, hs, t, ht⟩ := this.out
  have : IsIso (C := SheafOfModules.{u} (Spec R).ringCatSheaf) M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨(presentationTilde N (s : Set N) hs (t : Set _) ht).ofIsIso M.fromTildeΓ,
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set N))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }⟩

/-- A module of finite presentation has finite global presentations over the members of an open
cover. -/
theorem exists_isOpenCover_presentation_isFinite (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens) (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ ∀ i, (P i).IsFinite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := X.ringCatSheaf) M
  exact ⟨q.I, q.X, fun i ↦ presentationRestrictOfOver (q.presentation i)
    (Scheme.Opens.ι (q.X i)) (by simp), (Opens.coversTop_iff _ q.X).mp q.coversTop,
    fun i ↦ inferInstance⟩

/-- **The pullback of a module of finite presentation is of finite presentation.** Finite
presentations of `M` over the members `U i` of an open cover of `Y` pull back along the
restrictions `g ∣_ U i` to finite presentations of `g^* M` over the open cover `g ⁻¹ᵁ U i`. -/
instance isFinitePresentation_pullback (g : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((Modules.pullback g).obj M).IsFinitePresentation := by
  obtain ⟨ι, U, pres, hU, hfin⟩ := exists_isOpenCover_presentation_isFinite M
  have (i : ι) : PreservesColimitsOfSize.{u, u} (Modules.pullback (g ∣_ U i)) := inferInstance
  let P (i : ι) : (((Modules.pullback g).obj M).restrict (g ⁻¹ᵁ U i).ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      ((restrictFunctorIsoPullback _).app _ ≪≫ (Modules.pullbackComp (g ⁻¹ᵁ U i).ι g).app M ≪≫
        (Modules.pullbackCongr (morphismRestrict_ι g (U i)).symm).app M ≪≫
        ((Modules.pullbackComp (g ∣_ U i) (U i).ι).symm).app M ≪≫
        (Modules.pullback (g ∣_ U i)).mapIso ((restrictFunctorIsoPullback _).app M).symm).inv
      ((pres i).map (Modules.pullback (g ∣_ U i)) (pullbackObjUnitIso _).symm)
  have (i : ι) : (P i).IsFinite := by
    dsimp only [P]
    infer_instance
  refine isFinitePresentation_of_isOpenCover _ (U := fun i ↦ g ⁻¹ᵁ U i) ?_ P
  refine IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨i, hi⟩ := hU.exists_mem (g.base x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- **Finite presentation is local** for a family of open immersions covering `X`: if the
pullbacks of `M` along them are of finite presentation, so is `M`. -/
theorem isFinitePresentation_of_isOpenImmersion (M : X.Modules) {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, ((Modules.pullback (f i)).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have (i : ι) : (M.restrict (f i)).IsFinitePresentation :=
    have := h i
    isFinitePresentation_of_iso ((restrictFunctorIsoPullback (f i)).app M).symm
  choose κ W P hW hP using fun i ↦ exists_isOpenCover_presentation_isFinite (M.restrict (f i))
  refine isFinitePresentation_of_iSup_opensRange_eq_top M
    (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ f j.1) ?_ fun j ↦
      (P j.1 j.2).ofIsIso ((restrictFunctorComp (W j.1 j.2).ι (f j.1)).app M).inv
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hf.ge (Set.mem_univ x) : x ∈ ⨆ i, (f i).opensRange)
  obtain ⟨y, rfl⟩ := hi
  obtain ⟨k, hk⟩ := (hW i).exists_mem y
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, k⟩, ⟨⟨y, hk⟩, rfl⟩⟩

/-- A finite locally free module is free of finite rank on an open neighbourhood of every
point. -/
theorem exists_restrict_iso_free_of_isFiniteLocallyFree (M : X.Modules) [M.IsFiniteLocallyFree]
    (x : X) : ∃ (U : X.Opens) (κ : Type u), Finite κ ∧ x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.free κ) := by
  obtain ⟨U, I, _, hx, ⟨e⟩⟩ := exists_mem_over_iso_free M x
  exact ⟨U, I, inferInstance, hx, ⟨overIsoFreeEquiv M U I e⟩⟩

/-- The pullback of a finite locally free module is finite locally free. -/
instance isFiniteLocallyFree_pullback (g : Y ⟶ X) (M : X.Modules) [M.IsFiniteLocallyFree] :
    ((Modules.pullback g).obj M).IsFiniteLocallyFree := by
  choose U κ hκ hx e using exists_restrict_iso_free_of_isFiniteLocallyFree M
  refine isFiniteLocallyFree_of_restrict_iso_free _ (fun y : Y ↦ (g ⁻¹ᵁ U (g y)).ι) ?_
    (fun y ↦ κ (g y)) fun y ↦
    ⟨(restrictFunctorIsoPullback (g ⁻¹ᵁ U (g y)).ι).app ((Modules.pullback g).obj M) ≪≫
      (Modules.pullbackComp (g ⁻¹ᵁ U (g y)).ι g).app M ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι g (U (g y))).symm).app M ≪≫
      (Modules.pullbackComp (g ∣_ U (g y)) (U (g y)).ι).symm.app M ≪≫
      (Modules.pullback (g ∣_ U (g y))).mapIso
        ((restrictFunctorIsoPullback (U (g y)).ι).symm.app M ≪≫ (e (g y)).some) ≪≫
      pullbackFreeIso _ _⟩
  refine eq_top_iff.2 fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, ?_⟩
  rw [Scheme.Opens.opensRange_ι]
  exact hx (g y)

/-- **Finite local freeness is local** for a family of open immersions covering `X`: if the
pullbacks of `M` along them are finite locally free, so is `M`. -/
theorem isFiniteLocallyFree_of_isOpenImmersion (M : X.Modules) {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤)
    (h : ∀ i, ((Modules.pullback (f i)).obj M).IsFiniteLocallyFree) :
    M.IsFiniteLocallyFree := by
  choose W κ hκ hW e using fun i ↦
    have := h i
    exists_restrict_iso_free_of_isFiniteLocallyFree ((Modules.pullback (f i)).obj M)
  refine isFiniteLocallyFree_of_restrict_iso_free M
    (fun j : Σ i, (Y i : Type u) ↦ (W j.1 j.2).ι ≫ f j.1) ?_ (fun j ↦ κ j.1 j.2) fun j ↦
      ⟨(restrictFunctorComp (W j.1 j.2).ι (f j.1)).app M ≪≫
        (restrictFunctor (W j.1 j.2).ι).mapIso ((restrictFunctorIsoPullback (f j.1)).app M) ≪≫
        (e j.1 j.2).some⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hf.ge (Set.mem_univ x) : x ∈ ⨆ i, (f i).opensRange)
  obtain ⟨y, rfl⟩ := hi
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, y⟩, ⟨⟨y, hW i y⟩, rfl⟩⟩

/-- If the restriction of `M` to an open `W` is free, so is its restriction along any open
immersion with image in `W`. -/
noncomputable def restrictIsoFreeOfOpensRangeLE {M : X.Modules} {W : X.Opens} {I : Type u}
    (e : M.restrict W.ι ≅ SheafOfModules.free I) (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : f.opensRange ≤ W) : M.restrict f ≅ SheafOfModules.free I :=
  let u : Y ⟶ W.toScheme := IsOpenImmersion.lift W.ι f (by
    rw [Scheme.Opens.range_ι]
    exact hf)
  haveI : IsOpenImmersion (u ≫ W.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  haveI : IsOpenImmersion u := IsOpenImmersion.of_comp u W.ι
  restrictCompIso M W.ι u f (IsOpenImmersion.lift_fac _ _ _) ≪≫ (restrictFunctor u).mapIso e ≪≫
    restrictFreeIso u I

/-- **A locally free module of finite presentation is finite locally free.** If `M` is free on
`I` over an affine open `V ∋ x`, then `Γ(M, V) ≅ Γ(X, V)^(I)` is a finite `Γ(X, V)`-module and
`Γ(X, V) ≠ 0`, so `I` is finite. -/
theorem isFiniteLocallyFree_of_isFinitePresentation_of_isLocallyFree (M : X.Modules)
    [M.IsFinitePresentation] [M.IsLocallyFree] : M.IsFiniteLocallyFree := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  have key (x : X) : ∃ (V : X.Opens) (hV : IsAffineOpen V) (I : Type u), Finite I ∧ x ∈ V ∧
      Nonempty (M.restrict hV.fromSpec ≅ SheafOfModules.free I) := by
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (q.X i).2
    replace hV : IsAffineOpen V := hV
    let I := (q.generators i).I
    let E : M.restrict hV.fromSpec ≅ SheafOfModules.free I :=
      restrictIsoFreeOfOpensRangeLE (overIsoFreeEquiv M (q.X i) I (asIso (q.generators i).π).symm)
        hV.fromSpec (by
          rw [hV.opensRange_fromSpec]
          exact hVi)
    have : Nontrivial Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).nontrivial
    have := finitePresentation_sections_of_isFinitePresentation M hV
    let e : (I →₀ Γ(X, V)) ≃ₗ[Γ(X, V)] Γ(M, V) :=
      (asIso (tilde.adjunction.unit.app (ModuleCat.of Γ(X, V) (I →₀ Γ(X, V)))) ≪≫
        moduleSpecΓFunctor.mapIso (tildeFinsupp I ≪≫ E.symm)).toLinearEquiv ≪≫ₗ
        sectionsRestrictFromSpecLinearEquiv M hV
    exact ⟨V, hV, I, Module.Finite.finite_basis (Finsupp.basisSingleOne.map e), hxV, ⟨E⟩⟩
  choose V hV I hI hx E using key
  refine isFiniteLocallyFree_of_restrict_iso_free M (fun x ↦ (hV x).fromSpec) ?_ I E
  refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨x, ?_⟩
  rw [(hV x).opensRange_fromSpec]
  exact hx x

/-- **Finite presentation descends along a faithfully flat map of affine schemes**
`Spec.map φ : Spec B ⟶ Spec R`, for quasi-coherent modules: the global sections of the pullback
are `B ⊗[R] Γ(P, ⊤)`, and finite presentation descends along `R ⟶ B`. -/
theorem finitePresentation_sections_top_of_pullback_Spec_map {R B : CommRingCat.{u}} (φ : R ⟶ B)
    [Flat (Spec.map φ)] [Surjective (Spec.map φ)] (P : (Spec R).Modules) [P.IsQuasicoherent]
    [((Modules.pullback (Spec.map φ)).obj P).IsFinitePresentation] :
    Module.FinitePresentation R Γ(P, ⊤) := by
  have hφ : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩
  have := finitePresentation_sections_top ((Modules.pullback (Spec.map φ)).obj P)
  have hfp : Module.FinitePresentation B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) :=
    .of_equiv (pullbackSpecΓEquiv φ P).symm
  algebraize [φ.hom]
  have : Module.FinitePresentation B (TensorProduct R B Γ(P, ⊤)) := by exact hfp
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat (B := B)

/-- **Flatness descends along a faithfully flat map of affine schemes**
`Spec.map φ : Spec B ⟶ Spec R`, for quasi-coherent modules whose pullback is finite locally
free. -/
theorem flat_sections_top_of_pullback_Spec_map {R B : CommRingCat.{u}} (φ : R ⟶ B)
    [Flat (Spec.map φ)] [Surjective (Spec.map φ)] (P : (Spec R).Modules) [P.IsQuasicoherent]
    [((Modules.pullback (Spec.map φ)).obj P).IsFiniteLocallyFree] :
    Module.Flat R Γ(P, ⊤) := by
  have hφ : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨‹_›, ‹_›⟩
  obtain ⟨-, _⟩ :=
    finitePresentation_flat_sections_top_of_isFiniteLocallyFree
      ((Modules.pullback (Spec.map φ)).obj P)
  have hfl : Module.Flat B
      ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P)) :=
    .of_linearEquiv (pullbackSpecΓEquiv φ P)
  algebraize [φ.hom]
  have : Module.Flat B (TensorProduct R B Γ(P, ⊤)) := by exact hfl
  exact .of_flat_tensorProduct _ _ B

/-- Descent of finite presentation along a flat surjective morphism `F : W ⟶ Spec R` from an
affine scheme, for quasi-coherent modules on `Spec R`. -/
theorem finitePresentation_sections_top_of_pullback_of_isAffine {R : CommRingCat.{u}}
    {W : Scheme.{u}} [IsAffine W] (F : W ⟶ Spec R) [Flat F] [Surjective F]
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [((Modules.pullback F).obj P).IsFinitePresentation] :
    Module.FinitePresentation R Γ(P, ⊤) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ F)
  have : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : ((Modules.pullback (Spec.map φ)).obj P).IsFinitePresentation :=
    isFinitePresentation_of_iso
      (pullbackCompOfEq W.isoSpec.inv F _ hφ.symm P)
  exact finitePresentation_sections_top_of_pullback_Spec_map φ P

/-- Descent of flatness along a flat surjective morphism `F : W ⟶ Spec R` from an affine scheme,
for quasi-coherent modules on `Spec R` whose pullback is finite locally free. -/
theorem flat_sections_top_of_pullback_of_isAffine {R : CommRingCat.{u}}
    {W : Scheme.{u}} [IsAffine W] (F : W ⟶ Spec R) [Flat F] [Surjective F]
    (P : (Spec R).Modules) [P.IsQuasicoherent]
    [((Modules.pullback F).obj P).IsFiniteLocallyFree] :
    Module.Flat R Γ(P, ⊤) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ F)
  have : Flat (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : ((Modules.pullback (Spec.map φ)).obj P).IsFiniteLocallyFree :=
    isFiniteLocallyFree_of_iso (pullbackCompOfEq W.isoSpec.inv F _ hφ.symm P)
  exact flat_sections_top_of_pullback_Spec_map φ P

/-- Descent of finite presentation along a finite jointly surjective family of flat morphisms
`f j : W j ⟶ Spec R` from affine schemes, for quasi-coherent modules on `Spec R`: the morphism
`∐ W j ⟶ Spec R` is flat and surjective, with affine source. -/
theorem finitePresentation_sections_top_of_pullback_of_iUnion_range_eq_univ
    {R : CommRingCat.{u}} (P : (Spec R).Modules) [P.IsQuasicoherent] {κ : Type u} [Finite κ]
    {W : κ → Scheme.{u}} [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R) [∀ j, Flat (f j)]
    (hf : ⋃ j, Set.range (f j) = Set.univ)
    (h : ∀ j, ((Modules.pullback (f j)).obj P).IsFinitePresentation) :
    Module.FinitePresentation R Γ(P, ⊤) := by
  have : Surjective (Sigma.desc f) := .sigmaDesc_of_union_range_eq_univ hf
  have : ((Modules.pullback (Sigma.desc f)).obj P).IsFinitePresentation := by
    refine isFinitePresentation_of_isOpenImmersion _ (Sigma.ι W)
      (sigmaOpenCover W).iSup_opensRange fun j ↦ ?_
    have := h j
    exact isFinitePresentation_of_iso (pullbackCompOfEq _ _ _ (Sigma.ι_comp_desc f j) P).symm
  exact finitePresentation_sections_top_of_pullback_of_isAffine (Sigma.desc f) P

/-- Descent of flatness along a finite jointly surjective family of flat morphisms
`f j : W j ⟶ Spec R` from affine schemes, for quasi-coherent modules on `Spec R` whose pullbacks
are finite locally free. -/
theorem flat_sections_top_of_pullback_of_iUnion_range_eq_univ
    {R : CommRingCat.{u}} (P : (Spec R).Modules) [P.IsQuasicoherent] {κ : Type u} [Finite κ]
    {W : κ → Scheme.{u}} [∀ j, IsAffine (W j)] (f : ∀ j, W j ⟶ Spec R) [∀ j, Flat (f j)]
    (hf : ⋃ j, Set.range (f j) = Set.univ)
    (h : ∀ j, ((Modules.pullback (f j)).obj P).IsFiniteLocallyFree) :
    Module.Flat R Γ(P, ⊤) := by
  have : Surjective (Sigma.desc f) := .sigmaDesc_of_union_range_eq_univ hf
  have : ((Modules.pullback (Sigma.desc f)).obj P).IsFiniteLocallyFree := by
    refine isFiniteLocallyFree_of_isOpenImmersion _ (Sigma.ι W)
      (sigmaOpenCover W).iSup_opensRange fun j ↦ ?_
    have := h j
    exact isFiniteLocallyFree_of_iso (pullbackCompOfEq _ _ _ (Sigma.ι_comp_desc f j) P).symm
  exact flat_sections_top_of_pullback_of_isAffine (Sigma.desc f) P

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Affine-local form of a descent datum.** Let `M` be a module on `T` whose descent datum
relative to an fpqc covering `{g i : T' i ⟶ T}` is isomorphic to `D`, and let `U` be an affine
open of `T`. Then there are finitely many flat morphisms `f j : W j ⟶ Spec Γ(T, U)` from affine
schemes, jointly surjective, along which the pullback of `M` to `Spec Γ(T, U)` becomes isomorphic
to a pullback of a component of `D`. -/
theorem exists_pullback_fromSpec_iso_of_toDescentData_iso
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T)))
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    {U : T.Opens} (hU : IsAffineOpen U) :
    ∃ (κ : Type u) (_ : Finite κ) (W : κ → Scheme.{u}) (_ : ∀ j, IsAffine (W j))
      (f : ∀ j, W j ⟶ Spec Γ(T, U)) (_ : ∀ j, Flat (f j)),
      ⋃ j, Set.range (f j) = Set.univ ∧ ∀ j, ∃ (i : ι) (k : W j ⟶ T' i),
        Nonempty ((Scheme.Modules.pullback (f j)).obj
          ((Scheme.Modules.pullback hU.fromSpec).obj M) ≅
          (Scheme.Modules.pullback k).obj (D.obj i)) := by
  obtain ⟨e⟩ := hM
  obtain ⟨κ, W, f, _, _, _, hfS, hcov⟩ := Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable hU.fromSpec hg)
  choose i k hk using fun j ↦ (Sieve.mem_ofArrows_iff _ _ _).1 (hfS j)
  refine ⟨κ, inferInstance, W, inferInstance, f, inferInstance, ?_, fun j ↦ ⟨i j, k j, ⟨?_⟩⟩⟩
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hcov x
    obtain ⟨j, k', rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
    exact Set.mem_iUnion.2 ⟨j, k' y, rfl⟩
  · -- `f j ≫ fromSpec = k j ≫ g (i j)`, and `(g (i j))^* M ≅ D (i j)` by the descent datum
    let c : (Scheme.Modules.pullback (g (i j))).obj M ≅ D.obj (i j) :=
      ⟨e.hom.hom (i j), e.inv.hom (i j), congrArg (fun φ ↦ φ.hom (i j)) e.hom_inv_id,
        congrArg (fun φ ↦ φ.hom (i j)) e.inv_hom_id⟩
    exact pullbackCompOfEq (f j) hU.fromSpec _ (hk j) M ≪≫
      (pullbackCompOfEq (k j) (g (i j)) _ rfl M).symm ≪≫ (Scheme.Modules.pullback (k j)).mapIso c

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finite presentation descends along an fpqc covering**, for a quasi-coherent module: over
an affine open `U` of `T`, the global sections of the pullback of `M` to `Spec Γ(T, U)` are a
finitely presented `Γ(T, U)`-module by faithfully flat descent, so this pullback has a finite
global presentation. -/
theorem isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation) :
    (M : T.Modules).IsFinitePresentation := by
  have hP (U : T.affineOpens) :
      ∃ P : ((M : T.Modules).restrict U.2.fromSpec).Presentation, P.IsFinite := by
    obtain ⟨κ, _, W, _, f, _, hf, h⟩ :=
      exists_pullback_fromSpec_iso_of_toDescentData_iso g hg D M hM U.2
    let N := (Scheme.Modules.pullback U.2.fromSpec).obj (M : T.Modules)
    have : Module.FinitePresentation Γ(T, U.1) Γ(N, ⊤) :=
      Scheme.Modules.finitePresentation_sections_top_of_pullback_of_iUnion_range_eq_univ N f hf
        fun j ↦ by
          obtain ⟨i, k, ⟨e⟩⟩ := h j
          have := hD i
          exact Scheme.Modules.isFinitePresentation_of_iso e.symm
    obtain ⟨P, hP⟩ := Scheme.Modules.exists_presentation_isFinite_of_finitePresentation N
    exact ⟨P.ofIsIso ((Scheme.Modules.restrictFunctorIsoPullback _).app _).inv, inferInstance⟩
  choose P _ using hP
  refine Scheme.Modules.isFinitePresentation_of_iSup_opensRange_eq_top _ _ ?_ P
  exact (iSup_congr fun V ↦ IsAffineOpen.opensRange_fromSpec V.2).trans
    (iSup_affineOpens_eq_top T)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finite local freeness descends along an fpqc covering**, for a quasi-coherent module: `M`
is of finite presentation by `isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent`, and
over an affine open `U` of `T` the sections `Γ(M, U)` are flat over `Γ(T, U)` by faithfully flat
descent, so `M` is finite locally free. -/
theorem isLocallyFree_of_toDescentData_iso_of_isQuasicoherent
    (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    (D : modulesPseudofunctor.DescentData g)
    (M : modulesPseudofunctor.obj (.mk (op T))) (hMq : (M : T.Modules).IsQuasicoherent)
    (hM : Nonempty ((modulesPseudofunctor.toDescentData g).obj M ≅ D))
    (hD : ∀ i, (D.obj i : (T' i).Modules).IsFinitePresentation ∧
      (D.obj i : (T' i).Modules).IsLocallyFree) :
    (M : T.Modules).IsLocallyFree := by
  have := isFinitePresentation_of_toDescentData_iso_of_isQuasicoherent g hg D M hMq hM
    fun i ↦ (hD i).1
  suffices (M : T.Modules).IsFiniteLocallyFree from inferInstance
  refine Scheme.Modules.isFiniteLocallyFree_of_isAffineOpen _ fun U hU ↦
    ⟨Scheme.Modules.finitePresentation_sections_of_isFinitePresentation _ hU, ?_⟩
  obtain ⟨κ, _, W, _, f, _, hf, h⟩ :=
    exists_pullback_fromSpec_iso_of_toDescentData_iso g hg D M hM hU
  let N := (Scheme.Modules.pullback hU.fromSpec).obj (M : T.Modules)
  have : Module.Flat Γ(T, U) (moduleSpecΓFunctor.obj N) :=
    Scheme.Modules.flat_sections_top_of_pullback_of_iUnion_range_eq_univ N f hf fun j ↦ by
      obtain ⟨i, k, ⟨e⟩⟩ := h j
      obtain ⟨_, _⟩ := hD i
      have := Scheme.Modules.isFiniteLocallyFree_of_isFinitePresentation_of_isLocallyFree
        (D.obj i : (T' i).Modules)
      exact Scheme.Modules.isFiniteLocallyFree_of_iso e.symm
  exact .of_linearEquiv ((Scheme.Modules.sectionsRestrictFromSpecLinearEquiv _ hU).symm ≪≫ₗ
    (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback _).app _)).toLinearEquiv)

end AlgebraicGeometry
