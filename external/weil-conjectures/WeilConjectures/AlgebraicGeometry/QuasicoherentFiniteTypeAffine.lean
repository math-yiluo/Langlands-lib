/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine criteria for finite type and finite presentation of modules

Source: Stacks Project, Modules, Tags 01BN and 01BO; Properties, Tags 01PB and 01PC
(blueprint: lem-weil-pbc-quasi-coherent-finite-type-affine).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

section SiteHelpers

universe u₁ u₂ v₁ v₂

open SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem finiteType_of_data {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

private theorem finiteType_of_generators {M : SheafOfModules.{u} R}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryProducts C] (g : M.GeneratingSections) [g.IsFiniteType] :
    M.IsFiniteType := by
  have : g.localGeneratorsData.IsFiniteType := ⟨fun _ ↦ by
    dsimp [SheafOfModules.GeneratingSections.localGeneratorsData]
    infer_instance⟩
  exact finiteType_of_data g.localGeneratorsData

private theorem finiteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := ⟨fun i ↦ by
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType⟩
  exact finiteType_of_data q'

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_pushforward
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  let Q : ((pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
          pushforward (𝟙 _)
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        let e : (pushforward.{u} (F := G') ψ).obj (unit (R.over (P.X i.2.1))) ≅
            unit (S.over i.1) := overS.mapIso η
        letI : PreservesColimitsOfSize.{u, u} (pushforward.{u} (F := G') ψ) := h _ _ _
        exact (P.generators i.2.1).map (pushforward.{u} (F := G') ψ) e.symm }
  have : Q.IsFiniteType := ⟨fun i ↦ by
    have := hP.isFiniteType i.2.1
    dsimp [Q]
    infer_instance⟩
  exact finiteType_of_data Q

private theorem finiteType_pushforward_leftAdjoint
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  apply +allowSynthFailures finiteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

section Locality

variable [HasPullbacks C] [HasBinaryProducts C]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasPullbacks C] [HasBinaryProducts C] in
private theorem finiteType_of_cover (M : SheafOfModules.{u} R) {I : Type v}
    (X : I → C) (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFiniteType] :
    M.IsFiniteType := by
  choose D hD using fun i ↦ IsFiniteType.exists_localGeneratorsData (M.over (X i))
  let q : M.LocalGeneratorsData :=
    { I := (i : I) × (D i).I
      X ij := ((D ij.1).X ij.2).left
      coversTop := hX.over (fun i ↦ (D i).coversTop)
      generators i := by
        let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
          (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
          (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
        exact (((D i.1).generators i.2).map e.inverse (.refl _)).ofEpi
          (e.fullyFaithfulFunctor.preimageIso
            (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom }
  have : q.IsFiniteType := ⟨fun i ↦ by
    have := (hD i.1).isFiniteType i.2
    dsimp [q]
    infer_instance⟩
  exact finiteType_of_data q

end Locality

end SiteHelpers

namespace AlgebraicGeometry.Scheme.Modules


variable {X Y : Scheme.{u}}

private theorem finiteType_restrict (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) [M.IsFiniteType] : (M.restrict f).IsFiniteType := by
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app U := (f.appIso U.unop).inv }
  have : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : Y.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj
      X.ringCatSheaf := ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : IsIso φ := by
    rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    dsimp [φ]
    infer_instance
  exact finiteType_pushforward_leftAdjoint f.opensFunctor φ (restrictUnitIso _)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_equivOver (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsFiniteType] :
    ((overEquiv U).functor.obj M).IsFiniteType := by
  let := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : TopologicalSpace.Opens ↥U) : (Over.post U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over V)
      (((Opens.grothendieckTopology X).over U).over
        (U.overEquivalence.symm.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.symm.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv).obj M).IsFiniteType
  exact finiteType_pushforward_leftAdjoint U.overEquivalence.symm.functor _ (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_equivOver (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) [M.IsFinitePresentation] :
    ((overEquiv U).functor.obj M).IsFinitePresentation := by
  let := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  have (V : TopologicalSpace.Opens ↥U) : (Over.post U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over V)
      (((Opens.grothendieckTopology X).over U).over
        (U.overEquivalence.symm.functor.obj V)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _ U.overEquivalence.symm.functor).overPost V)
  change ((SheafOfModules.pushforward
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv).obj M).IsFinitePresentation
  exact SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint
    U.overEquivalence.symm.functor _ (Iso.refl _)

private theorem finiteType_restrict_of_over (M : X.Modules) (U : X.Opens)
    [h : (M.over U).IsFiniteType] : (M.restrict U.ι).IsFiniteType := by
  have := finiteType_equivOver U (M.over U)
  exact @finiteType_of_iso _ _ _ U.toScheme.ringCatSheaf _ _ _ _
    ((overFunctorEquiv U).app M) this

private theorem finitePresentation_restrict_of_over (M : X.Modules) (U : X.Opens)
    [h : (M.over U).IsFinitePresentation] : (M.restrict U.ι).IsFinitePresentation := by
  have := finitePresentation_equivOver U (M.over U)
  exact @isFinitePresentation_of_iso U.toScheme _ _ ((overFunctorEquiv U).app M) this


private theorem finiteType_fromSpec_of_over (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) [(M.over U).IsFiniteType] :
    (M.restrict hU.fromSpec).IsFiniteType := by
  let f : Spec Γ(X, U) ⟶ U.toScheme := IsOpenImmersion.lift U.ι hU.fromSpec (by
    rw [Scheme.Opens.range_ι]
    exact hU.opensRange_fromSpec.le)
  have hf : f ≫ U.ι = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (f ≫ U.ι) := by rw [hf]; infer_instance
  have : IsOpenImmersion f := IsOpenImmersion.of_comp f U.ι
  have := finiteType_restrict_of_over M U
  have := finiteType_restrict f (M.restrict U.ι)
  exact @finiteType_of_iso _ _ _ (Spec Γ(X, U)).ringCatSheaf _ _ _ _
    (((restrictFunctorComp f U.ι).app M).symm ≪≫ (restrictFunctorCongr hf).app M) this

private theorem finitePresentation_fromSpec_of_over (M : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) [(M.over U).IsFinitePresentation] :
    (M.restrict hU.fromSpec).IsFinitePresentation := by
  let f : Spec Γ(X, U) ⟶ U.toScheme := IsOpenImmersion.lift U.ι hU.fromSpec (by
    rw [Scheme.Opens.range_ι]
    exact hU.opensRange_fromSpec.le)
  have hf : f ≫ U.ι = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (f ≫ U.ι) := by rw [hf]; infer_instance
  have : IsOpenImmersion f := IsOpenImmersion.of_comp f U.ι
  have := finitePresentation_restrict_of_over M U
  have : ((M.restrict U.ι).restrict f).IsFinitePresentation := inferInstance
  exact @isFinitePresentation_of_iso (Spec Γ(X, U)) _ _
    (((restrictFunctorComp f U.ι).app M).symm ≪≫ (restrictFunctorCongr hf).app M) this

/-- The sections of a quasi-coherent module of finite type over an affine open `U` form a
finitely generated `Γ(X, U)`-module. -/
theorem finite_sections_of_finiteType (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hcov : IsOpenCover q.X := (Opens.coversTop_iff _ q.X).mp q.coversTop
  let s : Set Γ(X, U) := {g | Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    obtain ⟨g, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨x, hi⟩ hx
    have hV := hU.basicOpen g
    let f : Spec Γ(X, X.basicOpen g) ⟶ Scheme.Opens.toScheme (q.X i) :=
      IsOpenImmersion.lift (Scheme.Opens.ι (q.X i)) hV.fromSpec (by
        rw [Scheme.Opens.range_ι]
        exact hV.opensRange_fromSpec.le.trans hgW)
    have hf : f ≫ Scheme.Opens.ι (q.X i) = hV.fromSpec := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (f ≫ Scheme.Opens.ι (q.X i)) := by rw [hf]; infer_instance
    have : IsOpenImmersion f := IsOpenImmersion.of_comp f (Scheme.Opens.ι (q.X i))
    have : PreservesColimitsOfSize.{u, u} (overEquiv (q.X i)).functor :=
      (overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
    have : PreservesColimitsOfSize.{u, u} (restrictFunctor f) := inferInstance
    let T := (overEquiv (q.X i)).functor ⋙ restrictFunctor f
    have : PreservesColimitsOfSize.{u, u} T := inferInstance
    let e : T.obj (F.over (q.X i)) ≅ F.restrict hV.fromSpec :=
      (restrictFunctor f).mapIso ((overFunctorEquiv (q.X i)).app F) ≪≫
        ((restrictFunctorComp f (Scheme.Opens.ι (q.X i))).app F).symm ≪≫
        (restrictFunctorCongr hf).app F
    let σ := ((q.generators i).map T
      ((restrictUnitIso f).symm ≪≫
        (restrictFunctor f).mapIso (overEquivFunctorObjUnitIso (q.X i)))).ofEpi e.hom
    have : Finite σ.I := (hq.isFiniteType i).finite
    have : IsIso (F.restrict hV.fromSpec).fromTildeΓ :=
      isIso_fromTildeΓ_of_isQuasicoherent _
    have : Module.Finite Γ(X, X.basicOpen g) Γ(F.restrict hV.fromSpec, ⊤) :=
      finite_sections_top_of_isIso_fromTildeΓ _ σ
    exact Opens.mem_iSup.mpr
      ⟨⟨g, finite_sections_of_finite_sections_restrict_fromSpec F hV⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(F, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen F hU r.1
  have _ (r : s) := hU.isLocalization_basicOpen r.1
  have _ (r : s) : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(F, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun r : s ↦ Γ(X, X.basicOpen r.1)) (fun r ↦
      { toFun := F.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul F _ }) fun r ↦ r.2

private theorem exists_finite_generators_spec {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Module.Finite R Γ(M, ⊤)] :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType := by
  let N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)
  have : Module.Finite R N := ‹Module.Finite R Γ(M, ⊤)›
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R N).FG)
  have : IsIso (C := SheafOfModules.{u} (Spec R).ringCatSheaf) M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  let p := ModuleCat.ofHom (Finsupp.linearCombination R ((↑) : ↥(s : Set N) → N))
  have hp : Epi p := (ModuleCat.epi_iff_surjective p).mpr (by
    change Function.Surjective (Finsupp.linearCombination R ((↑) : ↥(s : Set N) → N))
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hs)
  have hp' : Epi ((tilde.functor R).map p) := Functor.map_epi _ _
  let φ : SheafOfModules.free (R := (Spec R).ringCatSheaf) (s : Set N) ⟶ M :=
    (tildeFinsupp (R := R) (s : Set N)).inv ≫ tilde.map p ≫ M.fromTildeΓ
  have hε : Epi M.fromTildeΓ := @IsIso.epi_of_iso _ _ _ _ _ inferInstance
  have hι : Epi (tildeFinsupp (R := R) (s : Set N)).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (tildeFinsupp (R := R) (s : Set N)))
  have hφ : Epi φ :=
    @epi_comp _ _ _ _ _ _ hι _ (@epi_comp _ _ _ _ _ _ hp' _ hε)
  let σ := (SheafOfModules.free.generatingSections (R := (Spec R).ringCatSheaf)
    (s : Set N)).ofEpi φ
  exact ⟨σ, ⟨inferInstanceAs (Finite (s : Set N))⟩⟩

private theorem finiteType_over_of_generators_restrict (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f]
    (σ : (M.restrict f).GeneratingSections) [σ.IsFiniteType] :
    (M.over f.opensRange).IsFiniteType := by
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor f.isoOpensRange.inv) :=
    inferInstance
  let τ := (σ.map (restrictFunctor f.isoOpensRange.inv)
    (restrictUnitIso _).symm).ofEpi
      (((restrictFunctorComp f.isoOpensRange.inv f).app M).inv ≫
        (restrictFunctorCongr f.isoOpensRange_inv_comp).hom.app M)
  let F : SheafOfModules.{u} f.opensRange.toScheme.ringCatSheaf ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over f.opensRange) := (overEquiv f.opensRange).inverse
  let e : F.obj (M.restrict f.opensRange.ι) ≅ M.over f.opensRange :=
    F.mapIso ((overFunctorEquiv f.opensRange).app M).symm ≪≫
      ((overEquiv f.opensRange).unitIso.app (M.over f.opensRange)).symm
  let ρ := (τ.map F
    (f.opensRange.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofEpi e.hom
  have : ρ.IsFiniteType := ⟨inferInstanceAs (Finite σ.I)⟩
  exact finiteType_of_generators (R := X.ringCatSheaf.over f.opensRange) ρ

private theorem finiteType_affine_iff (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    (F.over U).IsFiniteType ↔ Module.Finite Γ(X, U) Γ(F, U) := by
  constructor
  · intro h
    have := finiteType_fromSpec_of_over F hU
    have := finite_sections_of_finiteType (F.restrict hU.fromSpec)
      (isAffineOpen_top (Spec Γ(X, U)))
    have : Module.Finite Γ(X, U)
        (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec)) :=
      finite_sections_top_of_finite (F.restrict hU.fromSpec)
    exact Module.Finite.equiv (sectionsRestrictFromSpecLinearEquiv F hU)
  · intro h
    have : Module.Finite Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      Module.Finite.equiv (sectionsRestrictFromSpecLinearEquiv F hU).symm
    obtain ⟨σ, hσ⟩ := exists_finite_generators_spec (F.restrict hU.fromSpec)
    have := finiteType_over_of_generators_restrict F hU.fromSpec σ
    exact hU.opensRange_fromSpec ▸ this

private theorem finitePresentation_affine_iff (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    (F.over U).IsFinitePresentation ↔ Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  constructor
  · intro h
    have := finitePresentation_fromSpec_of_over F hU
    have : Module.FinitePresentation Γ(X, U)
        (moduleSpecΓFunctor.obj (F.restrict hU.fromSpec)) :=
      finitePresentation_sections_top (F.restrict hU.fromSpec)
    exact Module.FinitePresentation.of_equiv (sectionsRestrictFromSpecLinearEquiv F hU)
  · intro h
    have : Module.FinitePresentation Γ(X, U) Γ(F.restrict hU.fromSpec, ⊤) :=
      Module.FinitePresentation.of_equiv (sectionsRestrictFromSpecLinearEquiv F hU).symm
    obtain ⟨P, hP⟩ := exists_presentation_isFinite_of_finitePresentation
      (F.restrict hU.fromSpec)
    have := (presentationOverOfRestrict hU.fromSpec.opensRange
      (presentationRestrictOpensRange hU.fromSpec P)).isFinitePresentation
    exact hU.opensRange_fromSpec ▸ this

/-- Finite presentation implies quasi-coherence. For a quasi-coherent module, finite type
and finite presentation on an affine open are equivalent to the corresponding finiteness
of its sections. Finite generation on an affine open cover gives finite type globally
and finite generation on every affine open; global finite presentation gives finitely
presented sections on every affine open.
Source: Stacks Project, Modules, Tags 01BN, 01BO; Properties, Tags 01PB, 01PC
(blueprint: lem-weil-pbc-quasi-coherent-finite-type-affine).

Proof:
1. Mathlib's finite-presentation instance gives quasi-coherence directly (Stacks 01BO).
2. Map finite generating families along colimit-preserving restriction functors and
   equivalences that preserve the unit. Bind local generating families over a cover;
   shrinking the index type gives locality for covers in any universe.
3. On `Spec R`, the existing `finite_sections_top_of_isIso_fromTildeΓ` shows that a
   finite global generating family has finite sections: the tilde functor reflects
   epimorphisms between quasi-coherent modules.
4. For a quasi-coherent module of finite type, refine its local generating cover by
   basic opens in an affine open. Map the generating families to these restrictions
   and use step 3. Their defining sections span the unit ideal, and
   `Module.Finite.of_localizationSpan'` descends finite generation (Stacks 01PB).
5. Conversely a finite spanning set of affine sections defines a surjection from a
   finite free module. Tilde preserves this epimorphism; compose with the counit
   isomorphism and transport to `F.over U`. These global generators imply finite type.
6. For finite presentation, use the proved source-library results in `FiniteDescent`:
   `finitePresentation_sections_top` and
   `exists_presentation_isFinite_of_finitePresentation`. The former descends finite
   presentations over basic opens; the latter applies tilde to a finite presentation
   of the module of sections. Restriction and `sectionsRestrictFromSpecLinearEquiv`
   give both directions on every affine open (Stacks 01PC).
7. Finite sections on a covering give finite type on each member by step 5. Bind the
   local finite generators as in step 2, and apply step 4 on any affine open. The
   final assertion is `finitePresentation_sections_of_isFinitePresentation`. -/
theorem quasicoherent_finite_type_affine (X : Scheme.{u}) :
    (∀ G : X.Modules, G.IsFinitePresentation → G.IsQuasicoherent) ∧
    (∀ F : X.Modules, F.IsQuasicoherent →
      (∀ U : X.Opens, IsAffineOpen U →
        ((F.over U).IsFiniteType ↔ Module.Finite Γ(X, U) Γ(F, U)) ∧
        ((F.over U).IsFinitePresentation ↔ Module.FinitePresentation Γ(X, U) Γ(F, U))) ∧
      (∀ (I : Type v) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ → (∀ i, IsAffineOpen (U i)) →
        (∀ i, Module.Finite Γ(X, U i) Γ(F, U i)) →
        F.IsFiniteType ∧ ∀ V : X.Opens, IsAffineOpen V → Module.Finite Γ(X, V) Γ(F, V)) ∧
      (F.IsFinitePresentation →
        ∀ U : X.Opens, IsAffineOpen U → Module.FinitePresentation Γ(X, U) Γ(F, U))) := by
  refine ⟨?_, ?_⟩
  · intro G hG
    exact inferInstance
  · intro F hF
    refine ⟨fun U hU ↦ ⟨finiteType_affine_iff F hU,
      finitePresentation_affine_iff F hU⟩, ?_, ?_⟩
    · intro I U hU hAffine hFinite
      have (i : I) : (F.over (U i)).IsFiniteType :=
        (finiteType_affine_iff F (hAffine i)).mpr (hFinite i)
      have : F.IsFiniteType := finiteType_of_cover F U
        ((Opens.coversTop_iff _ U).mpr hU)
      exact ⟨this, fun V hV ↦ finite_sections_of_finiteType F hV⟩
    · intro h
      exact fun U hU ↦ finitePresentation_sections_of_isFinitePresentation F hU

end AlgebraicGeometry.Scheme.Modules
