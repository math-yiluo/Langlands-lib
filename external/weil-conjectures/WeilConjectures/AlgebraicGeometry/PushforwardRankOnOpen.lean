/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! Rank of a finite flat structure-sheaf pushforward on a constant-rank open.
Source: Stacks Project, Tags 02KB and 04MH.
(blueprint: lem-sc-finite-pushforward-rank-on-open)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem rank_pushforward_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (n : ℕ)
    (h : ∀ y, f.finrank y = n) :
    ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsFiniteLocallyFreeOfRank n := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := isQuasicoherent_pushforward_of_isAffineHom f
    (SheafOfModules.unit X.ringCatSheaf)
  refine isFiniteLocallyFreeOfRank_of_isAffineOpen _ fun V hV ↦ ?_
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have : Algebra.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.finitePresentation_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have hfl : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.flat_appLE hV hV' le_rfl
    rwa [← Hom.app_eq_appLE] at this
  have hfp : Module.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    .of_finite_of_finitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  have hpb : IsPullback hV'.fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)))) f hV.fromSpec := by
    refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
    · rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hV hV' le_rfl, ← Hom.app_eq_appLE]
      rfl
    · rw [hV.opensRange_fromSpec, hV'.opensRange_fromSpec]
  refine ⟨hfp, hfl, fun p ↦ ?_⟩
  change Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) p = n
  rw [← Hom.finrank_SpecMap_algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)]
  exact (Hom.finrank_of_isPullback _ _ f _ hpb p).trans (h _)

private theorem rank_pushforward_site {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (K.over V) AddCommGrpCat.{u}]
    [∀ V, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    [∀ V, (Over.post (X := V) G).IsContinuous (K.over V) (J.over (G.obj V))]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward.{u} φ).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S)
    (hp : ∀ (V : D) (W : C) (f : G.obj V ⟶ W),
      Limits.PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u} (R := R.over W)
          (F := Over.post (X := V) G ⋙ Over.map f)
          (((Over.forget V).sheafPushforwardContinuous RingCat.{u} (K.over V) K).map φ)))
    (M : SheafOfModules.{u} R) (n : ℕ) [h : M.IsFiniteLocallyFreeOfRank n] :
    ((SheafOfModules.pushforward.{u} φ).obj M).IsFiniteLocallyFreeOfRank n := by
  classical
  obtain ⟨q, hq, hr⟩ := h.exists_localGeneratorsData
  have := hq
  let q' : ((SheafOfModules.pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (V : D) (i : q.I), G.obj V ⟶ q.X i
      X := fun i ↦ i.1
      coversTop := fun V ↦ by
        refine K.superset_covering ?_ (G.cover_lift K _ (q.coversTop (G.obj V)))
        intro W g ⟨i, ⟨v⟩⟩
        exact ⟨⟨W, i, v⟩, ⟨𝟙 _⟩⟩
      generators := fun i ↦ by
        have := hp i.1 (q.X i.2.1) i.2.2
        exact (q.generators i.2.1).map
          (SheafOfModules.pushforward.{u}
            (F := Over.post (X := i.1) G ⋙ Over.map i.2.2)
            (((Over.forget i.1).sheafPushforwardContinuous RingCat (K.over i.1) K).map φ))
          ((SheafOfModules.pushforward (𝟙 (S.over i.1))).mapIso η).symm }
  have : q'.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [q']
    infer_instance
  refine ⟨q', this, ?_⟩
  intro i
  exact hr i.2.1

private theorem rank_over_of_restrict {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (n : ℕ) [h : (M.restrict U.ι).IsFiniteLocallyFreeOfRank n] :
    (M.over U).IsFiniteLocallyFreeOfRank n := by
  classical
  let G := U.overEquivalence.functor
  have : G.IsContinuous ((Opens.grothendieckTopology Y).over U)
      (Opens.grothendieckTopology U.carrier) := by
    dsimp [G]
    infer_instance
  have : G.IsCocontinuous ((Opens.grothendieckTopology Y).over U)
      (Opens.grothendieckTopology U.carrier) := by
    dsimp [G]
    infer_instance
  have hpost : ∀ (V : Over U), (Over.post (X := V) G).IsContinuous
      (((Opens.grothendieckTopology Y).over U).over V)
      ((Opens.grothendieckTopology U.carrier).over (G.obj V)) := by
    intro V
    apply Functor.isContinuous_iff_coverPreserving.mpr
    exact (CoverPreserving.of_isContinuous G _ _).overPost V
  let φ := (U.sheafRestrictSheafEquivOver.app Y.ringCatSheaf).inv
  let η := U.sheafOfModulesEquivOverInverseUnit Y.ringCatSheaf
  let R := (TopologicalSpace.Opens.sheafRestrict (C := RingCat.{u}) U).obj Y.ringCatSheaf
  let N : SheafOfModules.{u} R := M.restrict U.ι
  have hn₀ : N.IsFiniteLocallyFreeOfRank n := h
  have hp (V : CategoryTheory.Over U) (W : TopologicalSpace.Opens U.carrier) (f : G.obj V ⟶ W) :
      CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u}
          (R := R.over W)
          (F := CategoryTheory.Over.post (X := V) G ⋙ CategoryTheory.Over.map f)
          (((CategoryTheory.Over.forget V).sheafPushforwardContinuous RingCat
            ((Opens.grothendieckTopology Y).over U |>.over V)
            ((Opens.grothendieckTopology Y).over U)).map φ)) := by
    let F := Over.post (X := V) G ⋙ Over.map f
    have : F.IsContinuous (((Opens.grothendieckTopology Y).over U).over V)
        ((Opens.grothendieckTopology U.carrier).over W) := inferInstance
    have : F.IsCocontinuous (((Opens.grothendieckTopology Y).over U).over V)
        ((Opens.grothendieckTopology U.carrier).over W) :=
      isCocontinuous_comp _ _ _ ((Opens.grothendieckTopology U.carrier).over (G.obj V))
    have : F.IsLeftAdjoint := by dsimp [F, G]; infer_instance
    let ψ : (Y.ringCatSheaf.over U).over V ⟶
        (F.sheafPushforwardContinuous RingCat
          (((Opens.grothendieckTopology Y).over U).over V)
          ((Opens.grothendieckTopology U.carrier).over W)).obj (R.over W) :=
      ((Over.forget V).sheafPushforwardContinuous RingCat
      (((Opens.grothendieckTopology Y).over U).over V)
      ((Opens.grothendieckTopology Y).over U)).map φ
    have : (SheafOfModules.pushforward.{u} (F := F) ψ).IsLeftAdjoint :=
      SheafOfModules.isLeftAdjoint_pushforward_of_isIso (F := F) ψ
    infer_instance
  have := hn₀
  have hn : ((SheafOfModules.pushforward.{u} φ).obj N).IsFiniteLocallyFreeOfRank n :=
    rank_pushforward_site G φ η hp N n
  have : ((overEquiv U).inverse.obj (M.restrict U.ι)).IsFiniteLocallyFreeOfRank n := hn
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    ((overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm)

private theorem pushforward_restrict_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) :
    Nonempty (((pushforward f).obj M).restrict U.ι ≅
      (pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)) := by
  let e : U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor :=
    NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V).symm)
  change Nonempty (((SheafOfModules.pushforward f.toRingCatSheafHom) ⋙
    restrictFunctor U.ι).obj M ≅
    (restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U)).obj M)
  unfold restrictFunctor pushforward
  refine ⟨((SheafOfModules.pushforwardComp _ _) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm).app M⟩
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext V x
  change X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
      (f.app (U.ι ''ᵁ V.unop) ((U.ι.appIso V.unop).inv x)) =
    ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V.unop)).inv ((f ∣_ U).app V.unop x)
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  exact (ConcreteCategory.congr_hom (morphismRestrict_app f U V.unop) x).symm

/-- On any open where a finite flat locally finitely presented morphism has constant rank
`n`, its structure-sheaf pushforward has finite locally free rank `n`.

Source: Stacks Project, Morphisms of Schemes, Tags 02KB and 04MH.
(blueprint: lem-sc-finite-pushforward-rank-on-open)

Proof: Cover `U` by affine opens `V = Spec A` of `Y` contained in `U`. Since `f` is finite,
its inverse image is affine, say `Spec B`. The module of sections of the pushforward on `V`
is `B` with its `A`-action induced by `f`. Finiteness, flatness and local finite presentation
of `f` make `B` a finite flat finitely presented `A`-module, hence a finite projective module.
At every prime of `A`, its local rank equals `f.finrank` at the corresponding point of `V`,
by the affine definition and base-change invariance of the morphism rank. The hypothesis
therefore makes every such rank equal to `n`. A finite projective module of constant rank
`n` is locally free of rank `n`: near each prime, choose a basis of its free localization
and shrink to a principal open where its finitely many basis vectors and inverse matrix
are defined. These principal opens cover `V`. The associated sheaf is consequently locally
free of rank `n`. Combining the covers for all `V` gives local generators data of rank `n`
on the over-`U` site. If `U` is empty the covering condition is vacuous; for `n = 0` the
localized modules and the free sheaves are zero, so the same argument applies. -/
theorem isFiniteLocallyFreeOfRank_pushforward_unit_over {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (U : Y.Opens) (n : ℕ)
    (h : ∀ y ∈ U, f.finrank y = n) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).over U) n := by
  have hr : ∀ y : U, (f ∣_ U).finrank y = n := by
    intro y
    exact (Hom.finrank_of_isPullback _ _ f U.ι
      (isPullback_morphismRestrict f U).flip y).trans (h y.1 y.2)
  have := rank_pushforward_unit (f ∣_ U) n hr
  obtain ⟨e⟩ := pushforward_restrict_iso f U (SheafOfModules.unit X.ringCatSheaf)
  have e' := e ≪≫ (pushforward (f ∣_ U)).mapIso (restrictUnitIso (f ⁻¹ᵁ U).ι)
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (r := n) e'.symm
  exact rank_over_of_restrict _ U n

end AlgebraicGeometry.Scheme.Modules
