/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.CategoryTheory.Sites.ConstantForget
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence

/-! # Intrinsic finite constructibility and fixed coefficient modules

Source: Stacks Project, Tags 09AJ, 099Y and 00YV.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.ConstantForget

private theorem finite_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {Λ : Type w} [Ring Λ] [Finite Λ]
    [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))]
    {F : Sheaf J (ModuleCat.{w} Λ)} {X : Type w} [Finite X]
    (e : (sheafCompose J (CategoryTheory.forget (ModuleCat.{w} Λ))).obj F ≅
      (constantSheaf J (Type w)).obj X) (T : C)
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
    [∀ U : C, (J.over U).HasSheafCompose (CategoryTheory.forget (ModuleCat.{w} Λ))] :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (f : U ⟶ T), S f →
      ∃ M : ModuleCat.{w} Λ, Finite M ∧ Nonempty
        (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj M) := by
  classical
  let : Fintype ((X × X) ⊕ (Λ × X) ⊕ Unit) := Fintype.ofFinite _
  -- the finitely many sections whose restrictions have to be of the form `σ_z`
  let t : (X × X) ⊕ (Λ × X) ⊕ Unit → F.obj.obj (op T)
    | .inl p => σ e T p.1 + σ e T p.2
    | .inr (.inl p) => p.1 • σ e T p.2
    | .inr (.inr _) => 0
  let Si : (X × X) ⊕ (Λ × X) ⊕ Unit → Sieve T := fun i ↦
    Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj X)) (e.hom.hom.app (op T) (t i))
  have hSi : ∀ i, Si i ∈ J T := fun i ↦ Presheaf.imageSieve_mem J _ _
  refine ⟨Finset.univ.inf Si, J.finsetInf_mem _ _ hSi, fun U f hf ↦ ?_⟩
  have hf' : ∀ i, ∃ z, F.obj.map f.op (t i) = F.obj.map f.op (σ e T z) := fun i ↦
    exists_eq_map_σ e (t i) f (Finset.inf_le (Finset.mem_univ i) (f := Si) _ hf)
  let ρ : F.obj.obj (op T) →ₗ[Λ] F.obj.obj (op U) := (F.obj.map f.op).hom
  -- the restrictions of the `σ_x` form a submodule `N` of `F(U)`
  let N : Submodule Λ (F.obj.obj (op U)) :=
    { carrier := Set.range fun x ↦ ρ (σ e T x)
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inl (x, y))
        exact ⟨z, by rw [← map_add]; exact hz.symm⟩
      zero_mem' := by
        obtain ⟨z, hz⟩ := hf' (.inr (.inr ()))
        exact ⟨z, by rw [← map_zero ρ]; exact hz.symm⟩
      smul_mem' := by
        rintro c _ ⟨x, rfl⟩
        obtain ⟨z, hz⟩ := hf' (.inr (.inl (c, x)))
        exact ⟨z, by rw [← map_smul]; exact hz.symm⟩ }
  -- the morphism from the constant presheaf at `N` to `F|_U`
  let α : (Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N) ⟶ (F.over U).obj :=
    { app V := ModuleCat.ofHom ((F.obj.map V.unop.hom.op).hom ∘ₗ N.subtype)
      naturality V W g := by
        ext n
        change F.obj.map W.unop.hom.op n.1 = F.obj.map g.unop.left.op (F.obj.map V.unop.hom.op n.1)
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w] }
  let φ : (constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj (ModuleCat.of Λ N) ⟶ F.over U :=
    ⟨sheafifyLift (J.over U) α (F.over U).property⟩
  have hφ : toSheafify (J.over U) _ ≫ φ.hom = α := toSheafify_sheafifyLift _ _ _
  -- the restriction of the sheafification map of the constant presheaf at `X`
  let τ := Functor.whiskerLeft (Over.forget U).op
    (toSheafify J ((Functor.const Cᵒᵖ).obj X))
  have : Presheaf.IsLocallyInjective J (toSheafify J ((Functor.const Cᵒᵖ).obj X)) :=
    (J.W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective J (toSheafify J ((Functor.const Cᵒᵖ).obj X)) :=
    (J.W_toSheafify _).isLocallySurjective
  have hτi : Presheaf.IsLocallyInjective (J.over U) τ :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hτs : Presheaf.IsLocallySurjective (J.over U) τ :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  -- the value of `α` on the restriction of `σ_x`
  have hα (V : (Over U)ᵒᵖ) (x : X) :
      e.hom.hom.app (op V.unop.left) (α.app V ⟨ρ (σ e T x), x, rfl⟩) = τ.app V x := by
    change e.hom.hom.app (op V.unop.left)
      (F.obj.map V.unop.hom.op (F.obj.map f.op (σ e T x))) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact hom_app_map_σ e _ x
  have hαi : Presheaf.IsLocallyInjective (J.over U) α := by
    refine ⟨fun {V} n₁ n₂ h ↦ ?_⟩
    obtain ⟨x₁, hx₁⟩ := n₁.2
    obtain ⟨x₂, hx₂⟩ := n₂.2
    have e₁ : n₁ = ⟨ρ (σ e T x₁), x₁, rfl⟩ := Subtype.ext hx₁.symm
    have e₂ : n₂ = ⟨ρ (σ e T x₂), x₂, rfl⟩ := Subtype.ext hx₂.symm
    have h' : τ.app V x₁ = τ.app V x₂ := by
      rw [← hα, ← hα, ← e₁, ← e₂, h]
    refine J.over U |>.superset_covering ?_ (Presheaf.equalizerSieve_mem _ τ x₁ x₂ h')
    intro W g (hg : x₁ = x₂)
    change ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₁ =
      ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N)).map g.op n₂
    rw [e₁, e₂, hg]
  have hαs : Presheaf.IsLocallySurjective (J.over U) α := by
    refine ⟨fun {V} s ↦ ?_⟩
    refine J.over U |>.superset_covering ?_
      (Presheaf.imageSieve_mem _ τ (e.hom.hom.app (op V.left) s))
    rintro W g ⟨x, hx⟩
    refine ⟨⟨ρ (σ e T x), x, rfl⟩, injective_hom_app e W.left ?_⟩
    rw [hα]
    exact hx.trans (NatTrans.naturality_apply e.hom.hom g.left.op s).symm
  have : Presheaf.IsLocallyInjective (J.over U)
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((J.over U).W_toSheafify _).isLocallyInjective
  have : Presheaf.IsLocallySurjective (J.over U)
      (toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ N))) :=
    ((J.over U).W_toSheafify _).isLocallySurjective
  have : IsIso φ := by
    rw [← Sheaf.isLocallyBijective_iff_isIso φ]
    rw [← hφ] at hαi hαs
    exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp hαi,
      (Presheaf.comp_isLocallySurjective_iff _ _ _).mp hαs⟩
  have hN : Finite N := Finite.of_surjective
    (fun x : X ↦ (⟨ρ (σ e T x), x, rfl⟩ : N)) (by
      rintro ⟨n, x, rfl⟩
      exact ⟨x, rfl⟩)
  exact ⟨ModuleCat.of Λ N, hN, ⟨(asIso φ).symm⟩⟩

namespace AlgebraicGeometry.Scheme

private abbrev underlying (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf ((adicLisseForget X).obj R) ⋙
    sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})

private theorem pullbackUnderlying {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (proEtaleModuleInverseImage g R ⋙
      underlying Y ((adicTowerInverseImage g).obj R) ≅
        underlying X R ⋙ proEtaleSheafInverseImage g (Type (u + 1))) := by
  obtain ⟨_, e, _⟩ := (proEtale_moduleInverseImage_comparison g R).2
  exact ⟨e⟩

private def fixedUnderlyingPullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    ProEtale.upperStar (ModuleCat.{u + 1} B) g ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget (ModuleCat.{u + 1} B)) ≅
      sheafCompose (ProEt.topology X) (CategoryTheory.forget (ModuleCat.{u + 1} B)) ⋙
        proEtaleSheafInverseImage g (Type (u + 1)) := by
  let F := proEtaleBaseChange g
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits _
  let : (CategoryTheory.forget (ModuleCat.{u + 1} B)).PreservesLeftKanExtensions F.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget (ModuleCat.{u + 1} B)) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (CategoryTheory.forget (ModuleCat.{u + 1} B)) P F.op V := by
      intro V
      infer_instance
    infer_instance
  exact sheafPullbackForgetIso (ProEt.topology X) (ProEt.topology Y)
    F (CategoryTheory.forget (ModuleCat.{u + 1} B))

private def constantUnderlying (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (M : ModuleCat.{u + 1} B) :
    (underlying X (adicLisseConstantRing X B)).obj ((adicLisseConstantModules X B).obj M) ≅
      (constantSheaf (ProEt.topology X) (Type (u + 1))).obj (M : Type (u + 1)) := by
  exact (sheafComposeNatIso _ (CategoryTheory.forget AddCommGrpCat.{u + 1})
    (sheafificationAdjunction _ AddCommGrpCat.{u + 1})
    (sheafificationAdjunction _ (Type (u + 1)))).symm.app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteModels_of_sieve
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (S : Sieve (⊤_ X.ProEt)) (hS : S ∈ ProEt.topology X (⊤_ X.ProEt))
    (hmodels : ∀ (V : X.ProEt) (f : V ⟶ ⊤_ X.ProEt), S f →
      ∃ M : ModuleCat.{u + 1} B, Finite M ∧ Nonempty
        (F.over V ≅ (constantSheaf ((ProEt.topology X).over V)
          (ModuleCat.{u + 1} B)).obj M)) : ProEtale.IsFiniteLocallyConstant B F := by
  let T : X.ProEt := ProEt.mk (𝟙 X)
  let S' := S.pullback (terminal.from T)
  have hS' : S' ∈ ProEt.topology X T :=
    (ProEt.topology X).pullback_stable (terminal.from T) hS
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp hS'
  obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at hP
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id (f i).left).symm.trans hw
    simpa only [hw] using hP
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hmodels (U i) (f i ≫ terminal.from T) (hPS _ _ ⟨i⟩)
  have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) := ProEt.sliceDense X (U i)
  let E := (ProEt.sliceEquiv X (U i)).sheafCongr
    ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : E.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
    ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
  exact ⟨M, Module.Finite.of_finite, ⟨(ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
      r.symm ≪≫ E.functor.mapIso e ≪≫ c⟩⟩

private theorem finiteConstantUnderlying_lisse
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (T : Type (u + 1)) [Finite T]
    (e : (sheafCompose (ProEt.topology X)
        (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj F ≅
      (constantSheaf (ProEt.topology X) (Type (u + 1))).obj T) :
    ProEtale.IsFiniteLocallyConstant B F := by
  obtain ⟨S, hS, h⟩ := finite_refinement e (⊤_ X.ProEt)
  exact finiteModels_of_sieve X B F S hS (fun U f hf ↦ h f hf)

private def coefficientUnderlying
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : adicLisseConstantRing X B ≅ AdicCoefficients.coefficientRing X B)
    (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    (underlying X (adicLisseConstantRing X B)).obj
      ((pbcRestrict e.hom).obj
        ((SheafOfModules.restrictScalars
          (AdicCoefficients.finiteRingComparison X B).hom).obj
            ((ProEtale.finiteCoefficientRealization X B).obj G))) ≅
      (sheafCompose (ProEt.topology X)
        (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj G := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot _
  exact (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso
      (asIso ((sheafificationAdjunction (ProEt.topology X)
        AddCommGrpCat.{u + 1}).counit.app
          ((sheafCompose (ProEt.topology X)
            (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).obj G)))

private def pullbackConstant {X Y : Scheme.{u}} (g : Y ⟶ X)
    (T : Type (u + 1)) :
    (proEtaleSheafInverseImage g (Type (u + 1))).obj
      ((constantSheaf (ProEt.topology X) (Type (u + 1))).obj T) ≅
        (constantSheaf (ProEt.topology Y) (Type (u + 1))).obj T := by
  exact ((proEtaleSheafAdjunction g (Type (u + 1))).leftAdjointUniq
    ((proEtaleBaseChange g).sheafAdjunctionContinuous (Type (u + 1))
      (ProEt.topology X) (ProEt.topology Y))).app _ ≪≫
    ((proEtaleBaseChange g).constantSheafsheafPullbackIso
    (Type (u + 1)) (ProEt.topology X) (ProEt.topology Y)
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (proEtaleBaseChange g))).app T

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_lisse_of_underlying_models
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (S : Sieve (⊤_ X.ProEt)) (hS : S ∈ ProEt.topology X (⊤_ X.ProEt))
    (hmodels : ∀ (V : X.ProEt) (f : V ⟶ ⊤_ X.ProEt), S f →
      ∃ T : Type (u + 1), Finite T ∧ Nonempty
        (((sheafCompose (ProEt.topology X)
          (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj F).over V ≅
            (constantSheaf ((ProEt.topology X).over V) (Type (u + 1))).obj T)) :
    ProEtale.IsFiniteLocallyConstant B F := by
  classical
  let T : X.ProEt := ProEt.mk (𝟙 X)
  let S' := S.pullback (terminal.from T)
  have hS' : S' ∈ ProEt.topology X T :=
    (ProEt.topology X).pullback_stable (terminal.from T) hS
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp hS'
  obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage X := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage X at hP
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 X = (U i).hom at hw
      exact (Category.comp_id (f i).left).symm.trans hw
    simpa only [hw] using hP
  have hl (i : I) : ProEtale.IsFiniteLocallyConstant B
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) (U i).hom).obj F) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := hmodels (U i) (f i ≫ terminal.from T) (hPS _ _ ⟨i⟩)
    let : Finite N := hN
    let : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) (Type (u + 1))
    let r : (sheafCompose (ProEt.topology (U i).left)
        (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} B) (U i).hom).obj F) ≅
        E.functor.obj (((sheafCompose (ProEt.topology X)
          (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj F).over (U i)) :=
      (sheafCompose (ProEt.topology (U i).left)
        (CategoryTheory.forget (ModuleCat.{u + 1} B))).mapIso
          ((ProEtale.upperStarIsoLocalizationRestriction
            (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F)
    exact finiteConstantUnderlying_lisse (U i).left B _ N
      (r ≪≫ E.functor.mapIso e ≪≫
        ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
          ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
          (Type (u + 1)) (Over.mkIdTerminal (X := U i))).app N)
  choose J W g hg' hc using hl
  refine ⟨Σ i, J i, fun p ↦ W p.1 p.2, fun p ↦ g p.1 p.2 ≫ (U p.1).hom,
    Precoverage.IsStableUnderComposition.comp_mem_coverings _ hg g hg', fun ⟨i, j⟩ ↦ ?_⟩
  obtain ⟨N, hN, ⟨e⟩⟩ := hc i j
  exact ⟨N, hN, ⟨(ProEtale.upperStarComp _ (g i j) (U i).hom).app F ≪≫ e⟩⟩

private theorem relative_lisse_fixed
    {X Y : Scheme.{u}} (g : Y ⟶ X) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
    (G : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} B))
    (e : (underlying Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))).obj F ≅
      (sheafCompose (ProEt.topology Y)
        (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj G)
    (hF : IsRelativelyFiniteLisseModule g B F) :
    ProEtale.IsFiniteLocallyConstant B G := by
  obtain ⟨S, hS, h⟩ := hF
  obtain ⟨c⟩ := pullbackUnderlying g (adicLisseConstantRing X B)
  refine finite_lisse_of_underlying_models Y B G S hS ?_
  intro V f hf
  obtain ⟨M, hM, ⟨eM⟩⟩ := h V f hf
  let U := SheafOfModules.toSheaf
    (((adicLisseForget Y).obj
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))).over V) ⋙
    sheafCompose ((ProEt.topology Y).over V)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let m : ((underlying Y
      ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))).obj F).over V ≅
      ((underlying Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))).obj
        ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
          ((adicLisseConstantModules X B).obj M))).over V := U.mapIso eM
  let k : (underlying Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B))).obj
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
        ((adicLisseConstantModules X B).obj M)) ≅
      (constantSheaf (ProEt.topology Y) (Type (u + 1))).obj (M : Type (u + 1)) :=
    c.app _ ≪≫ (proEtaleSheafInverseImage g (Type (u + 1))).mapIso
      (constantUnderlying X B M) ≪≫ pullbackConstant g (M : Type (u + 1))
  exact ⟨M, hM, ⟨((ProEt.topology Y).overPullback (Type (u + 1)) V).mapIso e.symm ≪≫
    m ≪≫ ((ProEt.topology Y).overPullback (Type (u + 1)) V).mapIso k ≪≫
      (constantSheafOverIso (ProEt.topology Y) (Type (u + 1)) V
        (M : Type (u + 1))).symm⟩⟩

/-- Intrinsic finite constructibility gives constructibility in the fixed-ring
presentation, for any isomorphism presenting the finite constant coefficient ring.
This is an assertion about a single sheaf, with no derived objects or bounds.

Source: Stacks Project, proetale.tex, Tags 09AJ and 099Y; Tag 00YV for associated
module sheaves (blueprint: lem-weil-pbc-finite-coefficient-intrinsic-constructibility).

Proof: forget each relative finite module model to its finite underlying set.
The module inverse-image comparison and preservation of constant sheaves identify
these with constant finite set models of the fixed-ring sheaf on each stratum.
Scalar restriction leaves underlying sets unchanged, including for an arbitrary
presenting isomorphism e. After a finite covering refinement, addition, zero and
every scalar multiple of the finitely many constant sections are constant.
Their values form a finite submodule N of the sections on that cover member.
The induced map from the constant N-module presheaf is locally bijective on
underlying sets, so sheafification makes it an isomorphism of module sheaves.
Compose the covers and use the equivalence between the slice site and the
pro-etale site of the covering object. The original finite stratification now
witnesses fixed-ring constructibility. Empty strata and the zero coefficient
ring satisfy the same construction. -/
theorem finiteCoefficient_intrinsic_constructible
    (X : Scheme.{u}) [IsNoetherian X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (e : adicLisseConstantRing X B ≅ AdicCoefficients.coefficientRing X B) :
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := discreteTopology_bot _
    ∀ G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B),
      IsConstructibleProEtaleCoefficientModuleSheaf X B
        ((pbcRestrict e.hom).obj
          ((SheafOfModules.restrictScalars
            (AdicCoefficients.finiteRingComparison X B).hom).obj
              ((ProEtale.finiteCoefficientRealization X B).obj G))) →
      ProEtale.IsConstructible B G := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot _
  intro G hG
  let F := (pbcRestrict e.hom).obj
    ((SheafOfModules.restrictScalars
      (AdicCoefficients.finiteRingComparison X B).hom).obj
        ((ProEtale.finiteCoefficientRealization X B).obj G))
  obtain ⟨S, _, _, hS⟩ := hG
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨c⟩ := pullbackUnderlying (S.immersion i) (adicLisseConstantRing X B)
  exact relative_lisse_fixed (S.immersion i) B _ _
    (c.app F ≪≫ (proEtaleSheafInverseImage (S.immersion i) (Type (u + 1))).mapIso
      (coefficientUnderlying X B e G) ≪≫
        (fixedUnderlyingPullback (S.immersion i) B).symm.app G) (hS i)

end AlgebraicGeometry.Scheme
