/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentGenericMonoIdealFactor
import WeilConjectures.AlgebraicGeometry.IntegralIdealsCommonGenericLattice
import WeilConjectures.AlgebraicGeometry.CoherentGenericPointIdealInclusion
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits ZeroObject AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] preservesBiproduct_of_preservesProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem stalk_preservesFiniteLimits (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (RingedSpace.moduleStalkFunctor X.toRingedSpace x) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let A := forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  have : PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful X.ringCatSheaf).2.1
  have : PreservesFiniteLimits
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor (X := X.toTopCat) AddCommGrpCat.{u} x) :=
    TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor _
  have : PreservesFiniteLimits (S ⋙ A) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
          TopCat.Presheaf.stalkFunctor (X := X.toTopCat) AddCommGrpCat.{u} x))
    exact comp_preservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat ⋙
        TopCat.Presheaf.stalkFunctor (X := X.toTopCat) AddCommGrpCat.{u} x)
  exact preservesFiniteLimits_of_reflects_of_preserves S A

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem stalk_sum_isIso (X : Scheme.{u}) (x : X) (r : ℕ)
    {A B : X.Modules} (b : A ⟶ B)
    [IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map b)] :
    IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
      (biproduct.map (fun _ : Fin r ↦ b))) := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let : PreservesFiniteLimits S := stalk_preservesFiniteLimits X x
  have he : S.map (biproduct.map (fun _ : Fin r ↦ b)) =
      (S.mapBiproduct (fun _ : Fin r ↦ A)).hom ≫
        (biproduct.mapIso (fun _ : Fin r ↦ asIso (S.map b))).hom ≫
          (S.mapBiproduct (fun _ : Fin r ↦ B)).inv := by
    apply (cancel_mono (S.mapBiproduct (fun _ : Fin r ↦ B)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biproduct.hom_ext
    intro j
    change S.map (biproduct.map (fun _ : Fin r ↦ b)) ≫
        (biproduct.lift (fun j : Fin r ↦ S.map (biproduct.π (fun _ ↦ B) j))) ≫
          biproduct.π _ j =
      (biproduct.lift (fun j : Fin r ↦ S.map (biproduct.π (fun _ ↦ A) j))) ≫
        (biproduct.map (fun _ : Fin r ↦ S.map b)) ≫ biproduct.π _ j
    simp only [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc,
      ← S.map_comp]
  rw [he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Core geometric construction of the patching embedding, omitting the generic
stalk bijectivity conclusion.  Source: Stacks Project, Tag 01YL, third paragraph.
(blueprint: lem-weil-pbc-coherent-ideal-patching-generic-embedding-core)
Proof: carry out the finite pushforward, ideal intersection, annihilator, and
factorization construction from Tag 01YL; generic stalk bijectivity is established
separately by `coherent_ideal_patching_generic_embedding_stalk_bijective`. -/
theorem coherent_ideal_patching_generic_embedding_core
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (ξ : X) (hclosure : closure ({ξ} : Set X) = Set.range i.base)
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hsupport : {x : X | ¬ Subsingleton (G.presheaf.stalk x)} = Set.range i.base)
    (hkill : ∀ g : X.presheaf.stalk ξ,
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj G,
        g ∈ IsLocalRing.maximalIdeal _ → g • m = 0)
    (I : Z.IdealSheafData) :
    ∃ (r : ℕ), 1 ≤ r ∧
      let M := @biproduct (Fin r) X.Modules _ _
        (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
        (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
      (IsZero M ∨
        ∃ (J : X.Modules) (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf),
          Mono ι ∧ J.IsQuasicoherent ∧
          Function.Surjective
            ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι).hom ∧
          ∃ (τ : idealModuleProduct ι G ⟶ M), Mono τ ∧
            Function.Surjective
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map τ).hom) := by
  classical
  by_cases hI : IsZero ((pushforward i).obj I.toModules)
  · refine ⟨1, le_refl _, Or.inl ?_⟩
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact hI.eq_of_tgt _ _
  have : IsNoetherian X := ⟨⟩
  have hpoint : i.base (genericPoint Z) = ξ := by
    have h := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h
    exact h.eq hclosure
  have hkill' : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj G, a • m = 0 := by
    rw [hpoint]
    intro a ha m
    exact hkill a m ha
  obtain ⟨r, A, _, α, hα, W, hW, hαW⟩ :=
    coherent_generic_point_ideal_inclusion i G hG hkill'
  have : Mono α := hα
  have hx : ¬ Subsingleton (G.presheaf.stalk (i.base (genericPoint Z))) := by
    change i.base (genericPoint Z) ∈ {x : X | ¬ Subsingleton (G.presheaf.stalk x)}
    rw [hsupport]
    exact ⟨genericPoint Z, rfl⟩
  have : IsIso ((restrictFunctor W.ι).map α) := by
    apply (NatIso.isIso_map_iff (overFunctorEquiv W) α).mp
    change IsIso ((overEquiv W).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf W).map α))
    have := hαW
    infer_instance
  have hαbij : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map α).hom := by
    rw [← hpoint]
    exact bijective_stalk_of_isIso_restrict α _ hW
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hzA : IsZero A.toModules := by
      apply isZero_of_forall_affineOpens
      intro U
      refine ⟨fun a b ↦ ?_⟩
      apply A.injective_toModulesι_app U.1
      have zero (a : Γ(A.toModules, U.1)) : A.toModulesι.app U.1 a = 0 := by
        have ha : A.toModulesι.app U.1 a ∈ (A.ideal U : Set Γ(Z, U.1)) := by
          rw [← A.range_toModulesι_app U]
          exact Set.mem_range_self a
        simpa [hbot] using ha
      exact (zero a).trans (zero b).symm
    have hzsum : IsZero (∐ fun _ : Fin r ↦ A.toModules) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact hzA.eq_of_src _ _
    have hz := (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_isZero
      ((pushforward i).map_isZero hzsum)
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
        ((pushforward i).obj (∐ fun _ : Fin r ↦ A.toModules))) :=
      ModuleCat.subsingleton_of_isZero hz
    rw [hpoint] at hx
    exact hx hαbij.2.subsingleton
  have hr : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := by omega
    subst r
    have hzsum : IsZero (∐ fun _ : Fin 0 ↦ A.toModules) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact j.elim0
    have hz := (RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_isZero
      ((pushforward i).map_isZero hzsum)
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).obj
        ((pushforward i).obj (∐ fun _ : Fin 0 ↦ A.toModules))) :=
      ModuleCat.subsingleton_of_isZero hz
    rw [hpoint] at hx
    exact hx hαbij.2.subsingleton
  obtain ⟨K, b, d, _, hK, hb, hd, hbξ, hdξ⟩ :=
    integral_ideals_common_generic_lattice i I A hI hAne
  have : Mono b := hb
  have : Mono d := hd
  have hbξ' : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map b) := by
    rwa [hpoint] at hbξ
  have hdξ' : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map d) := by
    rwa [hpoint] at hdξ
  let L := ⨁ fun _ : Fin r ↦ K
  let M := @biproduct (Fin r) X.Modules _ _
    (fun _ : Fin r ↦ (pushforward i).obj I.toModules)
    (HasBiproduct.of_hasProduct (fun _ : Fin r ↦ (pushforward i).obj I.toModules))
  let e : (⨁ fun _ : Fin r ↦ (pushforward i).obj A.toModules) ≅
      (pushforward i).obj (∐ fun _ : Fin r ↦ A.toModules) :=
    (Functor.mapBiproduct (pushforward i) (fun _ : Fin r ↦ A.toModules)).symm ≪≫
      (pushforward i).mapIso (biproduct.isoCoproduct (fun _ : Fin r ↦ A.toModules))
  let a : L ⟶ G := biproduct.map (fun _ : Fin r ↦ b) ≫ e.hom ≫ α
  let δ : L ⟶ M := biproduct.map (fun _ : Fin r ↦ d)
  have : Mono a := inferInstanceAs (Mono (biproduct.map (fun _ : Fin r ↦ b) ≫ _ ≫ α))
  have : Mono δ := inferInstanceAs (Mono (biproduct.map (fun _ : Fin r ↦ d)))
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map α) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hαbij
  have : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
      (biproduct.map (fun _ : Fin r ↦ b))) := stalk_sum_isIso X ξ r b
  have hδbij : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map δ).hom := by
    have := stalk_sum_isIso X ξ r d
    exact ConcreteCategory.bijective_of_isIso _
  have habij : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map a).hom := by
    dsimp only [a]
    rw [Functor.map_comp, Functor.map_comp]
    exact ConcreteCategory.bijective_of_isIso _
  have hL : RingedSpace.IsCoherent X.toRingedSpace L :=
    (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).2.2.1 r _ (fun _ ↦ hK)
  obtain ⟨J, ι, hι, hJ, hιξ, ψ, hψ⟩ :=
    coherent_generic_mono_ideal_factor X hL hG a ξ habij
  have : Mono ι := hι
  have hproduct : Mono (idealModuleProductι ι G) := by
    dsimp [idealModuleProductι]
    infer_instance
  have : Mono ψ := mono_of_mono_fac hψ
  have hψsurj : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ψ).hom := by
    obtain ⟨e', _, _, _, hrange, _⟩ := ideal_module_product_stalk ι G ξ
    have htop : (LinearMap.range
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map ι ≫ e'.hom).hom :
          Ideal (X.presheaf.stalk ξ)) = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      exact (ConcreteCategory.bijective_of_isIso e'.hom).2.comp hιξ
    have hpsurj : Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map
          (idealModuleProductι ι G)).hom := by
      apply LinearMap.range_eq_top.mp
      rw [hrange, htop, Submodule.top_smul]
    intro m
    obtain ⟨n, hn⟩ := hpsurj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map a).hom m)
    refine ⟨n, habij.1 ?_⟩
    have he := congrArg (fun f ↦ f.hom n)
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace ξ).map_comp ψ a)
    rw [hψ] at he
    exact he.symm.trans hn
  refine ⟨r, hr, Or.inr ⟨J, ι, hι, hJ, hιξ, ψ ≫ δ, inferInstance, ?_⟩⟩
  rw [Functor.map_comp]
  exact hδbij.2.comp hψsurj

end

end AlgebraicGeometry.Scheme.Modules
