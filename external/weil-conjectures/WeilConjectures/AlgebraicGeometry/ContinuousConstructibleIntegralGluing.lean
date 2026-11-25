/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.Devissage
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Assembling ordinary integral models along a finite stratification

Source: Bhatt--Scholze, Lemma 6.8.13 and Proposition 6.8.14(2).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Cache the canonical smallness proof before the unrelated Noetherian-category instances
-- imported by etale devissage can send instance search through an unspecified category.
private instance (priority := 2000) essentiallySmallSelfInstance
    (C : Type (u + 1)) [Category.{u} C] : CategoryTheory.EssentiallySmall.{u + 1} C :=
  CategoryTheory.essentiallySmallSelf.{0} C

section OpenPart

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

open Opposite in
private theorem mono_lan_transpose
    {P : U.ProEtᵒᵖ ⥤ Ab.{u + 1}} {Q : X.ProEtᵒᵖ ⥤ Ab.{u + 1}}
    (ψ : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lan.obj P ⟶ Q)
    (hψ : Mono
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lanUnit.app P ≫
        Functor.whiskerLeft
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op ψ)) :
    Mono ψ := by
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).Full :=
    MorphismProperty.Over.full_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _
  have : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).Faithful :=
    MorphismProperty.Over.faithful_map (P := @WeaklyEtale) (Q := ⊤) (f := j) _
  have hm (W) : Mono (ψ.app (L.obj W)) := by
    have : Mono ((L.lanUnit.app P).app W ≫ ψ.app (L.obj W)) :=
      inferInstanceAs (Mono ((L.lanUnit.app P ≫ Functor.whiskerLeft L ψ).app W))
    rw [← IsIso.inv_hom_id_assoc ((L.lanUnit.app P).app W) (ψ.app (L.obj W))]
    infer_instance
  have hall (V) : Mono (ψ.app V) := by
    rcases SmallSite.mem_essImage_or_isEmpty_costructuredArrow_op_overMap
        (inferInstance : WeaklyEtale j) V with ⟨W, ⟨e⟩⟩ | hV
    · have := hm W
      have h : Mono ((L.lan.obj P).map e.hom ≫ ψ.app V) := by
        rw [ψ.naturality]
        infer_instance
      rw [← IsIso.inv_hom_id_assoc ((L.lan.obj P).map e.hom) (ψ.app V)]
      infer_instance
    · have := hV
      exact ((isColimitEquivIsInitialOfIsEmpty Ab.{u + 1} _).1
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit P V)).isZero.mono _
  exact NatTrans.mono_of_mono_app ψ

private theorem mono_restriction_counit
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    Mono ((ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j).counit.app F) := by
  let adj := sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}
  let ε := (ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j).counit.app F
  let ψ := adj.homEquiv _ _ ε
  have hψ : Mono ψ := by
    apply mono_lan_transpose j
    have hunit (G : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
        (sheafToPresheaf _ _).map
          ((ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j).unit.app G) =
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lanUnit.app G.obj ≫
          Functor.whiskerLeft
            (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op
            (toSheafify _ ((MorphismProperty.Over.map ⊤
              (inferInstance : WeaklyEtale j)).op.lan.obj G.obj)) := by
      dsimp only [ProEtale.openImmersionLowerShriekAdjunction,
        ProEtale.localizationLowerShriekAdjunction,
        Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
      erw [Adjunction.map_restrictFullyFaithful_unit_app]
      simp [Functor.lanAdjunction_unit]
    have heq :
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.lanUnit.app _ ≫
          Functor.whiskerLeft
            (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op ψ =
        𝟙 _ := by
      calc
        _ = (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1}).map
            ((ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j).unit.app
                ((ProEtale.openImmersionRestriction Ab.{u + 1} j).obj F) ≫
              (ProEtale.openImmersionRestriction Ab.{u + 1} j).map ε) := by
          rw [Functor.map_comp, hunit, Category.assoc]
          rfl
        _ = _ := by
          rw [(ProEtale.openImmersionLowerShriekAdjunction
            Ab.{u + 1} j).right_triangle_components]
          exact (sheafToPresheaf (Scheme.ProEt.topology U) Ab.{u + 1}).map_id _
    rw [heq]
    infer_instance
  have heq : ε = (presheafToSheaf _ Ab.{u + 1}).map ψ ≫ adj.counit.app F := by
    exact ((adj.homEquiv _ _).symm_apply_apply ε).symm.trans (adj.homEquiv_counit (g := ψ))
  change Mono ε
  rw [heq]
  infer_instance

private theorem mono_ab_counit (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    Mono ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).counit.app F) := by
  have := mono_restriction_counit j F
  change Mono (_ ≫ (ProEtale.openImmersionLowerShriekAdjunction
    Ab.{u + 1} j).counit.app F)
  infer_instance

omit [IsCommMonObj Λ] in
private theorem mono_linear_counit
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F) := by
  have : Mono ((Mod.forget _).map
      ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F)) := by
    change Mono (((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      Ab.{u + 1} j).homEquiv _ F.X).symm (𝟙 _))
    rw [Adjunction.homEquiv_symm_id]
    exact mono_ab_counit j F.X
  exact (Mod.forget _).mono_of_mono_map inferInstance

private theorem mono_condensed_counit
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app F) := by
  have := mono_linear_counit Λ j F
  change Mono (_ ≫
    (linearOpenImmersionLowerShriek Λ j).map
      ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).counit.app _) ≫
    (linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F)
  have : (Mod.comap (condensedPullbackHom Λ j)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).isEquivalence_functor
  have : IsIso (Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).counit :=
    inferInstance
  exact mono_comp' (IsIso.mono_of_iso _)
    (mono_comp' (IsIso.mono_of_iso _) (mono_linear_counit Λ j F))

private theorem iso_condensed_counit [IsIso j]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app F) := by
  have hab : IsIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      Ab.{u + 1} j).counit.app F.X) := inferInstance
  have hlin : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F) := by
    have hh : IsIso ((Mod.forget _).map
        ((linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F)) := by
      change IsIso (((ProEtale.openImmersionLowerShriekUpperStarAdjunction
        Ab.{u + 1} j).homEquiv _ F.X).symm (𝟙 _))
      rw [Adjunction.homEquiv_symm_id]
      exact hab
    exact isIso_of_reflects_iso _ (Mod.forget _)
  change IsIso (_ ≫
    (linearOpenImmersionLowerShriek Λ j).map
      ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ j)).counit.app _) ≫
    (linearOpenImmersionLowerShriekAdjunction Λ j).counit.app F)
  have : (Mod.comap (condensedPullbackHom Λ j)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).isEquivalence_functor
  infer_instance

private theorem module_zero_of_empty {Y : Scheme.{u}} [IsEmpty Y]
    (R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) R) : IsZero M := by
  have hX : IsZero M.X := by
    apply Sheaf.isZero_of_isZero_obj
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ (inferInstance : IsEmpty Y).false (T.hom t)⟩
    exact (isZero_zero _).of_iso
      ((Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).uniqueUpToIso
        HasZeroObject.zeroIsTerminal)
  exact (IsZero.iff_id_eq_zero _).2 (Mod.hom_ext _ _ (hX.eq_of_src _ _))

end OpenPart

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

private theorem constructible_of_extend_iso
    {X : Scheme.{u}} {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj T] [IsCommMonObj R]
    (α : R ⟶ T) [IsMonHom α] [IsIso α] (M : Mod _ R)
    (hM : IsConstructibleModuleObject T ((Mod.extendScalars α).obj M)) :
    IsConstructibleModuleObject R M := by
  have hh := _root_.constructible_of_iso ((Mod.extendScalarsIsoComapInv α).app M) hM
  exact _root_.constructible_of_iso
    (((Mod.comapComp α (inv α)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id α) ≪≫ Mod.comapId R).app M)
    (_root_.constructible_comap α hh)

private theorem closed_push_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ Z) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) ((i)_*⟦Λ⟧.obj M) := by
  have hc := moduleCounitOfAbelian Λ i
    (ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i)
  apply ProEtale.constructible_of_restrictions j i (by simp only [hij, compl_compl])
  · apply constructible_of_extend_iso (condensedPullbackHom Λ j)
    exact ProEtale.isConstructibleModuleObject_of_isZero _
      (openRestrictionPushforwardZero Λ i j hij M)
  · apply constructible_of_extend_iso (condensedPullbackHom Λ i)
    exact _root_.constructible_of_iso
      (asIso ((upperStarLowerStarAdjunction Λ i).counit.app M)).symm hM

private theorem supported_unit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero ((j)^*⟦Λ⟧.obj M)) :
    IsIso ((upperStarLowerStarAdjunction Λ i).unit.app M) := by
  apply moduleUnitOfAbelian Λ i M
  apply ProEtale.abelian_closed_support i j hij
  exact ((Mod.forget _).map_isZero hM).of_iso
    ((profinitePointModuleForgetPullbackIso Λ j).app M).symm

private theorem closed_pull_open_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U Z : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((i)^*⟦Λ⟧.obj ((j)_!open⟦Λ⟧.obj M)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply ((upperStarLowerStarAdjunction Λ i).homEquiv _ _).injective
  apply ((openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).injective
  exact (openRestrictionPushforwardZero Λ i j hij _).eq_of_tgt _ _

private theorem immersion_factor_of_reduced
    {X Y Z : Scheme.{u}} [IsReduced Z] (i : Y ⟶ X) [IsImmersion i]
    (f : Z ⟶ X) (h : Set.range f ⊆ Set.range i) : ∃ g : Z ⟶ Y, g ≫ i = f := by
  let f' := IsOpenImmersion.lift i.coborderRange.ι f
    (h.trans (by
      rw [Scheme.Opens.range_ι]
      change Set.range i ⊆ coborder (Set.range i)
      exact subset_coborder))
  have hf : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hr : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨z, rfl⟩
    refine ⟨y, i.coborderRange.ι.isEmbedding.injective ?_⟩
    exact (congrArg (fun k : Y ⟶ X ↦ k y) i.liftCoborder_ι).trans
      (hy.trans (congrArg (fun k : Z ⟶ X ↦ k z) hf).symm)
  obtain ⟨g, hg, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range
    i.liftCoborder f' hr
  exact ⟨g, by rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf]⟩

private theorem open_cokernel_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero ((j)^*⟦Λ⟧.obj
      (cokernel ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app F))) := by
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ j
  have hu := openUnitIsIso Λ j
  have h := adj.right_triangle_components F
  have hh : IsIso (adj.unit.app ((j)^*⟦Λ⟧.obj F) ≫
      (j)^*⟦Λ⟧.map (adj.counit.app F)) := by
    rw [h]
    exact IsIso.id _
  have : IsIso ((j)^*⟦Λ⟧.map (adj.counit.app F)) :=
    IsIso.of_isIso_comp_left (adj.unit.app _) _
  have : Epi ((j)^*⟦Λ⟧.map (adj.counit.app F)) := IsIso.epi_of_iso _
  exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (j)^*⟦Λ⟧ _)

private noncomputable def closed_cokernel_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X U Z : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (i)^*⟦Λ⟧.obj F ≅ (i)^*⟦Λ⟧.obj
      (cokernel ((openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app F)) := by
  let f := (openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app F
  have hz := closed_pull_open_zero Λ i j hij ((j)^*⟦Λ⟧.obj F)
  have heq : (i)^*⟦Λ⟧.map f = 0 := hz.eq_of_src _ _
  have : IsIso (cokernel.π ((i)^*⟦Λ⟧.map f)) := by
    rw [heq]
    infer_instance
  exact asIso (cokernel.π ((i)^*⟦Λ⟧.map f)) ≪≫
    (PreservesCokernel.iso (i)^*⟦Λ⟧ f).symm

omit [FiniteDimensional ℚ_[ℓ] E] in
private theorem integral_model_of_supported_restriction
    {X U Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hF : IsZero ((j)^*⟦Profinite.continuousMapRingObj E⟧.obj F))
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Z))
    (hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Z) N)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Z)).obj N ≅
      (i)^*⟦Profinite.continuousMapRingObj E⟧.obj F) :
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj M ≅ F) := by
  let M := (i)_*⟦integralCoeff ℓ E⟧.obj N
  let T := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)
  have hz : IsZero ((j)^*⟦Profinite.continuousMapRingObj E⟧.obj (T.obj M)) :=
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U) |>.map_isZero
      (openRestrictionPushforwardZero (integralCoeff ℓ E) i j hij N)).of_iso
        ((pullIso (integralScalarMap ℓ E) j).app M).symm
  have hunitM := supported_unit (Profinite.continuousMapRingObj E) i j hij (T.obj M) hz
  have hunitF := supported_unit (Profinite.continuousMapRingObj E) i j hij F hF
  have hc := moduleCounitOfAbelian (integralCoeff ℓ E) i
    (ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i)
  let er := ((pullIso (integralScalarMap ℓ E) i).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Z)).mapIso
      (asIso ((upperStarLowerStarAdjunction (integralCoeff ℓ E) i).counit.app N)) ≪≫ e
  exact ⟨M, closed_push_constructible (integralCoeff ℓ E) i j hij N hN,
    ⟨asIso ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) i).unit.app
        (T.obj M)) ≪≫
      (i)_*⟦Profinite.continuousMapRingObj E⟧.mapIso er ≪≫
      (asIso ((upperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) i).unit.app
        F)).symm⟩⟩

omit [FiniteDimensional ℚ_[ℓ] E] in
private theorem raw_model_to_condensed
    {X Y : Scheme.{u}} (i : Y ⟶ X)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)))
    (hN : IsConstructibleModuleObject
      ((ProEtale.upperStar Ab.{u + 1} i).obj (condensedRingObj (integralCoeff ℓ E) X)) N)
    (e : (Mod.extendScalars ((ProEtale.upperStar Ab.{u + 1} i).map
        (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅
      ((ProEtale.upperStar Ab.{u + 1} i).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj F) :
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y),
      IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj M ≅
        (i)^*⟦Profinite.continuousMapRingObj E⟧.obj F) := by
  let α := condensedPullbackHom (integralCoeff ℓ E) i
  let β := condensedPullbackHom (Profinite.continuousMapRingObj E) i
  let φ := (ProEtale.upperStar Ab.{u + 1} i).map
    (coefficientMap (integralScalarMap ℓ E) X)
  let M := (Mod.extendScalars α).obj N
  have hM : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y) M :=
    _root_.constructible_of_iso ((Mod.extendScalarsIsoComapInv α).app N).symm
      (_root_.constructible_comap (inv α) hN)
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((Mod.extendScalarsComp α (coefficientMap (integralScalarMap ℓ E) Y)).app N).symm ≪≫
    (Mod.extendScalarsIsoOfEq
      (map_coefficientMap_comp_condensedPullbackHom (integralScalarMap ℓ E) i).symm).app N ≪≫
    (Mod.extendScalarsComp φ β).app N ≪≫ (Mod.extendScalars β).mapIso e

/-- Keep the reduced closed-complement scheme abstract when using its geometric properties. -/
private theorem closed_difference_data
    (X : Scheme.{u}) (W₀ W : X.Opens) (h : W₀ ≤ W) :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ W), IsClosedImmersion k ∧ IsReduced Z ∧
      Set.range (X.homOfLE h) = (Set.range k)ᶜ ∧
      Set.range (k ≫ W.ι) ⊆ (W : Set X) \ W₀ := by
  let j := X.homOfLE h
  let k := j.closedComplement
  have hcompl : Set.range j = (Set.range k)ᶜ := by
    simp only [k, Scheme.Hom.range_closedComplement, compl_compl]
  have hr : Set.range (k ≫ W.ι) ⊆ (W : Set X) \ W₀ := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(k z).property, fun hz ↦ ?_⟩
    have hk : k z ∈ (Set.range j)ᶜ := by
      rw [← Scheme.Hom.range_closedComplement]
      exact ⟨z, rfl⟩
    apply hk
    refine ⟨⟨(k z).val, hz⟩, W.ι.isEmbedding.injective ?_⟩
    change (j ≫ W.ι) _ = W.ι (k z)
    rw [X.homOfLE_ι h]
    rfl
  have hred := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
    (X := W.toScheme) ⟨(j.opensRange : Set W.toScheme)ᶜ,
      j.opensRange.isOpen.isClosed_compl⟩
  exact ⟨_, k, inferInstance, hred, hcompl, hr⟩

omit [FiniteDimensional ℚ_[ℓ] E] in
-- Keep the final quotient explicit: comparing its aliases beneath j_! unfolds
-- the large extension functor during kernel checking.
private theorem open_difference_model
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    {Y : Scheme.{u}} (i : Y ⟶ X) [IsImmersion i]
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y))
    (hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) Y) N)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y)).obj N ≅
      (i)^*⟦Profinite.continuousMapRingObj E⟧.obj F)
    (W₀ W : X.Opens) (h : W₀ ≤ W) (hs : (W : Set X) \ W₀ ⊆ Set.range i) :
    ∃ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj M ≅
        (W.ι)_!open⟦Profinite.continuousMapRingObj E⟧.obj (cokernel
          ((openImmersionLowerShriekUpperStarAdjunction
            (Profinite.continuousMapRingObj E) (X.homOfLE h)).counit.app
            ((W.ι)^*⟦Profinite.continuousMapRingObj E⟧.obj F)))) := by
  have : TopologicalSpace.NoetherianSpace W₀.toScheme := W₀.ι.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace W.toScheme := W.ι.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact (X.homOfLE h) := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have : QuasiCompact W.ι := ⟨fun V _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨Z, k, hk, hred, hcompl, hr⟩ := closed_difference_data X W₀ W h
  let := hk
  let := hred
  obtain ⟨g, hg⟩ := immersion_factor_of_reduced i (k ≫ W.ι) (hr.trans hs)
  let NW := (g)^*⟦integralCoeff ℓ E⟧.obj N
  have hNW := isConstructibleModuleObject_upperStar (integralCoeff ℓ E) g N hN
  let er : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) _)).obj NW ≅
      (k)^*⟦Profinite.continuousMapRingObj E⟧.obj (cokernel
      ((openImmersionLowerShriekUpperStarAdjunction
        (Profinite.continuousMapRingObj E) (X.homOfLE h)).counit.app
        ((W.ι)^*⟦Profinite.continuousMapRingObj E⟧.obj F))) :=
    (pullIso (integralScalarMap ℓ E) g).app N ≪≫
      (g)^*⟦Profinite.continuousMapRingObj E⟧.mapIso e ≪≫
      ((upperStarComp (Profinite.continuousMapRingObj E) g i).app F).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar (Profinite.continuousMapRingObj E) f).obj F) hg) ≪≫
      (upperStarComp (Profinite.continuousMapRingObj E) k W.ι).app F ≪≫
      closed_cokernel_iso (Profinite.continuousMapRingObj E) k (X.homOfLE h) hcompl
        ((W.ι)^*⟦Profinite.continuousMapRingObj E⟧.obj F)
  obtain ⟨M, hM, ⟨eM⟩⟩ := integral_model_of_supported_restriction ℓ E k
    (X.homOfLE h) hcompl (cokernel ((openImmersionLowerShriekUpperStarAdjunction
        (Profinite.continuousMapRingObj E) (X.homOfLE h)).counit.app
        ((W.ι)^*⟦Profinite.continuousMapRingObj E⟧.obj F)))
    (open_cokernel_zero (Profinite.continuousMapRingObj E) (X.homOfLE h)
      ((W.ι)^*⟦Profinite.continuousMapRingObj E⟧.obj F)) NW hNW er
  exact ⟨(W.ι)_!open⟦integralCoeff ℓ E⟧.obj M,
    isConstructibleModuleObject_openImmersionLowerShriek (integralCoeff ℓ E) W.ι M hM,
    ⟨(openImmersionShriekIso (integralScalarMap ℓ E) W.ι).app M ≪≫
      (W.ι)_!open⟦Profinite.continuousMapRingObj E⟧.mapIso eM⟩⟩

omit [FiniteDimensional ℚ_[ℓ] E] in
private theorem single_integral_image (X : Scheme.{u})
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hM : ProEtale.IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj M ≅ F) :
    (((ProEtale.boundedConstructible (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙
      integralScalarExtension ℓ E X).essImage) ((DerivedCategory.singleFunctor _ 0).obj F) := by
  let K : integralConstructible ℓ E X :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj M, by
      rw [ProEtale.mem_boundedConstructible_iff]
      refine ⟨⟨0, 0, ?_⟩, ?_⟩
      · intro i hi
        rcases hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
      · intro i
        rcases eq_or_ne i 0 with rfl | hi
        · exact _root_.constructible_of_iso
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
        · rcases lt_or_gt_of_ne hi with hi | hi
          · exact ProEtale.isConstructibleModuleObject_of_isZero _
              (DerivedCategory.isZero_of_isGE _ 0 i hi)
          · exact ProEtale.isConstructibleModuleObject_of_isZero _
              (DerivedCategory.isZero_of_isLE _ 0 i hi)⟩
  refine ⟨K, ⟨?_⟩⟩
  exact (Functor.singleFunctorCompLeftDerivedFunctorIso
    (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X))).app M ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso e

omit [FiniteDimensional ℚ_[ℓ] E] in
private theorem extract_model (X : Scheme.{u})
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (K : integralConstructible ℓ E X)
    (e : (integralScalarExtension ℓ E X).obj K.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj F) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      ProEtale.IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ F) := by
  refine ⟨(DerivedCategory.homologyFunctor _ 0).obj K.obj, K.property.2 0, ⟨?_⟩⟩
  exact (Functor.leftDerivedFunctorHomologyFunctorIso
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)) 0).app K.obj ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F

private theorem filtration_mem {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C]
    (P : ObjectProperty (DerivedCategory C)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (F : C) (m : ℕ) (Fil : Fin (m + 1) → Subobject F) (hm : Monotone Fil)
    (h0 : IsZero (Subobject.underlying.obj (Fil 0))) (hlast : Fil (Fin.last m) = ⊤)
    (hgraded : ∀ (r : Fin m) (h : Fil r.castSucc ≤ Fil r.succ),
      P ((DerivedCategory.singleFunctor _ 0).obj (cokernel (Subobject.ofLE _ _ h)))) :
    P ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have hFil (i : Fin (m + 1)) :
      P ((DerivedCategory.singleFunctor _ 0).obj (Subobject.underlying.obj (Fil i))) := by
    induction i using Fin.induction with
    | zero => exact P.prop_of_isZero ((DerivedCategory.singleFunctor _ 0).map_isZero h0)
    | succ i ih =>
      let f := Subobject.ofLE _ _ (hm (Fin.castSucc_le_succ i))
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact := by
        exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f) inferInstance
          inferInstance
      exact P.ext_of_isTriangulatedClosed₂ _ hS.singleTriangle_distinguished ih
        (hgraded i _)
  have htop := hFil (Fin.last m)
  rw [hlast] at htop
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    (asIso (⊤ : Subobject F).arrow)) htop

private theorem stratification_mem
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (S : Scheme.Stratification X)
    (P : ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hstep : ∀ (W₀ W : X.Opens) (h : W₀ ≤ W) (a : Fin S.n),
      (W : Set X) \ W₀ ⊆ S.stratum a →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((W.ι)_!open⟦Λ⟧.obj (cokernel
          ((openImmersionLowerShriekUpperStarAdjunction Λ (X.homOfLE h)).counit.app
            ((W.ι)^*⟦Λ⟧.obj F)))))) :
    P ((DerivedCategory.singleFunctor _ 0).obj F) := by
  obtain ⟨m, V, hV0, hVm, hstepV⟩ :=
    Topology.Stratification.exists_chain_opens S.toStratification (⊥ : X.Opens)
  let ε (W : X.Opens) :=
    (openImmersionLowerShriekUpperStarAdjunction Λ W.ι).counit.app F
  have hε (W : X.Opens) : Mono (ε W) := mono_condensed_counit Λ W.ι F
  have hfac (W₀ W : X.Opens) (h : W₀ ≤ W) :
      ∃ α : (W₀.ι)_!open⟦Λ⟧.obj ((W₀.ι)^*⟦Λ⟧.obj F) ≅
          (W.ι)_!open⟦Λ⟧.obj ((X.homOfLE h)_!open⟦Λ⟧.obj
            ((X.homOfLE h)^*⟦Λ⟧.obj ((W.ι)^*⟦Λ⟧.obj F))),
        ε W₀ = α.hom ≫ (W.ι)_!open⟦Λ⟧.map
          ((openImmersionLowerShriekUpperStarAdjunction Λ (X.homOfLE h)).counit.app
            ((W.ι)^*⟦Λ⟧.obj F)) ≫ ε W := by
    obtain ⟨α, hα⟩ := Adjunction.exists_iso_counit_app
      (openImmersionLowerShriekUpperStarAdjunction Λ W₀.ι)
      ((openImmersionLowerShriekUpperStarAdjunction Λ (X.homOfLE h)).comp
        (openImmersionLowerShriekUpperStarAdjunction Λ W.ι))
      (eqToIso (congrArg (upperStar Λ) (X.homOfLE_ι h).symm) ≪≫
        upperStarComp Λ (X.homOfLE h) W.ι) F
    exact ⟨α, hα.trans (by rw [Adjunction.comp_counit_app])⟩
  have hle (W₀ W : X.Opens) (h : W₀ ≤ W) :
      Subobject.mk (ε W₀) ≤ Subobject.mk (ε W) := by
    obtain ⟨α, hα⟩ := hfac W₀ W h
    exact Subobject.mk_le_mk_of_comm (α.hom ≫ _) (by rw [hα, Category.assoc])
  have hmono : Monotone V := Fin.monotone_iff_le_succ.mpr fun r ↦ (hstepV r).1
  apply filtration_mem P F m (fun r ↦ Subobject.mk (ε (V r)))
    (fun a b hab ↦ hle _ _ (hmono hab))
  · have hzero : IsZero (((Scheme.Opens.ι (V 0)))^*⟦Λ⟧.obj F) := by
      rw [hV0]
      have : IsEmpty (⊥ : X.Opens).toScheme :=
        ⟨fun x ↦ TopologicalSpace.Opens.mem_bot.mp x.2⟩
      exact module_zero_of_empty _ _
    exact (((Scheme.Opens.ι (V 0)))_!open⟦Λ⟧.map_isZero hzero).of_iso (Subobject.underlyingIso _)
  · have : IsIso (ε (V (Fin.last m))) := by
      change IsIso ((openImmersionLowerShriekUpperStarAdjunction Λ
        (Scheme.Opens.ι (V (Fin.last m)))).counit.app F)
      rw [hVm]
      have : IsIso (Scheme.Opens.ι (⊤ : X.Opens)) :=
        inferInstanceAs (IsIso X.topIso.hom)
      exact iso_condensed_counit Λ _ F
    exact Subobject.mk_eq_top_of_isIso _
  · intro r h
    obtain ⟨hWW, a, ha⟩ := hstepV r
    obtain ⟨α, hα⟩ := hfac _ _ hWW
    let φ := (openImmersionLowerShriekUpperStarAdjunction Λ (X.homOfLE hWW)).counit.app
      (((Scheme.Opens.ι (V r.succ)))^*⟦Λ⟧.obj F)
    let e := Subobject.cokernelOfLEMkIso _ _ α _ hα h ≪≫
      (PreservesCokernel.iso ((Scheme.Opens.ι (V r.succ)))_!open⟦Λ⟧ φ).symm
    exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e).symm
      (hstep _ _ hWW a ha)

/-- Constructible ordinary integral models on the parts of a finite stratification
suffice to construct an ordinary integral model of the whole rational sheaf.
Source: Bhatt--Scholze, the filtration and Ext1 argument at the end of Lemma 6.8.13
and the essential-surjectivity argument of Proposition 6.8.14(2).
(auxiliary; not a blueprint node)

Proof in words. Noetherian induction produces a finite increasing chain of opens from
empty to X whose successive differences lie in individual strata. The counits
j_! j^* F → F are monic: in the open site inclusion, the Kan-extension unit is
invertible on its essential image and the other comma categories are empty.
Composition of adjunctions makes their image subobjects increasing. Their initial
term is zero, their final term is F, and each quotient is the outer open extension
of the cokernel for the inclusion of two successive opens.

For one difference, take its reduced closed complement Z inside the larger open.
Its map to X factors through the given stratum immersion: first lift to the
coborder open and then use reduced-source factorization through a closed immersion.
Transport the supplied lattice across the coefficient isomorphism and pull it back
to Z. Closed pushforward preserves constructibility by combining the given closed
stratification and zero on the complementary open. Rationalization of this closed
pushforward is supported on Z because scalar extension commutes with pullback.
The closed counit identifies its closed restriction with the supplied rational
lattice. The supported unit then identifies its rationalization with the desired
cokernel. Extending along the outer open preserves constructibility and commutes
with scalar extension. This constructs integral models for all graded pieces
without requiring a closed-pushforward filtered-colimit comparison.

The degree-zero complexes of these lattices are bounded integral constructible.
Short exact sequences in the finite filtration give distinguished triangles.
The triangulated integral-image theorem, which incorporates denominator clearing,
therefore gives a bounded integral constructible K rationalizing to F[0]. Set
N = H⁰(K). Constructibility follows from the definition of the bounded subcategory,
and exact scalar extension identifies its rationalization with H⁰(F[0]) = F.
Zero and empty pieces are included. The supplied lattices are only used to produce
graded-piece models; they need not themselves glue unchanged. -/
theorem continuousConstructible_integral_gluing (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (S : Scheme.Stratification X)
    (hmodels : ∀ a : Fin S.n,
      ∃ N : Mod (Sheaf (Scheme.ProEt.topology (S.domain a)) Ab.{u + 1})
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (integralCoeff ℓ E) X)),
        ProEtale.IsConstructibleModuleObject
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj
            (condensedRingObj (integralCoeff ℓ E) X)) N ∧
        Nonempty ((Mod.extendScalars
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map
            (coefficientMap (integralScalarMap ℓ E) X))).obj N ≅
          ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod
            (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj F)) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      ProEtale.IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) N ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ F) := by
  let P := ((ProEtale.boundedConstructible
    (condensedRingObj (integralCoeff ℓ E) X)).ι ⋙ integralScalarExtension ℓ E X).essImage
  have : P.IsTriangulated := continuousConstructible_integral_image_triangulated ℓ E X
  have hF : P ((DerivedCategory.singleFunctor _ 0).obj F) := by
    apply stratification_mem (Profinite.continuousMapRingObj E) X F S P
    intro W₀ W h a hs
    obtain ⟨N, hN, ⟨eN⟩⟩ := hmodels a
    obtain ⟨M, hM, ⟨eM⟩⟩ := raw_model_to_condensed ℓ E (S.immersion a) F N hN eN
    obtain ⟨L, hL, ⟨eL⟩⟩ := open_difference_model ℓ E X F (S.immersion a) M hM eM
      W₀ W h (by simpa only [S.range_immersion] using hs)
    exact single_integral_image ℓ E X _ L hL eL
  obtain ⟨K, ⟨eK⟩⟩ := hF
  exact extract_model ℓ E X F K eK

end AlgebraicGeometry.ProEtale.CondensedRing
