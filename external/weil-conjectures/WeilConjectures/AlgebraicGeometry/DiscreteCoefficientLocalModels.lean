/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
import WeilConjectures.AlgebraicGeometry.DiscreteConstantPresentationLifting
import WeilConjectures.AlgebraicGeometry.DiscretePointPresentationRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.WeilObject.Sheaf.Stalk

/-! # Discrete coefficient local models under section reconstruction

Source: Stacks, Tags 03CY, 00YV and 09AJ; the local finite-presentation step of
`lem-sfb-discrete-coefficient-model`.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  upperStar lowerStar CondensedRing.lowerStar CategoryTheory.Sheaf.monoidalCategory
  CondensedRing.upperStarComp upperStarFromPointComp Mod.extendScalarsIsoComapInv
  laxBraided_upperStarFromPoint monoidal_upperStarFromPoint
  smallModules coefficientModelFixedScalars Scheme.coefficientProEtaleFixedModulePullback

-- The cover argument below specializes the generic argument of IntegralSectionLocalModels.
-- Keeping the elementary cover calculation here avoids importing its integral-model holes.
-- A predicate stable under restriction defines the sieve of its local models.
private def modelSieve {C : Type (u + 1)} [SmallCategory C]
    (P : C → Prop) (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U) (V : C) : Sieve V where
  arrows U _ := P U
  downward_closed := by
    intro U W a h b
    exact hP b h

private theorem modelSieve_comparison
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (P Q : C → Prop)
    (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U)
    (hQ : ∀ {U V : C}, (U ⟶ V) → Q V → Q U)
    (T : C) (a : ∀ V, V ⟶ T)
    (forward : ∀ U, P U → ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (b : V ⟶ U), S b → Q V)
    (reverse : ∀ U, Q U → ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (b : V ⟶ U), S b → P V) :
    modelSieve P hP T ∈ J T ↔ ∀ V, modelSieve Q hQ V ∈ J V := by
  constructor
  · intro h V
    have hv : modelSieve P hP V ∈ J V := J.pullback_stable (a V) h
    apply J.transitive hv
    intro U g hg
    obtain ⟨S, hS, hs⟩ := forward U hg
    exact J.superset_covering (fun W b hb ↦ hs W b hb) hS
  · intro h
    apply J.transitive (h T)
    intro U g hg
    obtain ⟨S, hS, hs⟩ := reverse U hg
    exact J.superset_covering (fun W b hb ↦ hs W b hb) hS

private def pointModelAlong
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Z : Scheme.{u}} (g : Z ⟶ Y) : Prop :=
  ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
    Mod.IsFinitelyPresented Λ P ∧
      Nonempty (pointModelRestriction Λ f N g ≅
        (pointModelPullbackFunctor Λ Z).obj P)

private theorem pointModelAlong_stable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z W : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Z ⟶ Y) (b : W ⟶ Z) :
    pointModelAlong Λ f N g → pointModelAlong Λ f N (b ≫ g) := by
  rintro ⟨P, hP, ⟨e⟩⟩
  exact ⟨P, hP, ⟨(CondensedRing.upperStarCongr Λ (Category.assoc b g f)).app N ≪≫
    (CondensedRing.upperStarComp Λ b (g ≫ f)).app N ≪≫
    (CondensedRing.upperStar Λ b).mapIso e ≪≫
    (CondensedRing.upperStarFromPointModComp Λ b).app P⟩⟩

private theorem pointModelAlong_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ Y ((CondensedRing.upperStar Λ f).obj N) ↔
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
        ∀ i, pointModelAlong Λ f N (C.f i) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hC i
    exact ⟨P, hP, ⟨(CondensedRing.upperStarComp Λ (C.f i) f).app N ≪≫ e⟩⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨e⟩⟩ := hC i
    exact ⟨P, hP, ⟨((CondensedRing.upperStarComp Λ (C.f i) f).app N).symm ≪≫ e⟩⟩

private theorem coverPredicate_on_sieve {S : Scheme.{u}}
    (P : ∀ {Y : Scheme.{u}}, (Y ⟶ S) → Prop)
    (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ S) (b : Z ⟶ Y), P f → P (b ≫ f)) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage S, ∀ i, P (C.f i)) ↔
      ∃ V : Sieve (⊤_ S.ProEt), V ∈ Scheme.ProEt.topology S (⊤_ S.ProEt) ∧
        ∀ (U : S.ProEt) (f : U ⟶ ⊤_ S.ProEt), V f → P (Y := U.left) U.hom := by
  classical
  have hT : IsTerminal (Scheme.ProEt.mk (𝟙 S)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have t : Scheme.ProEt.mk (𝟙 S) ≅ ⊤_ S.ProEt := hT.uniqueUpToIso terminalIsTerminal
  constructor
  · rintro ⟨C, hC⟩
    let U (i : C.I₀) : S.ProEt :=
      MorphismProperty.Over.mk ⊤ (C.f i)
        ((Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀) ⟨i⟩)
    let a (i : C.I₀) : U i ⟶ ⊤_ S.ProEt :=
      (MorphismProperty.Over.homMk (B := Scheme.ProEt.mk (𝟙 S)) (C.f i)
        (by exact Category.comp_id _)) ≫ t.hom
    refine ⟨Sieve.ofArrows U a, ?_, ?_⟩
    · apply Precoverage.generate_mem_toGrothendieck
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      have : IsIso t.hom.left :=
        (Scheme.ProEt.forget S ⋙ Over.forget S).map_isIso t.hom
      change (Presieve.ofArrows (fun i ↦ C.X i)
        (fun i ↦ C.f i ≫ t.hom.left)) ∈ _
      exact (C.pushforward t.hom.left
        (Precoverage.mem_coverings_of_isIso _)).mem₀
    · intro W f hf
      obtain ⟨Z, b, c, ⟨i⟩, hbc⟩ := hf
      have hw : b.left ≫ C.f i = W.hom := MorphismProperty.Over.w b
      rw [← hw]
      exact hP (C.f i) b.left (hC i)
  · rintro ⟨V, hV, hmodels⟩
    obtain ⟨R, hR, hRV⟩ := Scheme.ProEt.mem_topology_iff.mp hV
    obtain ⟨I, U, f, rfl⟩ := R.exists_eq_ofArrows
    have hc : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        Scheme.proetalePrecoverage S := by
      let C₀ : Scheme.Cover Scheme.proetalePrecoverage (⊤_ S.ProEt).left :=
        ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (f i).left⟩, by
          simpa only [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
            Functor.comp_obj, Functor.comp_map, Scheme.ProEt.forget,
            MorphismProperty.Over.forget, MorphismProperty.Comma.forget, Over.forget,
            Comma.fst, PreZeroHypercover.presieve₀] using hR⟩
      have : IsIso t.inv.left :=
        (Scheme.ProEt.forget S ⋙ Over.forget S).map_isIso t.inv
      have he (i : I) : (f i).left ≫ t.inv.left = (U i).hom := by
        have ht := MorphismProperty.Over.w t.inv
        change t.inv.left = (⊤_ S.ProEt).hom at ht
        rw [ht]
        exact MorphismProperty.Over.w (f i)
      have h := (C₀.pushforward t.inv.left
        (Precoverage.mem_coverings_of_isIso _)).mem₀
      change (Presieve.ofArrows (fun i ↦ (U i).left)
        (fun i ↦ (f i).left ≫ t.inv.left)) ∈ _ at h
      rw [show (fun i ↦ (f i).left ≫ t.inv.left) = (fun i ↦ (U i).hom)
        from funext he] at h
      exact h
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage S :=
      ⟨⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom⟩, hc⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    let q := Precoverage.ZeroHypercover.Small.restrictFun.{u} C
    let D : Scheme.Cover.{u} Scheme.proetalePrecoverage S :=
      ⟨⟨Precoverage.ZeroHypercover.Small.Index.{u} C,
        fun i ↦ (U (q i)).left, fun i ↦ (U (q i)).hom⟩,
        Precoverage.ZeroHypercover.Small.mem₀ C⟩
    refine ⟨D, fun i ↦ ?_⟩
    let j : I := q i
    exact hmodels (U j) (f j) (hRV _ _ ⟨j⟩)

private def pointPresentationSieve
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) : Sieve V :=
  modelSieve (fun U ↦ pointModelAlong Λ f N (AsSmall.down.obj U).hom)
    (by
      intro U W b h
      rw [← MorphismProperty.Over.w (AsSmall.down.map b)]
      exact pointModelAlong_stable Λ f N _ _ h) V

private theorem pointPresentationSieve_cover_iff
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    HasFiniteConstantLocalModel Λ Y ((CondensedRing.upperStar Λ f).obj N) ↔
      pointPresentationSieve Λ f N (AsSmall.up.obj (⊤_ Y.ProEt)) ∈
        Scheme.coefficientProEtaleModelTopology.{u, u} Y (AsSmall.up.obj (⊤_ Y.ProEt)) := by
  have := Scheme.coefficientProEtaleModelUp_isContinuous.{u, u} Y
  have h := (pointModelAlong_cover Λ f N).trans
    (coverPredicate_on_sieve (pointModelAlong Λ f N)
      (fun g b ↦ pointModelAlong_stable Λ f N g b))
  rw [h]
  constructor
  · rintro ⟨S, hS, hm⟩
    have hs := (CoverPreserving.of_isContinuous
      (AsSmall.up : Y.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, u} Y)
      (Scheme.ProEt.topology Y)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)).cover_preserve hS
    apply (Scheme.coefficientProEtaleModelTopology.{u, u} Y).superset_covering ?_ hs
    intro U a ha
    obtain ⟨W, b, d, hb, _⟩ := ha
    change pointModelAlong Λ f N (AsSmall.down.obj U).hom
    rw [← MorphismProperty.Over.w (AsSmall.down.map d)]
    exact pointModelAlong_stable Λ f N _ _ (hm W b hb)
  · intro hs
    let S := pointPresentationSieve Λ f N (AsSmall.up.obj (⊤_ Y.ProEt))
    have hS := (CoverPreserving.of_isContinuous
      (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} Y ⥤ Y.ProEt)
      (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      (Scheme.ProEt.topology Y)).cover_preserve hs
    refine ⟨S.functorPushforward AsSmall.down, hS, ?_⟩
    intro U a ha
    obtain ⟨W, b, d, hb, _⟩ := ha
    rw [← MorphismProperty.Over.w d]
    exact pointModelAlong_stable Λ f N _ _ hb

private structure ScalarMatrix (k : Type (u + 1)) [CommRing k] where
  m : ℕ
  n : ℕ
  matrix : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k)

private def finiteConstantModel
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (F : Sheaf J (ModuleCat.{u + 1} k)) (U : C) : Prop :=
  ∃ M : ModuleCat.{u + 1} k, Module.Finite k M ∧
    Nonempty (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).obj M)

private def finiteConstantSieve
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (F : Sheaf J (ModuleCat.{u + 1} k))
    (V : C) : Sieve V :=
  modelSieve
    (finiteConstantModel J k F)
    (by
      intro W U b h
      obtain ⟨M, hM, ⟨e⟩⟩ := h
      refine ⟨M, hM, ⟨?_⟩⟩
      exact (Sheaf.pushforwardOverMapIso F b).symm ≪≫
        (J.overMapPullback (ModuleCat.{u + 1} k) b).mapIso e ≪≫
          ((Over.map b).pushforwardContinuousSheafificationCompatibility
            (ModuleCat.{u + 1} k) (J.over W) (J.over U)).symm.app
              ((Functor.const (Over U)ᵒᵖ).obj M)) V

private theorem finiteConstantSieve_cover_iff
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (F : Sheaf J (ModuleCat.{u + 1} k)) :
    IsCoefficientModelLocallyConstantFinite J k F ↔
      ∀ V, finiteConstantSieve J k F V ∈ J V := by
  constructor
  · intro h V
    obtain ⟨S, hS, hs⟩ := h V
    exact J.superset_covering hs hS
  · intro h V
    exact ⟨finiteConstantSieve J k F V, h V, fun U g hg ↦ hg⟩

private theorem finite_matrix_cokernel
    (k : Type (u + 1)) [CommRing k] {m n : ℕ}
    (q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k)) :
    Module.Finite k (cokernel q : ModuleCat.{u + 1} k) :=
  Module.Finite.of_surjective (cokernel.π q).hom
    ((ModuleCat.epi_iff_surjective (cokernel.π q)).mp inferInstance)

private theorem finiteConstantModel_iff_matrix
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (F : Sheaf J (ModuleCat.{u + 1} k)) (U : C) :
    finiteConstantModel J k F U ↔ ∃ d : ScalarMatrix k,
      Nonempty (F.over U ≅
        (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).obj (cokernel d.matrix)) := by
  constructor
  · rintro ⟨M, hM, ⟨iM⟩⟩
    let := hM
    let := Module.finitePresentation_of_finite k M
    obtain ⟨n, m, π, q, hπ, hq⟩ := Module.FinitePresentation.exists_fin' k M
    let q' := ModuleCat.ofHom q
    let π' : ModuleCat.of k (Fin n → k) ⟶ M := ModuleCat.ofHom π
    let i : M ≅ cokernel q' :=
      (ModuleCat.isColimitCokernelCofork q' π' hq hπ).coconePointUniqueUpToIso
        (colimit.isColimit _)
    exact ⟨⟨m, n, q'⟩,
      ⟨iM ≪≫ (constantSheaf (J.over U) (ModuleCat.{u + 1} k)).mapIso i⟩⟩
  · rintro ⟨d, hd⟩
    exact ⟨cokernel d.matrix, finite_matrix_cokernel k d.matrix, hd⟩

private theorem matrix_refinement_finite
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (k : Type (u + 1)) [CommRing k] (F : Sheaf J (ModuleCat.{u + 1} k))
    (U : C) (m n : ℕ)
    (h : ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (b : V ⟶ U), S b →
      ∃ q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k),
        Nonempty (F.over V ≅
          (constantSheaf (J.over V) (ModuleCat.{u + 1} k)).obj (cokernel q))) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (b : V ⟶ U), S b →
      finiteConstantModel J k F V := by
  obtain ⟨S, hS, hs⟩ := h
  refine ⟨S, hS, ?_⟩
  intro V b hb
  obtain ⟨q, hi⟩ := hs V b hb
  exact ⟨cokernel q, finite_matrix_cokernel k q, hi⟩

-- Bundle the ranks with their dependent matrix type to keep presentation elimination small.
private structure PresentationMatrix {D : Type*} [Category D] (free : ℕ → D) where
  m : ℕ
  n : ℕ
  matrix : free m ⟶ free n

private theorem functor_fp_models_iff_presentations
    {V : Type*} [Category V] [MonoidalCategory V] [Abelian V] [MonoidalPreadditive V]
    (R : V) [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
    {D : Type*} [Category D] (G : Mod V R ⥤ D) (M : D) :
    (∃ P : Mod V R, Mod.IsFinitelyPresented R P ∧ Nonempty (M ≅ G.obj P)) ↔
      ∃ d : PresentationMatrix (fun n ↦ Mod.finiteFree R n),
        Nonempty (M ≅ G.obj (cokernel d.matrix)) := by
  constructor
  · rintro ⟨P, ⟨n, m, d, ⟨iP⟩⟩, ⟨iM⟩⟩
    exact ⟨⟨m, n, d⟩, ⟨iM ≪≫ G.mapIso iP⟩⟩
  · rintro ⟨d, hd⟩
    exact ⟨cokernel d.matrix, ⟨d.n, d.m, d.matrix, ⟨Iso.refl _⟩⟩, hd⟩

private theorem pointModelAlong_iff_presentation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :
    pointModelAlong Λ f N (AsSmall.down.obj U).hom ↔
      ∃ d : PresentationMatrix (fun n ↦ pointModelFree Λ n),
        Nonempty
          (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
            (pointModelPullbackFunctor Λ (AsSmall.down.obj U).left).obj (cokernel d.matrix)) := by
  unfold pointModelFree
  exact functor_fp_models_iff_presentations Λ
    (pointModelPullbackFunctor Λ (AsSmall.down.obj U).left)
    (pointModelRestriction Λ f N (AsSmall.down.obj U).hom)

private structure PointPresentationData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) where
  free : ℕ → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ
  finite : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} Y,
    pointModelAlong Λ f N (AsSmall.down.obj U).hom ↔ ∃ d : PresentationMatrix free,
      Nonempty
        (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
          (pointModelPullbackFunctor Λ (AsSmall.down.obj U).left).obj (cokernel d.matrix))

private noncomputable def pointPresentationData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    PointPresentationData Λ f N where
  free := fun n ↦ pointModelFree Λ n
  finite := pointModelAlong_iff_presentation Λ f N

private theorem pointPresentationData_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (pointPresentationData Λ f N).free = (fun n ↦ pointModelFree Λ n) := rfl

attribute [local irreducible] pointModelAlong pointModelRestriction pointModelPullbackFunctor
  pointModelFree pointPresentationData

-- The cover criterion depends only on transport of specified finite presentations.
-- Abstracting the coefficient object keeps this API independent of its construction.
private structure PointPresentationComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (k : Type (u + 1)) [CommRing k]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      (ModuleCat.{u + 1} k)) where
  p : PointPresentationData Λ f N
  forward : ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
      (d : p.free m ⟶ p.free n),
      Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
        (pointModelPullbackFunctor Λ (AsSmall.down.obj U).left).obj (cokernel d)) →
      ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
        ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
          ∃ q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k),
            Nonempty (F.over V ≅ (constantSheaf
              ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over V)
                (ModuleCat.{u + 1} k)).obj (cokernel q))
  reverse : ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
      (q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k)),
      Nonempty (F.over U ≅ (constantSheaf
        ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
          (ModuleCat.{u + 1} k)).obj (cokernel q)) →
      ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
        ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
          ∃ d : p.free m ⟶ p.free n,
            Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj V).hom ≅
              (pointModelPullbackFunctor Λ (AsSmall.down.obj V).left).obj (cokernel d))

private noncomputable def pointPresentationComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (k : Type (u + 1)) [CommRing k]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      (ModuleCat.{u + 1} k))
    (hforward : ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
      (d : pointModelFree Λ m ⟶ pointModelFree Λ n),
      Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅
        (pointModelPullbackFunctor Λ (AsSmall.down.obj U).left).obj (cokernel d)) →
      ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
        ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
          ∃ q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k),
            Nonempty (F.over V ≅ (constantSheaf
              ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over V)
                (ModuleCat.{u + 1} k)).obj (cokernel q)))
    (hreverse : ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (m n : ℕ)
      (q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k)),
      Nonempty (F.over U ≅ (constantSheaf
        ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
          (ModuleCat.{u + 1} k)).obj (cokernel q)) →
      ∃ S : Sieve U, S ∈ Scheme.coefficientProEtaleModelTopology.{u, u} Y U ∧
        ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, u} Y) (g : V ⟶ U), S g →
          ∃ d : pointModelFree Λ m ⟶ pointModelFree Λ n,
            Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj V).hom ≅
              (pointModelPullbackFunctor Λ (AsSmall.down.obj V).left).obj (cokernel d))) :
    PointPresentationComparison Λ f N k F where
  p := pointPresentationData Λ f N
  forward := by
    rw [pointPresentationData_free]
    exact hforward
  reverse := by
    rw [pointPresentationData_free]
    exact hreverse

private theorem presentation_local_model_criterion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
      (ModuleCat.{u + 1} k))
    (q : PointPresentationComparison Λ f N k F) :
    HasFiniteConstantLocalModel Λ Y ((CondensedRing.upperStar Λ f).obj N) ↔
      IsCoefficientModelLocallyConstantFinite
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k F := by
  classical
  let p := q.p
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} Y
  let T : Scheme.coefficientProEtaleSiteModel.{u, u} Y := AsSmall.up.obj (⊤_ Y.ProEt)
  let P (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :=
    pointModelAlong Λ f N (AsSmall.down.obj U).hom
  let Q (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y) :=
    (finiteConstantSieve J k F U) (𝟙 U)
  have hP {U V : Scheme.coefficientProEtaleSiteModel.{u, u} Y}
      (b : U ⟶ V) (h : P V) : P U := by
    change pointModelAlong Λ f N (AsSmall.down.obj U).hom
    rw [← MorphismProperty.Over.w (AsSmall.down.map b)]
    exact pointModelAlong_stable Λ f N _ _ h
  have hQ {U V : Scheme.coefficientProEtaleSiteModel.{u, u} Y}
      (b : U ⟶ V) (h : Q V) : Q U :=
    (finiteConstantSieve J k F V).downward_closed (f := 𝟙 V) h b
  rw [pointPresentationSieve_cover_iff Λ f N, finiteConstantSieve_cover_iff J k F]
  apply modelSieve_comparison J P Q (fun b h ↦ hP b h) (fun b h ↦ hQ b h) T
    (fun V ↦ AsSmall.up.map (terminal.from (AsSmall.down.obj V)))
  · intro U h
    obtain ⟨d, hi⟩ := (p.finite U).mp h
    exact matrix_refinement_finite J k F U d.m d.n (q.forward U d.m d.n d.matrix hi)
  · intro U h
    obtain ⟨mat, hi⟩ := (finiteConstantModel_iff_matrix J k F U).mp h
    obtain ⟨R, hR, hr⟩ := q.reverse U mat.m mat.n mat.matrix hi
    refine ⟨R, hR, ?_⟩
    intro V b hb
    obtain ⟨d, hd⟩ := hr V b hb
    exact (p.finite V).mpr ⟨⟨mat.m, mat.n, d⟩, hd⟩

/-- The section-action presentation identifies finite constant local models after any
scheme restriction. This is only a local-model comparison: it asserts no stratification,
constructibility equivalence, coefficient-map existence, or tensor structure.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV; Pro-etale, Tag 09AJ;
the finite-matrix argument in step 3 of `lem-sfb-discrete-coefficient-model`.
(auxiliary; not a blueprint node).

Proof: a finitely presented internal module over the discrete condensed ring is the
cokernel of a finite matrix of scalars in A. The constant-sheaf comparison identifies
the pullback of this presentation to a scheme with its constant module presentation.
Section reconstruction and the equivalent small site preserve that cokernel and all
restrictions. Scalar restriction along c sends its finitely many matrix entries to
sections of the constant ring sheaf k. Refine the pro-etale covering so that those
entries are constant; this is possible simultaneously because the matrix is finite.
On each member the result is the constant cokernel of a finite matrix over k, hence
a finitely presented k-module. Conversely, present each finitely presented constant
k-module by a finite matrix, apply c inverse, and refine until its finitely many entries
are constant in A. The corresponding point presentation pulls back to the inverse
local model. The section equivalence and inverse image commute with localization and
with scheme pullback, so the same argument applies to f-restrictions. A scheme cover
generates covering sieves over every object; conversely a covering sieve over the
terminal object is refined by a pro-etale covering family. Over the Noetherian ring k,
finite generation and finite presentation agree. This proves both implications. For
empty schemes the empty covering works; the zero ring uses its zero presentations.
No normalization of c is needed: only finitely many coefficients must be constant on
each refinement, so even an automorphism of the constant ring sheaf is allowed.
-/
theorem discrete_coefficient_local_models
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type u) [CommRing A] (k : Type (u + 1)) [CommRing k] [IsNoetherianRing k]
    (e : ULift.{u + 1} A ≃+* k)
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj (discreteObj A) X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X)) :
    HasFiniteConstantLocalModel (discreteObj A) Y
        ((CondensedRing.upperStar (discreteObj A) f).obj N) ↔
      IsCoefficientModelLocallyConstantFinite
        (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((coefficientModelFixedScalars _ k).obj
            ((smallModules X (condensedRingObj (discreteObj A) X) ⋙
              ConstantCompletion.res c.hom).obj N))) := by
  exact presentation_local_model_criterion (discreteObj A) f N k _
    (pointPresentationComparison (discreteObj A) f N k _
      (discrete_point_presentation_refinement f A k e c N)
      (discrete_constant_presentation_lifting f A k e c N))

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
