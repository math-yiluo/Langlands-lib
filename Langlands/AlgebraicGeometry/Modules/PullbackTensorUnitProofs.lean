import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitStatements
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

local instance pullbackTensorUnitProofsMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
lemma tensorHomEquiv_leftUnitor (M : X.Modules) :
    tensorHomEquiv (structureSheaf X) M M (tensorLeftUnitor M).hom =
      (λ_ M.val).hom := by
  exact ((sheafifyAdjunction X).homEquiv _ M).apply_symm_apply (λ_ M.val).hom

set_option backward.isDefEq.respectTransparency false in
lemma tensorHomEquiv_rightUnitor (M : X.Modules) :
    tensorHomEquiv M (structureSheaf X) M (tensorRightUnitor M).hom =
      (ρ_ M.val).hom := by
  exact ((sheafifyAdjunction X).homEquiv _ M).apply_symm_apply (ρ_ M.val).hom

set_option backward.isDefEq.respectTransparency false in
lemma pushforwardTensor_leftUnitor (f : X ⟶ Y) (P : X.Modules) :
    tensorMap (unitToPushforwardUnit f) (𝟙 ((Scheme.Modules.pushforward f).obj P)) ≫
        pushforwardTensorApp f (structureSheaf X) P ≫
        (Scheme.Modules.pushforward f).map (tensorLeftUnitor P).hom =
      (tensorLeftUnitor ((Scheme.Modules.pushforward f).obj P)).hom := by
  apply (tensorHomEquiv _ _ _).injective
  erw [tensorHomEquiv_tensorMap_comp, tensorHomEquiv_comp,
    tensorHomEquiv_pushforwardTensorApp, tensorHomEquiv_leftUnitor]
  refine PresheafOfModules.hom_ext
    (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun r p => ?_))
  have h := tensorHomEquiv_leftUnitor P
  change tensorSheafifyUnit (structureSheaf X) P ≫ (tensorLeftUnitor P).hom.val =
    (λ_ P.val).hom at h
  have h' := congrArg
    (fun k => (k.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom
      ((f.c.app U).hom r ⊗ₜ p)) h
  exact h'

set_option backward.isDefEq.respectTransparency false in
lemma pushforwardTensor_rightUnitor (f : X ⟶ Y) (P : X.Modules) :
    tensorMap (𝟙 ((Scheme.Modules.pushforward f).obj P)) (unitToPushforwardUnit f) ≫
        pushforwardTensorApp f P (structureSheaf X) ≫
        (Scheme.Modules.pushforward f).map (tensorRightUnitor P).hom =
      (tensorRightUnitor ((Scheme.Modules.pushforward f).obj P)).hom := by
  apply (tensorHomEquiv _ _ _).injective
  erw [tensorHomEquiv_tensorMap_comp, tensorHomEquiv_comp,
    tensorHomEquiv_pushforwardTensorApp, tensorHomEquiv_rightUnitor]
  refine PresheafOfModules.hom_ext
    (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun p r => ?_))
  have h := tensorHomEquiv_rightUnitor P
  change tensorSheafifyUnit P (structureSheaf X) ≫ (tensorRightUnitor P).hom.val =
    (ρ_ P.val).hom at h
  have h' := congrArg
    (fun k => (k.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom
      (p ⊗ₜ (f.c.app U).hom r)) h
  exact h'

set_option backward.isDefEq.respectTransparency false in
lemma pullbackTensorLeftUnitor : PullbackTensorLeftUnitorStatement.{u} := by
  intro X Y f M
  have hu := pullbackUnitAdjunction X Y f
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y) ≫
    (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      unitToPushforwardUnit f at hu
  have hn := pushforwardTensorApp_naturality f (pullbackUnitIso f).hom
    (𝟙 ((Scheme.Modules.pullback f).obj M))
  change tensorMap ((Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom)
      ((Scheme.Modules.pushforward f).map (𝟙 ((Scheme.Modules.pullback f).obj M))) ≫
      pushforwardTensorApp f (structureSheaf X) ((Scheme.Modules.pullback f).obj M) =
    pushforwardTensorApp f ((Scheme.Modules.pullback f).obj (structureSheaf Y))
      ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pushforward f).map
        (tensorMap (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M))) at hn
  rw [CategoryTheory.Functor.map_id] at hn
  have hn' := congrArg
    (fun k => k ≫ (Scheme.Modules.pushforward f).map
      (tensorLeftUnitor ((Scheme.Modules.pullback f).obj M)).hom) hn
  simp only [Category.assoc] at hn'
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackTensorComparisonApp,
    Functor.map_comp, Category.assoc]
  rw [← hn', ← Category.assoc, tensorMap_comp]
  erw [Category.comp_id, hu]
  rw [Adjunction.homEquiv_unit,
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]
  have hl := pushforwardTensor_leftUnitor f ((Scheme.Modules.pullback f).obj M)
  calc
    _ = tensorMap (𝟙 (structureSheaf Y))
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (tensorMap (unitToPushforwardUnit f)
          (𝟙 ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M))) ≫
          pushforwardTensorApp f (structureSheaf X) ((Scheme.Modules.pullback f).obj M) ≫
          (Scheme.Modules.pushforward f).map
            (tensorLeftUnitor ((Scheme.Modules.pullback f).obj M)).hom) := by
      symm
      rw [← Category.assoc, tensorMap_comp]
      erw [Category.id_comp, Category.comp_id]
    _ = _ := by
      rw [hl, tensorLeftUnitor_naturality]
      rfl


set_option backward.isDefEq.respectTransparency false in
lemma pullbackTensorRightUnitor : PullbackTensorRightUnitorStatement.{u} := by
  intro X Y f M
  have hu := pullbackUnitAdjunction X Y f
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y) ≫
    (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      unitToPushforwardUnit f at hu
  have hn := pushforwardTensorApp_naturality f
    (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackUnitIso f).hom
  change tensorMap ((Scheme.Modules.pushforward f).map (𝟙 ((Scheme.Modules.pullback f).obj M)))
      ((Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom) ≫
      pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M) (structureSheaf X) =
    pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj (structureSheaf Y)) ≫
      (Scheme.Modules.pushforward f).map
        (tensorMap (𝟙 ((Scheme.Modules.pullback f).obj M)) (pullbackUnitIso f).hom) at hn
  rw [CategoryTheory.Functor.map_id] at hn
  have hn' := congrArg
    (fun k => k ≫ (Scheme.Modules.pushforward f).map
      (tensorRightUnitor ((Scheme.Modules.pullback f).obj M)).hom) hn
  simp only [Category.assoc] at hn'
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackTensorComparisonApp,
    Functor.map_comp, Category.assoc]
  rw [← hn', ← Category.assoc, tensorMap_comp]
  erw [Category.comp_id, hu]
  rw [Adjunction.homEquiv_unit,
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]
  have hr := pushforwardTensor_rightUnitor f ((Scheme.Modules.pullback f).obj M)
  calc
    _ = tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          (𝟙 (structureSheaf Y)) ≫
        (tensorMap
          (𝟙 ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M)))
          (unitToPushforwardUnit f) ≫
          pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M) (structureSheaf X) ≫
          (Scheme.Modules.pushforward f).map
            (tensorRightUnitor ((Scheme.Modules.pullback f).obj M)).hom) := by
      symm
      rw [← Category.assoc, tensorMap_comp]
      erw [Category.id_comp, Category.comp_id]
    _ = _ := by
      rw [hr, tensorRightUnitor_naturality]
      rfl

/-- The canonical tensor and unit comparisons for scheme-module pullback respect
both explicit tensor unitors. -/
theorem pullbackTensorUnitCoherence : PullbackTensorUnitCoherenceStatement.{u} :=
  ⟨pullbackTensorLeftUnitor, pullbackTensorRightUnitor⟩

end Langlands.Scheme.Modules
