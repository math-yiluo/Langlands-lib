import Langlands.Representation.Hecke.CentralIdempotentIdeal
import Langlands.Algebra.NonUnitalModuleRestrictScalars

/-! # Modules over a central Hecke ideal -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))
  (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
  (hz : IsIdempotentElem z)

/-- The smooth objects on which the selected central operator acts identically. -/
def centralFixedProperty : ObjectProperty (SmoothRep.{0,u,max u v} ℂ G) :=
  fun V => z.app V = 𝟙 V

include hz in
/-- Restriction of the integrated action is nondegenerate on a central fixed object. -/
theorem centralIdeal_restriction_nondegenerate
    (V : (centralFixedProperty z).FullSubcategory) :
    @Algebra.IsNondegenerate (centralIdeal μ hl z) V.obj _ _
      (Algebra.NonUnitalModuleRestrictScalars.module
        (NonUnitalSubringClass.subtype (centralIdeal μ hl z))
        (heckeNonUnitalModule μ V.obj.representation V.obj.isSmooth)) := by
  intro x
  obtain ⟨a, ha⟩ := heckeNonUnitalModule_isNondegenerate μ V.obj.representation V.obj.isSmooth x
  let p := centralIdealProjection μ hl z hz
  have hp : IsIdempotentElem (p (a : HeckeAlgebra μ)) := by
    change p (a : HeckeAlgebra μ) * p (a : HeckeAlgebra μ) = p (a : HeckeAlgebra μ)
    rw [← map_mul, a.property.eq]
  refine ⟨⟨p (a : HeckeAlgebra μ), hp⟩, ?_⟩
  change heckeAction μ V.obj.representation V.obj.isSmooth
    (centralMultiplier μ hl z (a : HeckeAlgebra μ)) x = x
  change heckeAction μ V.obj.representation V.obj.isSmooth (a : HeckeAlgebra μ) x = x at ha
  rw [centralMultiplier_action, ha, V.property]
  rfl

/-- The actual restriction functor from fixed smooth objects to nondegenerate ideal modules. -/
def centralIdealModuleFunctor :
    (centralFixedProperty z).FullSubcategory ⥤
      Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z) where
  obj V :=
    ⟨(Algebra.NonUnitalModuleRestrictScalars.functor
        (NonUnitalSubringClass.subtype (centralIdeal μ hl z))).obj
          (heckeNondegenerateModule μ V.obj).obj,
      centralIdeal_restriction_nondegenerate μ hl z hz V⟩
  map {V W} f := ObjectProperty.homMk
    { toAddMonoidHom := (SmoothRep.hom f.hom).toLinearMap.toAddMonoidHom
      map_smul' := fun a x =>
        integratedAction_intertwiner μ V.obj.isSmooth W.obj.isSmooth
          (SmoothRep.hom f.hom) (HeckeAlgebra.toTestFunction μ (a : HeckeAlgebra μ)) x }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Expose the original ideal-linear map through the two full-subcategory wrappers. -/
abbrev centralIdealModuleUnderlying
    {V W : (centralFixedProperty z).FullSubcategory}
    (f : (centralIdealModuleFunctor μ hl z hz).obj V ⟶
      (centralIdealModuleFunctor μ hl z hz).obj W) :
    @Algebra.NonUnitalModuleHom (centralIdeal μ hl z) V.obj W.obj _ _ _
      (Algebra.NonUnitalModuleRestrictScalars.module
        (NonUnitalSubringClass.subtype (centralIdeal μ hl z))
        (heckeNonUnitalModule μ V.obj.representation V.obj.isSmooth))
      (Algebra.NonUnitalModuleRestrictScalars.module
        (NonUnitalSubringClass.subtype (centralIdeal μ hl z))
        (heckeNonUnitalModule μ W.obj.representation W.obj.isSmooth)) := f.hom

/-- An ideal-linear map between fixed objects already respects the full Hecke action. -/
def centralIdealModuleFullMap
    {V W : (centralFixedProperty z).FullSubcategory}
    (f : (centralIdealModuleFunctor μ hl z hz).obj V ⟶
      (centralIdealModuleFunctor μ hl z hz).obj W) :
    heckeNondegenerateModule μ V.obj ⟶ heckeNondegenerateModule μ W.obj := by
  letI := Algebra.NonUnitalModuleRestrictScalars.module
    (NonUnitalSubringClass.subtype (centralIdeal μ hl z))
    (heckeNonUnitalModule μ V.obj.representation V.obj.isSmooth)
  letI := Algebra.NonUnitalModuleRestrictScalars.module
    (NonUnitalSubringClass.subtype (centralIdeal μ hl z))
    (heckeNonUnitalModule μ W.obj.representation W.obj.isSmooth)
  let ff := centralIdealModuleUnderlying μ hl z hz f
  exact ObjectProperty.homMk
    { toAddMonoidHom := ff.toAddMonoidHom
      map_smul' := by
        intro a x
        change ff (heckeAction μ V.obj.representation V.obj.isSmooth a x) =
          heckeAction μ W.obj.representation W.obj.isSmooth a (ff x)
        have hV := (central_app_eq_id_iff μ hl z V.obj).mp V.property a x
        have hW := (central_app_eq_id_iff μ hl z W.obj).mp W.property a (ff x)
        calc
          ff (heckeAction μ V.obj.representation V.obj.isSmooth a x) =
              ff (heckeAction μ V.obj.representation V.obj.isSmooth
                (centralMultiplier μ hl z a) x) := congrArg ff hV.symm
          _ = heckeAction μ W.obj.representation W.obj.isSmooth
              (centralMultiplier μ hl z a) (ff x) :=
            ff.map_smul (centralIdealProjection μ hl z hz a) x
          _ = heckeAction μ W.obj.representation W.obj.isSmooth a (ff x) := hW }

/-- Fullness of ideal restriction, through the proved III.1.4 full Hecke functor. -/
theorem centralIdealModuleFunctor_full : (centralIdealModuleFunctor μ hl z hz).Full where
  map_surjective f :=
    ⟨ObjectProperty.homMk
      (NondegenerateEquivalence.preimage μ (centralIdealModuleFullMap μ hl z hz f)), by
        apply ObjectProperty.hom_ext
        apply Algebra.NonUnitalModuleHom.ext
        intro x
        rfl⟩

/-- Faithfulness follows from retaining the whole underlying additive map. -/
theorem centralIdealModuleFunctor_faithful :
    (centralIdealModuleFunctor μ hl z hz).Faithful where
  map_injective := by
    intro V W f g h
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    ext x
    exact congrArg (fun k => centralIdealModuleUnderlying μ hl z hz k x) h

/-- Extend an ideal module to the whole Hecke algebra through the central ring projection. -/
def centralIdealExtend
    (M : Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z)) :
    Algebra.NondegenerateModuleCat.{u,max u v} (HeckeAlgebra μ) :=
  ⟨(Algebra.NonUnitalModuleRestrictScalars.functor
      (centralIdealProjection μ hl z hz)).obj M.obj, by
    intro x
    obtain ⟨a, ha⟩ := M.property x
    have hi : IsIdempotentElem ((a : centralIdeal μ hl z) : HeckeAlgebra μ) := by
      exact congrArg (fun b : centralIdeal μ hl z => (b : HeckeAlgebra μ)) a.property.eq
    refine ⟨⟨((a : centralIdeal μ hl z) : HeckeAlgebra μ), hi⟩, ?_⟩
    change Algebra.NonUnitalModule.toEndHom M.obj.isModule
      (centralIdealProjection μ hl z hz (a : centralIdeal μ hl z)) x = x
    rw [centralIdealProjection_subtype]
    exact ha⟩

/-- Recover a smooth representation from the extended module by III.1.4. -/
def centralIdealRecovered
    (M : Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z)) :
    SmoothRep.{0,u,max u v} ℂ G :=
  NondegenerateEquivalence.recoveredObject μ (centralIdealExtend μ hl z hz M)

/-- The recovered representation is fixed by the selected central operator. -/
theorem centralIdealRecovered_fixed
    (M : Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z)) :
    centralFixedProperty z (centralIdealRecovered μ hl z hz M) := by
  let := NondegenerateEquivalence.scalars μ (centralIdealExtend μ hl z hz M).property
  apply (central_app_eq_id_iff μ hl z (centralIdealRecovered μ hl z hz M)).mpr
  intro a x
  change heckeAction μ
      (NondegenerateEquivalence.recovered μ (centralIdealExtend μ hl z hz M).property)
      (NondegenerateEquivalence.recovered_smooth μ (centralIdealExtend μ hl z hz M).property)
      (centralMultiplier μ hl z a) x =
    heckeAction μ
      (NondegenerateEquivalence.recovered μ (centralIdealExtend μ hl z hz M).property)
      (NondegenerateEquivalence.recovered_smooth μ (centralIdealExtend μ hl z hz M).property) a x
  rw [NondegenerateEquivalence.integrated_recovered,
    NondegenerateEquivalence.integrated_recovered]
  change Algebra.NonUnitalModule.toEndHom M.obj.isModule (centralIdealProjection μ hl z hz
      ((centralIdealProjection μ hl z hz a) : HeckeAlgebra μ)) x =
    Algebra.NonUnitalModule.toEndHom M.obj.isModule (centralIdealProjection μ hl z hz a) x
  rw [centralIdealProjection_subtype]

/-- The fixed smooth object recovered from an arbitrary nondegenerate ideal module. -/
def centralIdealRecoveredFixed
    (M : Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z)) :
    (centralFixedProperty z).FullSubcategory :=
  ⟨centralIdealRecovered μ hl z hz M, centralIdealRecovered_fixed μ hl z hz M⟩

/-- Restricting the recovered action gives exactly the original ideal module. -/
def centralIdealRecoveredIso
    (M : Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z)) :
    (centralIdealModuleFunctor μ hl z hz).obj (centralIdealRecoveredFixed μ hl z hz M) ≅ M where
  hom := ObjectProperty.homMk
    { toAddMonoidHom := AddMonoidHom.id M.obj
      map_smul' := by
        intro a x
        let := NondegenerateEquivalence.scalars μ (centralIdealExtend μ hl z hz M).property
        change heckeAction μ
            (NondegenerateEquivalence.recovered μ (centralIdealExtend μ hl z hz M).property)
            (NondegenerateEquivalence.recovered_smooth μ
              (centralIdealExtend μ hl z hz M).property) (a : HeckeAlgebra μ) x =
          Algebra.NonUnitalModule.toEndHom M.obj.isModule a x
        rw [NondegenerateEquivalence.integrated_recovered]
        change Algebra.NonUnitalModule.toEndHom M.obj.isModule
          (centralIdealProjection μ hl z hz (a : HeckeAlgebra μ)) x =
            Algebra.NonUnitalModule.toEndHom M.obj.isModule a x
        rw [centralIdealProjection_subtype] }
  inv := ObjectProperty.homMk
    { toAddMonoidHom := AddMonoidHom.id M.obj
      map_smul' := by
        intro a x
        let := NondegenerateEquivalence.scalars μ (centralIdealExtend μ hl z hz M).property
        change Algebra.NonUnitalModule.toEndHom M.obj.isModule a x = heckeAction μ
            (NondegenerateEquivalence.recovered μ (centralIdealExtend μ hl z hz M).property)
            (NondegenerateEquivalence.recovered_smooth μ
              (centralIdealExtend μ hl z hz M).property) (a : HeckeAlgebra μ) x
        rw [NondegenerateEquivalence.integrated_recovered]
        change Algebra.NonUnitalModule.toEndHom M.obj.isModule a x =
          Algebra.NonUnitalModule.toEndHom M.obj.isModule
            (centralIdealProjection μ hl z hz (a : HeckeAlgebra μ)) x
        rw [centralIdealProjection_subtype] }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Algebra.NonUnitalModuleHom.ext
    intro x
    rfl
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Algebra.NonUnitalModuleHom.ext
    intro x
    rfl

/-- Every nondegenerate ideal module is in the essential image of the actual restriction. -/
theorem centralIdealModuleFunctor_essSurj :
    (centralIdealModuleFunctor μ hl z hz).EssSurj where
  mem_essImage M :=
    ⟨centralIdealRecoveredFixed μ hl z hz M, ⟨centralIdealRecoveredIso μ hl z hz M⟩⟩

/-- Fixed smooth representations are equivalent to nondegenerate central-ideal modules. -/
def centralIdealModuleEquivalence :
    (centralFixedProperty z).FullSubcategory ≌
      Algebra.NondegenerateModuleCat.{u,max u v} (centralIdeal μ hl z) := by
  letI : (centralIdealModuleFunctor μ hl z hz).IsEquivalence :=
    { faithful := centralIdealModuleFunctor_faithful μ hl z hz
      full := centralIdealModuleFunctor_full μ hl z hz
      essSurj := centralIdealModuleFunctor_essSurj μ hl z hz }
  exact (centralIdealModuleFunctor μ hl z hz).asEquivalence

/-- The forward equivalence is the actual Hecke action restricted to the central ideal. -/
def centralIdealModuleEquivalence_comparison :
    (centralIdealModuleEquivalence μ hl z hz).functor ⋙
        Algebra.nondegenerateInclusion (centralIdeal μ hl z) ≅
      (centralFixedProperty z).ι ⋙ heckeNondegenerateModuleFunctor μ ⋙
        Algebra.nondegenerateInclusion (HeckeAlgebra μ) ⋙
          Algebra.NonUnitalModuleRestrictScalars.functor
            (NonUnitalSubringClass.subtype (centralIdeal μ hl z)) :=
  Iso.refl _

end Langlands.Hecke
