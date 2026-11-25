/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteHeartRealization
import all WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteHeartRealization
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Constructibility for the specified finite-coefficient heart realization

## References

* Stacks Tags 03ET, 09AJ and 099Y
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem finiteScalarPointMap_isIso (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (finiteScalarPointMap.{u} A) := by
  let J := coherentTopology Profinite.{u}
  have h : J.W (A := RingCat.{u + 1}) (finiteConstants.{u} A) :=
    J.W_of_isLocallyBijective _
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map (finiteConstants.{u} A)) :=
    (J.W_iff _).mp h
  have heq : constantToContinuous.{u} A =
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
        (CommRingCat.of (ULift.{u + 1} A))).hom ≫
      (presheafToSheaf J RingCat.{u + 1}).map (finiteConstants.{u} A) ≫
        (sheafificationAdjunction J RingCat.{u + 1}).counit.app
          (Profinite.continuousMapRingSheaf.{u} A) := rfl
  have : IsIso (constantToContinuous.{u} A) := by rw [heq]; infer_instance
  unfold finiteScalarPointMap
  infer_instance

private def liftContinuousRingIso (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousCoefficientRingSheaf (ULift.{u} A) := by
  refine ObjectProperty.isoMk _ ?_
  refine NatIso.ofComponents (fun S ↦ ?_) ?_
  · exact
      { hom := RingCat.ofHom
          { toFun := fun f ↦ ULift.up
              ⟨fun x ↦ ULift.up (f.down x), continuous_uliftUp.comp f.down.continuous⟩
            map_one' := rfl
            map_mul' _ _ := rfl
            map_zero' := rfl
            map_add' _ _ := rfl }
        inv := RingCat.ofHom
          { toFun := fun f ↦ ULift.up
              ⟨fun x ↦ (f.down x).down, continuous_uliftDown.comp f.down.continuous⟩
            map_one' := rfl
            map_mul' _ _ := rfl
            map_zero' := rfl
            map_add' _ _ := rfl }
        hom_inv_id := by ext f; rfl
        inv_hom_id := by ext f; rfl }
  · intro S T f
    ext g
    rfl

private def liftedScalarPointMap (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    discreteObj.{u} A ⟶ FiniteDiscreteOrdinary.coefficient (ULift.{u} A) :=
  finiteScalarPointMap A ≫
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (liftContinuousRingIso A).hom

private instance liftedScalarPointMap_mon (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    IsMonHom (liftedScalarPointMap.{u} A) := by
  unfold liftedScalarPointMap
  have : IsMonHom ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (liftContinuousRingIso A).hom) :=
    Sheaf.isMonHom_sheafCompose_map _ (liftContinuousRingIso A).hom
  infer_instance

private instance liftedScalarPointMap_isIso (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (liftedScalarPointMap.{u} A) := by
  have := finiteScalarPointMap_isIso.{u} A
  unfold liftedScalarPointMap
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Constructibility is unchanged by the specified heart realization, on a single sheaf. -/
theorem finiteHeartConstructibility
    (X : Scheme.{u}) [IsNoetherian X] (A : Type) [Field A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj A) X)) :
    IsConstantModelConstructible (discreteObj A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X (ULift.{u, 0} A)
        ((finiteHeartRealization X A).obj M)  := by
  classical
  let B := ULift.{u} A
  let Λ := FiniteDiscreteOrdinary.coefficient B
  let φ := liftedScalarPointMap.{u} A
  let ψ := coefficientMap φ X
  let N := (Mod.comap (inv ψ)).obj M
  let e := (FiniteDiscreteOrdinary.encoding_exists B X).some
  let P := (e.ordinary.functor ⋙ e.fixed.functor).obj N
  let Q := (Scheme.proEtaleModuleRestriction X B).obj ((finiteHeartRealization X A).obj M)
  have ec : (Mod.comap ψ).obj N ≅ M :=
    ((Mod.comapComp ψ (inv ψ)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id ψ) ≪≫ Mod.comapId _).app M
  have hc : IsConstantModelConstructible (discreteObj A) X M ↔
      IsConstantModelConstructible Λ X N := by
    refine Iff.trans ?_ (constantModel_comap_iff φ X N)
    exact ⟨constructible_iso ec.symm, constructible_iso ec⟩
  have hp : IsConstantModelConstructible Λ X N ↔
      IsConstructible (ULift.{u + 1} B) P := by
    have h := FiniteDiscreteOrdinary.constructible_comparison B X e N
    rw [FiniteDiscreteOrdinary.ordinaryConstructible,
      ite_eq_left ⟨inferInstance, inferInstance⟩] at h
    refine h.trans ?_
    apply exists_congr
    intro S
    refine forall_congr' fun i ↦ ?_
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨ULift.{u + 1} C.I₀, (fun j ↦ C.X j.down),
        (fun j ↦ C.f j.down), ?_, fun j ↦ (hC j.down).imp fun _ hP ↦
          ⟨by have := hP.1; exact Module.Finite.of_finite, hP.2⟩⟩
      change Presieve.ofArrows (C.X ∘ ULift.down)
        (fun j : ULift.{u + 1} C.I₀ ↦ C.f j.down) ∈ _
      rw [Presieve.ofArrows_comp_eq_of_surjective C.f
        (show Function.Surjective (ULift.down : ULift.{u + 1} C.I₀ → C.I₀) from
          fun j ↦ ⟨ULift.up j, rfl⟩)]
      exact C.mem₀
    · rintro ⟨I, U, f, hf, h⟩
      let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain i) :=
        ⟨{ I₀ := I, X := U, f := f }, hf⟩
      let : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
        inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
      exact ⟨C.restrictIndexOfSmall.{u}, fun j ↦
        (h (Precoverage.ZeroHypercover.Small.restrictFun C j)).imp fun _ hM ↦
          ⟨by have := hM.1; exact Module.finite_of_finite (ULift.{u + 1} B), hM.2⟩⟩
  let U₁ := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1})
  have ep : U₁.obj P ≅ M.X := by
    dsimp only [P]
    rw [e.ordinary_functor, e.fixed_functor]
    exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  have := finiteScalarMap_isIso X A
  let R := (Mod.extendScalars (finiteScalarMap X A)).obj M
  let H := (CondensedRing.continuousRingModuleEquivalence X A).functor ⋙
    integralModelFixedScalars X A
  obtain ⟨ei⟩ := intrinsicRealization_restriction X B
  have eq : U₁.obj Q ≅ M.X :=
    U₁.mapIso (ei.app (H.obj R)) ≪≫
      (integralModel_fixed_forget X A).app R ≪≫
      (Mod.forget _).mapIso ((Mod.extendScalarsIsoComapInv (finiteScalarMap X A)).app M)
  let U₂ := sheafCompose (Scheme.ProEt.topology X) (CategoryTheory.forget Ab.{u + 1})
  have es : (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1}
      (ULift.{u + 1} B)))).obj P ≅
      (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1}
        (ULift.{u + 1} B)))).obj Q := U₂.mapIso (ep ≪≫ eq.symm)
  have ht : IsConstructible (ULift.{u + 1} B) P ↔
      IsConstructible (ULift.{u + 1} B) Q :=
    ⟨integralModel_fixed_constructible_transfer _ _ X P Q es,
      integralModel_fixed_constructible_transfer _ _ X Q P es.symm⟩
  exact hc.trans (hp.trans (ht.trans
    (Scheme.proEtaleModuleRestriction_constructible_iff X B _).symm))

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
