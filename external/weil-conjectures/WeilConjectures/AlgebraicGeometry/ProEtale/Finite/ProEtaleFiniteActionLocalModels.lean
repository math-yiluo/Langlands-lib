/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.Finite.FiniteRingActionLocalConstancy
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Finite operation tables give localized pro-étale module models

## References

* Stacks Project, Modules on Sites, Tag 093S
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem proEtale_siteForCoverings (X : Scheme.{u}) :
    (ProEt.precoverage X).IsSiteForCoverings := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro U R T hR hT
    exact (ProEt.precoverage X).toPretopology.transitive R
      (fun _ g hg ↦ T g hg) hR (fun V g hg ↦ hT V g hg)
  · intro I U V g hg W a
    exact ⟨fun i ↦ pullback a (g i), fun i ↦ pullback.fst _ _,
      fun i ↦ pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _,
      Precoverage.mem_coverings_of_isPullback g hg a _ _
        (fun i ↦ IsPullback.of_hasPullback _ _)⟩

attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
private theorem constantModule_over_comparison (X : Scheme.{u})
    (B : Type u) [CommRing B] (V : X.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} B)) :
    Nonempty (((commutativeSiteConstantModuleFunctor (ProEt.topology X)
      (ULift.{u + 1, u} B)).obj M).over V ≅
        proEtaleConstantModuleSheafOverOfUniverses X B V M) := by
  let A := ULift.{u + 1, u} B
  let J := ProEt.topology X
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X B)
  let a := proEtaleModuleScalarUnit X B
  let aV := Functor.whiskerLeft (Over.forget V).op a
  have : Presheaf.IsLocallyInjective J a :=
    (proEtaleConstantRingUnit_locallyBijective X B).1
  have : Presheaf.IsLocallySurjective J a :=
    (proEtaleConstantRingUnit_locallyBijective X B).2
  have : Presheaf.IsLocallyInjective (J.over V) aV :=
    (proEtaleConstantRingUnit_over_locallyBijective X B V).1
  have : Presheaf.IsLocallySurjective (J.over V) aV :=
    (proEtaleConstantRingUnit_over_locallyBijective X B V).2
  let E := ConstantScalarComparison.restriction.{u} (J.over V) A (R.over V) aV
  have hglobal := ConstantScalarComparison.constantComparisonHom_isIso.{u} J A R a M
  have hlocal := ConstantScalarComparison.constantComparisonHom_isIso.{u}
    (J.over V) A (R.over V) aV M
  let e : E.obj (((commutativeSiteConstantModuleFunctor J A).obj M).over V) ≅
      E.obj (proEtaleConstantModuleSheafOverOfUniverses X B V M) :=
    (J.overPullback (ModuleCat.{u + 1} A) V).mapIso
      (asIso (ConstantScalarComparison.constantComparisonHom.{u} J A R a M)).symm ≪≫
    (constantSheafOverIso J (ModuleCat.{u + 1} A) V M).symm ≪≫
    asIso (ConstantScalarComparison.constantComparisonHom.{u} (J.over V) A (R.over V) aV M)
  exact ⟨(ConstantScalarComparison.restrictionFullyFaithful.{u}
    (J.over V) A (R.over V) aV).preimageIso e⟩

/-- A finite constant coefficient action on a sheaf with finite locally constant
underlying sets admits finite module models on localized ringed sites. -/
theorem proEtale_finiteLocalModels_of_finiteUnderlying
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (F : proEtaleRingModules X (proEtaleConstantRing X B))
    (hF : ∀ U : X.ProEt, ∃ S : Presieve U, S ∈ ProEt.precoverage X U ∧
      ∀ (V : X.ProEt) (g : V ⟶ U), S g →
        ∃ Z : Type (u + 1), Finite Z ∧ Nonempty
          ((((sheafCompose (ProEt.topology X)
            (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
            (constantSheaf ((ProEt.topology X).over V) (Type (u + 1))).obj Z)) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses.{u, u}
      X B (fun M ↦ Finite M) F := by
  obtain ⟨S, hS, hs⟩ := SheafOfModules.finite_ring_action_local_constancy
    (ProEt.precoverage X) (proEtale_siteForCoverings X) (ULift.{u + 1, u} B)
    F hF (ProEt.mk (𝟙 X))
  obtain ⟨I, V, g, rfl⟩ := S.exists_eq_ofArrows
  refine ⟨I, V, g, hS, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hs (V i) (g i) ⟨i⟩
  exact ⟨M, hM, ⟨e ≪≫ (constantModule_over_comparison X B (V i) M).some⟩⟩

end AlgebraicGeometry.Scheme
