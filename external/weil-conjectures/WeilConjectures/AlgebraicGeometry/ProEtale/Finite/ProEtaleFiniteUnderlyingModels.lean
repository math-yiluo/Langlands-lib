/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Finite underlying local models from finite geometric stalks

## References

* Stacks Project, Modules on Sites, Definition 093Q
* Tag 099Y
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A locally constant module sheaf with finite geometric stalks has objectwise
finite constant underlying set models. -/
theorem proEtale_finiteUnderlyingModels_of_locallyConstant
    (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (hF : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} X A F)
    (hs : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing X A) F)) :
    ∀ U : X.ProEt, ∃ S : Presieve U, S ∈ ProEt.precoverage X U ∧
      ∀ (V : X.ProEt) (g : V ⟶ U), S g →
        ∃ Z : Type (u + 1), Finite Z ∧ Nonempty
          ((((sheafCompose (ProEt.topology X)
            (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
            (constantSheaf ((ProEt.topology X).over V) (Type (u + 1))).obj Z) := by
  classical
  have hl : IsLocallyConstantProEtaleModuleSheaf X A F := by
    obtain ⟨I, V, g, hg, he⟩ := hF
    exact ⟨I, V, g, hg, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
  let R := ULift.{u + 1, u} A
  let J := ProEt.topology X
  let F' := (proEtaleModuleRestriction X A).obj F
  obtain ⟨I, V, g, hg, he⟩ := ProEtale.finiteModels_over R F' (by
    obtain ⟨ι, W, g, hg, h⟩ := (finiteLocal_iff X A F).mpr ⟨hl, hs⟩
    refine ⟨ι, W, g, hg, fun i ↦ ?_⟩
    obtain ⟨M, hM, e⟩ := h i
    exact ⟨M, Module.finite_of_finite R, e⟩)
  intro U
  let a : U ⟶ ProEt.mk (𝟙 X) :=
    MorphismProperty.Over.homMk U.hom (Category.comp_id _)
  let W (i : I) := pullback a (g i)
  let p (i : I) : W i ⟶ U := pullback.fst _ _
  let t (i : I) : W i ⟶ V i := pullback.snd _ _
  refine ⟨Presieve.ofArrows W p,
    Precoverage.mem_coverings_of_isPullback g hg a p t
      (fun i ↦ IsPullback.of_hasPullback _ _), ?_⟩
  rintro _ _ ⟨i⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := he i
  let C := (constantSheaf J (ModuleCat.{u + 1} R)).obj M
  let E := (Over.map (t i)).sheafPushforwardContinuous
    (ModuleCat.{u + 1} R) (J.over (W i)) (J.over (V i))
  let e' : F'.over (W i) ≅
      (constantSheaf (J.over (W i)) (ModuleCat.{u + 1} R)).obj M :=
    (F'.pushforwardOverMapIso (t i)).symm ≪≫
    E.mapIso (e ≪≫ constantSheafOverIso J (ModuleCat.{u + 1} R) (V i) M) ≪≫
    C.pushforwardOverMapIso (t i) ≪≫
    (constantSheafOverIso J (ModuleCat.{u + 1} R) (W i) M).symm
  refine ⟨M, hM, ⟨?_⟩⟩
  exact (sheafCompose (J.over (W i))
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).mapIso e' ≪≫
      (constantCommuteCompose (J.over (W i))
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).app M

end AlgebraicGeometry.Scheme
