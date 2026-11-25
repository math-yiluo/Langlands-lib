/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionPureTensorUnit
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorAssociativity

/-! # Tensor coherence of specified action-site comparisons

Source: the normalized tensor and evaluation formulas of the twisted action-site
presentation; Stacks 03EK, 03EL and 03EO. No native or derived category occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.TwistedActionRingedSite

section PureSections

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}}

private theorem module_naturality_apply
    {A : Type (u + 1)} [Category.{u} A] {G H : A ⥤ Modules S} (e : G ⟶ H)
    {M N : A} (f : M ⟶ N) (X : Dᵒᵖ) (x : (G.obj M).val.obj X) :
    (e.app N).val.app X ((G.map f).val.app X x) =
      (H.map f).val.app X ((e.app M).val.app X x) :=
  congrArg (fun g ↦ g.val.app X x) (e.naturality f)

attribute [local irreducible] SheafOfModules.monoidalCategory

end PureSections

attribute [local irreducible] sigma pureTensor evaluationMap
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric

private theorem forgetPairs_obj {A : Type (u + 1)} [Category.{u} A]
    (T : A ⥤ A) (M : Pairs T) :
    (forgetPairs T).obj M = M.obj.a := rfl

private theorem forgetPairs_map {A : Type (u + 1)} [Category.{u} A]
    (T : A ⥤ A) {M N : Pairs T} (f : M ⟶ N) :
    (forgetPairs T).map f = f.hom.f := rfl

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

private noncomputable def tensorComparison (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory P.coefficient) ⋙ U ≅
      (U.prod U) ⋙ @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) := by
  letI := P.category
  exact NatIso.ofComponents (fun M ↦ P.tensor M.1 M.2)
    (fun f ↦ P.tensor_naturality f.1 f.2)

omit [s.functor.IsContinuous J J] in
private theorem tensorComparison_hom_app (P : Presentation J s R a) :
    letI := P.category
    ∀ M N : Modules P.coefficient,
      (tensorComparison P).hom.app (M, N) = (P.tensor M N).hom := by
  exact fun M N ↦ rfl

attribute [local irreducible] tensorComparison

omit [s.functor.IsContinuous J J] in
private theorem restriction_map (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ {M N : Modules P.coefficient} (f : M ⟶ N) (X : Cᵒᵖ)
      (x : (U.obj M).val.obj X),
      (P.restriction.hom.app N).val.app X ((U.map f).val.app X x) =
      f.val.app (P.inclusion.op.obj X) ((P.restriction.hom.app M).val.app X x) := by
  let := P.category
  dsimp only
  intro M N f X x
  exact module_naturality_apply P.restriction.hom f X x

omit [s.functor.IsContinuous J J] in
private theorem restriction_smul (P : Presentation J s R a) :
    letI := P.category
    ∀ (M : Modules P.coefficient) (X : Cᵒᵖ)
      (r : P.coefficient.obj.obj (P.inclusion.op.obj X))
      (x : (P.modules.functor.obj M).obj.a.val.obj X),
      (P.restriction.hom.app M).val.app X
          ((P.coefficientRestriction.hom.hom.app X) r • x) =
        r • (show M.val.obj (P.inclusion.op.obj X) from
          (P.restriction.hom.app M).val.app X x) := by
  let := P.category
  dsimp only
  intro M X r x
  have h := ((P.restriction.hom.app M).val.app X).hom.map_smul
    ((P.coefficientRestriction.hom.hom.app X) r) x
  change _ = (P.coefficientRestriction.inv.hom.app X
    (P.coefficientRestriction.hom.hom.app X r)) •
      (show M.val.obj (P.inclusion.op.obj X) from
        (P.restriction.hom.app M).val.app X x) at h
  have hi := congrArg (fun f ↦ f.hom.app X r) P.coefficientRestriction.hom_inv_id
  change P.coefficientRestriction.inv.hom.app X
    (P.coefficientRestriction.hom.hom.app X r) = r at hi
  rw [hi] at h
  exact h

omit [s.functor.IsContinuous J J] in
private theorem comparison_left_unit (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ M : Modules P.coefficient,
      (P.tensor (𝟙_ _) M).hom ≫ tensorMap P.unit.hom (𝟙 _) ≫ (λ_ (U.obj M)).hom =
        U.map (λ_ M).hom := by
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  dsimp only
  intro M
  apply (cancel_epi (P.tensor (𝟙_ _) M).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (P.restriction.hom.app M)).mp
  apply TensorRestriction.pure_ext
  intro X r x
  change (P.restriction.hom.app M).val.app X
      ((λ_ (U.obj M)).hom.val.app X
        ((tensorMap P.unit.hom (𝟙 (U.obj M))).val.app X (pureTensor _ _ X r x))) =
    (P.restriction.hom.app M).val.app X
      ((U.map (λ_ M).hom).val.app X
        ((P.tensor (𝟙_ _) M).inv.val.app X (pureTensor _ _ X r x)))
  erw [TensorRestriction.pure_map P.unit.hom (𝟙 (U.obj M)), pure_left_unitor (U.obj M),
    restriction_map P (λ_ M).hom, P.tensor_pure (𝟙_ _) M, pure_left_unitor M,
    P.unit_sections X]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  exact restriction_smul P M X _ x

omit [s.functor.IsContinuous J J] in
private theorem comparison_right_unit (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ M : Modules P.coefficient,
      (P.tensor M (𝟙_ _)).hom ≫ tensorMap (𝟙 _) P.unit.hom ≫ (ρ_ (U.obj M)).hom =
        U.map (ρ_ M).hom := by
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  dsimp only
  intro M
  rw [← braiding_leftUnitor, ← braiding_leftUnitor, Functor.map_comp]
  dsimp only [tensorMap]
  erw [BraidedCategory.braiding_naturality_assoc, ← Category.assoc,
    ← P.symmetry M (𝟙_ _), Category.assoc, comparison_left_unit P M]
  simp only [Functor.comp_map, forgetPairs_map]

omit [s.functor.IsContinuous J J] in
/-- The specified tensor comparisons are natural and coherent.

Source: Stacks 03EK, 03EL and 03EO; the tensor portion of the specified action-site
presentation (blueprint: lem-sf-twisted-action-tensor-coherence).

Proof: assemble the given components with tensor naturality. Cancel inverse comparison
maps in associativity and use the sheafification adjunction to reduce equality to pure
triples. The restriction isomorphism then identifies both sides with the source
associator on pure triples. Left-unit coherence similarly reduces to multiplication
of a section by a coefficient, using semilinearity of restriction and the specified
unit normalization. Right-unit coherence follows from left-unit coherence and braiding.
The symmetry equation is the specified presentation symmetry. -/
theorem tensor_coherence (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∃ τ : @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory P.coefficient) ⋙ U ≅
        (U.prod U) ⋙ @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R),
      Nonempty (RingedForgetTensorTransposition.TensorCoherence
        (SheafOfModules.monoidalCategory P.coefficient) (SheafOfModules.monoidalCategory R)
        (SheafOfModules.symmetricCategory P.coefficient) (SheafOfModules.symmetricCategory R)
        U τ) ∧ ∀ M N : Modules P.coefficient,
          τ.hom.app (M, N) = (P.tensor M N).hom := by
  let := P.category
  refine ⟨tensorComparison P, ⟨?_⟩, tensorComparison_hom_app P⟩
  refine { unit := P.unit
           associativity := ?_
           left_unit := ?_
           right_unit := ?_
           symmetry := ?_ }
  · intro M N T
    simpa only [tensorComparison_hom_app, MonoidalCategory.tensor_obj,
      MonoidalCategory.tensor_map, tensorMap,
      Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      forgetPairs_map, forgetPairs_obj, tensorObj] using tensor_associativity P M N T
  · intro M
    simpa only [tensorComparison_hom_app, MonoidalCategory.tensor_obj,
      MonoidalCategory.tensor_map, tensorMap,
      Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      forgetPairs_map, forgetPairs_obj, tensorObj] using comparison_left_unit P M
  · intro M
    simpa only [tensorComparison_hom_app, MonoidalCategory.tensor_obj,
      MonoidalCategory.tensor_map, tensorMap,
      Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      forgetPairs_map, forgetPairs_obj, tensorObj] using comparison_right_unit P M
  · intro M N
    simpa only [tensorComparison_hom_app, MonoidalCategory.tensor_obj,
      MonoidalCategory.tensor_map, tensorMap,
      Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
      forgetPairs_map, forgetPairs_obj, tensorObj] using P.symmetry M N

end CategoryTheory.TwistedActionRingedSite
