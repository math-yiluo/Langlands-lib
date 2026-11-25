/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionPureTripleExt
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Associativity of the specified tensor comparison

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

private theorem pure_associator (M N T : Modules S) (X : Dᵒᵖ)
    (x : M.val.obj X) (y : N.val.obj X) (z : T.val.obj X) :
    (α_ M N T).hom.val.app X
        (pureTensor (M ⊗ N) T X (pureTensor M N X x y) z) =
      pureTensor M (N ⊗ T) X x (pureTensor N T X y z) :=
  CochainPullback.moduleTmul_associator M N T X x y z

end PureSections

attribute [local irreducible] sigma pureTensor evaluationMap
attribute [local implicit_reducible] forgetPairs Endofunctor.Algebra.forget
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {s : C ≌ C} [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    {R : Sheaf J CommRingCat.{u}}
    {a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R}

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
private theorem restriction_tensor_map_pure (P : Presentation J s R a) :
    letI := P.category
    ∀ (M N : Modules P.coefficient) (K L : Modules R)
      (f : K ⟶ (P.modules.functor.obj M).obj.a)
      (g : L ⟶ (P.modules.functor.obj N).obj.a) (X : Cᵒᵖ)
      (x : K.val.obj X) (y : L.val.obj X),
      (P.restriction.hom.app (M ⊗ N)).val.app X
          ((P.tensor M N).inv.val.app X
            ((tensorMap f g).val.app X (pureTensor K L X x y))) =
        pureTensor M N (P.inclusion.op.obj X)
          ((P.restriction.hom.app M).val.app X (f.val.app X x))
          ((P.restriction.hom.app N).val.app X (g.val.app X y)) := by
  let := P.category
  intro M N K L f g X x y
  exact (congrArg (fun t ↦ (P.restriction.hom.app (M ⊗ N)).val.app X
    ((P.tensor M N).inv.val.app X t)) (TensorRestriction.pure_map f g X x y)).trans
      (P.tensor_pure M N X (f.val.app X x) (g.val.app X y))

omit [s.functor.IsContinuous J J] in
/-- The specified tensor comparisons preserve associativity.

Source: Stacks 03EK, 03EL; the pure-tensor formula for specified restriction
(blueprint: lem-sf-twisted-action-tensor-associativity).

Proof: cancel the two inverse tensor comparisons before and after the associativity
square. Postcompose with the restriction isomorphism and test on local pure triples,
using the proved sheafification triple-tensor extensionality criterion. Naturality
of restriction and the specified pure-tensor formula identify both paths with the
source associator applied to the corresponding restricted pure triple. The ordinary
pure-triple associator formula then gives equality. -/
theorem tensor_associativity (P : Presentation J s R a) :
    letI := P.category
    let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
    ∀ M N T : Modules P.coefficient,
      U.map (α_ M N T).hom ≫ (P.tensor M (N ⊗ T)).hom ≫
          tensorMap (𝟙 _) (P.tensor N T).hom =
        (P.tensor (M ⊗ N) T).hom ≫ tensorMap (P.tensor M N).hom (𝟙 _) ≫
          (α_ (U.obj M) (U.obj N) (U.obj T)).hom := by
  let := P.category
  let U := P.modules.functor ⋙ forgetPairs (sigma J s R a)
  dsimp only
  intro M N T
  let q := tensorMap (P.tensor M N).inv (𝟙 (U.obj T)) ≫ (P.tensor (M ⊗ N) T).inv
  let t := tensorMap (𝟙 (U.obj M)) (P.tensor N T).inv ≫ (P.tensor M (N ⊗ T)).inv
  apply (cancel_epi q).mp
  apply (cancel_mono t).mp
  dsimp only [q, t, tensorMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Iso.inv_hom_id,
    Category.id_comp]
  erw [id_tensorHom_id, id_tensorHom_id]
  simp only [Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_mono (P.restriction.hom.app (M ⊗ (N ⊗ T)))).mp
  apply pure_triple_ext (U.obj M) (U.obj N) (U.obj T)
  intro X x y z
  change (P.restriction.hom.app (M ⊗ (N ⊗ T))).val.app X
      ((U.map (α_ M N T).hom).val.app X
        ((P.tensor (M ⊗ N) T).inv.val.app X
          ((tensorMap (P.tensor M N).inv (𝟙 (U.obj T))).val.app X
            (pureTensor _ _ X (pureTensor _ _ X x y) z)))) =
    (P.restriction.hom.app (M ⊗ (N ⊗ T))).val.app X
      ((P.tensor M (N ⊗ T)).inv.val.app X
        ((tensorMap (𝟙 (U.obj M)) (P.tensor N T).inv).val.app X
          ((α_ (U.obj M) (U.obj N) (U.obj T)).hom.val.app X
            (pureTensor _ _ X (pureTensor _ _ X x y) z))))
  let Y := P.inclusion.op.obj X
  let x' := (P.restriction.hom.app M).val.app X x
  let y' := (P.restriction.hom.app N).val.app X y
  let z' := (P.restriction.hom.app T).val.app X z
  have hL := restriction_tensor_map_pure P (M ⊗ N) T
    (U.obj M ⊗ U.obj N) (U.obj T) (P.tensor M N).inv (𝟙 (U.obj T)) X
    (pureTensor (U.obj M) (U.obj N) X x y) z
  have hL' := hL.trans (congrArg
    (fun w ↦ pureTensor (M ⊗ N) T Y w z') (P.tensor_pure M N X x y))
  have hR₁ := congrArg (fun w ↦
    (P.restriction.hom.app (M ⊗ (N ⊗ T))).val.app X
      ((P.tensor M (N ⊗ T)).inv.val.app X
        ((tensorMap (𝟙 (U.obj M)) (P.tensor N T).inv).val.app X w)))
    (pure_associator (U.obj M) (U.obj N) (U.obj T) X x y z)
  have hR₂ := restriction_tensor_map_pure P M (N ⊗ T)
    (U.obj M) (U.obj N ⊗ U.obj T) (𝟙 (U.obj M)) (P.tensor N T).inv X x
    (pureTensor (U.obj N) (U.obj T) X y z)
  have hR₃ := congrArg (fun w ↦ pureTensor M (N ⊗ T) Y x' w)
    (P.tensor_pure N T X y z)
  have hR := hR₁.trans (hR₂.trans hR₃)
  have hA := restriction_map P (α_ M N T).hom X
    ((P.tensor (M ⊗ N) T).inv.val.app X
      ((tensorMap (P.tensor M N).inv (𝟙 (U.obj T))).val.app X
        (pureTensor _ _ X (pureTensor _ _ X x y) z)))
  have h := hA.trans ((congrArg ((α_ M N T).hom.val.app Y) hL').trans
    ((pure_associator M N T Y x' y' z').trans hR.symm))
  exact h

end CategoryTheory.TwistedActionRingedSite
