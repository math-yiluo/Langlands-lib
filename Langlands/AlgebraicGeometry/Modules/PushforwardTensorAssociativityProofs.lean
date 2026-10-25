import Langlands.AlgebraicGeometry.Modules.PushforwardTensorAssociativityStatement

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Scheme.Modules

-- This lax structure is derived from strong sheafification, without using pushforward.
local instance pushforwardAssociativityForgetLax (X : Scheme.{u}) :
    (Scheme.Modules.toPresheafOfModules X).LaxMonoidal :=
  (sheafifyAdjunction X).rightAdjointLaxMonoidal

variable {X Y : Scheme.{u}}

private lemma modules_comp_val {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    (a ≫ b).val = a.val ≫ b.val := rfl

private lemma forgetTensorComparison (M N : X.Modules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.toPresheafOfModules X) M N =
      tensorSheafifyUnit M N ≫ (localizedTensorIso X M N).inv.val := by
  rfl

private lemma tensorSheafifyUnit_eq_forgetComparison (M N : X.Modules) :
    tensorSheafifyUnit M N =
      Functor.LaxMonoidal.μ (Scheme.Modules.toPresheafOfModules X) M N ≫
        (localizedTensorIso X M N).hom.val := by
  rw [forgetTensorComparison, Category.assoc, ← SheafOfModules.comp_val,
    Iso.inv_hom_id, SheafOfModules.id_val, Category.comp_id]

/-- The localized tensor comparison intertwines the two fixed associators. -/
lemma localizedTensorIso_associativity (M N P : X.Modules) :
    ((localizedTensorIso X M N).hom ⊗ₘ 𝟙 P) ≫
        (localizedTensorIso X (tensorObj M N) P).hom ≫ (tensorAssociator M N P).hom =
      (α_ M N P).hom ≫ (𝟙 M ⊗ₘ (localizedTensorIso X N P).hom) ≫
        (localizedTensorIso X M (tensorObj N P)).hom := by
  simp only [tensorAssociator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((localizedTensorIso X M N).hom ⊗ₘ 𝟙 P),
    tensorHom_comp_tensorHom, Iso.hom_inv_id, Category.id_comp, id_tensorHom_id,
    Category.id_comp]

-- Transport forgetful lax associativity through the fixed localized tensor comparison.
@[reassoc]
private lemma tensorSheafifyUnit_associator (M N P : X.Modules) :
    (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val) ≫ tensorSheafifyUnit (tensorObj M N) P ≫
        (tensorAssociator M N P).hom.val =
      (α_ M.val N.val P.val).hom ≫ (𝟙 M.val ⊗ₘ tensorSheafifyUnit N P) ≫
        tensorSheafifyUnit M (tensorObj N P) := by
  let U := Scheme.Modules.toPresheafOfModules X
  change tensorSheafifyUnit M N ▷ U.obj P ≫ tensorSheafifyUnit (tensorObj M N) P ≫
      U.map (tensorAssociator M N P).hom =
    (α_ (U.obj M) (U.obj N) (U.obj P)).hom ≫ U.obj M ◁ tensorSheafifyUnit N P ≫
      tensorSheafifyUnit M (tensorObj N P)
  rw [tensorSheafifyUnit_eq_forgetComparison M N,
    tensorSheafifyUnit_eq_forgetComparison (tensorObj M N) P,
    tensorSheafifyUnit_eq_forgetComparison N P,
    tensorSheafifyUnit_eq_forgetComparison M (tensorObj N P)]
  change (Functor.LaxMonoidal.μ U M N ≫ U.map (localizedTensorIso X M N).hom) ▷ U.obj P ≫
      Functor.LaxMonoidal.μ U (tensorObj M N) P ≫
      U.map (localizedTensorIso X (tensorObj M N) P).hom ≫
      U.map (tensorAssociator M N P).hom =
    (α_ (U.obj M) (U.obj N) (U.obj P)).hom ≫
      U.obj M ◁ (Functor.LaxMonoidal.μ U N P ≫ U.map (localizedTensorIso X N P).hom) ≫
      Functor.LaxMonoidal.μ U M (tensorObj N P) ≫
      U.map (localizedTensorIso X M (tensorObj N P)).hom
  simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc]
  simp only [← U.map_comp, ← tensorHom_id, ← id_tensorHom]
  rw [localizedTensorIso_associativity]
  simp only [U.map_comp, tensorHom_id, id_tensorHom]
  rw [Functor.LaxMonoidal.associativity_assoc]

-- The nested unit detects maps because sheafification inverts the adjunction unit
-- and preserves tensors. The presheaf unit itself need not be an epimorphism.
private lemma tensorTriple_hom_ext (M N P Q : X.Modules)
    (a b : tensorObj (tensorObj M N) P ⟶ Q)
    (h : (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val) ≫
        tensorSheafifyUnit (tensorObj M N) P ≫ a.val =
      (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val) ≫
        tensorSheafifyUnit (tensorObj M N) P ≫ b.val) : a = b := by
  let pushforwardAssociativityIsoSheafifyUnit :
      IsIso ((sheafify X).map (tensorSheafifyUnit M N)) := by
    change IsIso ((sheafify X).map ((sheafifyAdjunction X).unit.app (M.val ⊗ N.val)))
    infer_instance
  let pushforwardAssociativityIsoSheafifyTensorUnit :
      IsIso ((sheafify X).map (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val)) := by
    rw [Functor.Monoidal.map_tensor]
    infer_instance
  apply (cancel_epi ((sheafify X).map (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val))).1
  apply ((sheafifyAdjunction X).homEquiv _ Q).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  change (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val) ≫
      tensorSheafifyUnit (tensorObj M N) P ≫ a.val =
    (tensorSheafifyUnit M N ⊗ₘ 𝟙 P.val) ≫
      tensorSheafifyUnit (tensorObj M N) P ≫ b.val
  exact h

@[reassoc]
private lemma tensorSheafifyUnit_tensorMap {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafifyUnit M N ≫ (tensorMap a b).val =
      (a.val ⊗ₘ b.val) ≫ tensorSheafifyUnit M' N' :=
  (tensorSheafifyUnit_naturality a b).symm

@[reassoc]
private lemma tensorSheafifyUnit_pushforwardTensorApp (f : X ⟶ Y) (M N : X.Modules) :
    tensorSheafifyUnit ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ≫ (pushforwardTensorApp f M N).val =
      pushforwardTensorPresheafHom f M N := by
  change tensorHomEquiv _ _ _ (pushforwardTensorApp f M N) = _
  exact tensorHomEquiv_pushforwardTensorApp f M N

set_option maxRecDepth 4000 in
/-- Associativity of the fixed canonical pushforward tensor comparison. -/
theorem pushforwardTensorAssociativity : PushforwardTensorAssociativityStatement.{u} := by
  intro X Y f M N P
  apply tensorTriple_hom_ext ((Scheme.Modules.pushforward f).obj M)
    ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).obj P) _ _ _
  simp only [modules_comp_val]
  rw [tensorSheafifyUnit_tensorMap_assoc, SheafOfModules.id_val,
    tensorSheafifyUnit_pushforwardTensorApp_assoc]
  rw [← Category.assoc (tensorSheafifyUnit ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) ⊗ₘ
      𝟙 ((Scheme.Modules.pushforward f).obj P).val),
    tensorHom_comp_tensorHom, Category.id_comp, tensorSheafifyUnit_pushforwardTensorApp]
  rw [tensorSheafifyUnit_associator_assoc, tensorSheafifyUnit_tensorMap_assoc,
    SheafOfModules.id_val, tensorSheafifyUnit_pushforwardTensorApp]
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp,
    tensorSheafifyUnit_pushforwardTensorApp]
  -- Both composites now reduce to reassociation of sections on the inverse-image open.
  refine PresheafOfModules.hom_ext
    (fun U => ModuleCat.MonoidalCategory.tensor_ext₃' (fun m n p => ?_))
  have h := congrArg
    (fun k => (k.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom
      (((m : M.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) ⊗ₜ
          (n : N.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))) ⊗ₜ
        (p : P.val.obj ((TopologicalSpace.Opens.map f.base).op.obj U))))
    (tensorSheafifyUnit_associator M N P)
  exact h

end Langlands.Scheme.Modules
