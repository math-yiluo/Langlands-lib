/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Global sections of internal Hom -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private noncomputable def freeUnitRegularIso
    (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    (Mod.free R).obj (𝟙_ _) ≅ Mod.regular R :=
  Mod.isoMk (ρ_ R) (by
    change (α_ R R (𝟙_ _)).inv ≫ μ[R] ▷ (𝟙_ _) ≫ (ρ_ R).hom =
      R ◁ (ρ_ R).hom ≫ μ[R]
    monoidal)

private noncomputable def regularSectionsIso
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] :
    preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ X))) ≅
      condensedModuleSections Λ X := by
  let J := Scheme.ProEt.topology X
  let R := condensedRingObj Λ X
  let T := Scheme.ProEt.mk (𝟙 X)
  have hT : IsTerminal T :=
    IsTerminal.ofUniqueHom (fun V ↦ MorphismProperty.Over.homMk V.hom) fun V f ↦
      MorphismProperty.Over.Hom.ext <| by
        change f.left = V.hom
        rw [← MorphismProperty.Over.w f]
        exact (Category.comp_id _).symm
  have : (Mod.free R).Additive := (Mod.freeForgetAdjunction R).left_adjoint_additive
  let e : preadditiveCoyoneda.obj (op (𝟙_ (Sheaf J Ab.{u + 1}))) ≅
      sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op T) :=
    NatIso.ofComponents
      (fun F ↦ (Sheaf.evaluationEquiv J T hT F).toAddCommGrpIso) (by
        intro F G f
        ext a
        exact (Sheaf.evaluationEquiv_naturality J T hT f a).symm)
  exact preadditiveCoyoneda.mapIso (freeUnitRegularIso X R).op ≪≫
    (Mod.freeForgetAdjunction R).preadditiveCoyonedaObjIso (𝟙_ _) ≪≫
    Functor.isoWhiskerLeft (Mod.forget R) e

set_option backward.isDefEq.respectTransparency false in
/-- Sections of internal Hom are the additive group of module morphisms, naturally
in the second module.  No freeness or boundedness is required.
Source: Stacks Project, Tag 08JJ, tensor-Hom adjunction and evaluation.
(auxiliary; not a blueprint node)

Proof: evaluation at the terminal pro-etale object is Hom from the constant integer
sheaf.  The free-module adjunction therefore identifies module sections with Hom
from the regular module.  Apply the module tensor-Hom adjunction at that regular
module; its tensor product with P is P by the unit isomorphism. -/
theorem condensed_internal_hom_sections
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Nonempty (Mod.ihom P ⋙ condensedModuleSections Λ X ≅ preadditiveCoyoneda.obj (op P)) := by
  let R := condensedRingObj Λ X
  have : (Mod.tensorLeft P).Additive := (Mod.ihomAdjunction P).left_adjoint_additive
  let e : (Mod.tensorLeft P).obj (Mod.regular R) ≅ P :=
    (Mod.relativeTensorRightIso P).app (Mod.regular R) ≪≫ (λ_ P)
  exact ⟨Functor.isoWhiskerLeft (Mod.ihom P) (regularSectionsIso X Λ).symm ≪≫
    ((Mod.ihomAdjunction P).preadditiveCoyonedaObjIso (Mod.regular R)).symm ≪≫
    preadditiveCoyoneda.mapIso e.op.symm⟩

end AlgebraicGeometry.ProEtale
