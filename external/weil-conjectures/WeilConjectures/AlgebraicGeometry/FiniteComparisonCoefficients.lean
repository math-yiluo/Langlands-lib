/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ConstantInternalModuleSheafEquivalence
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Specified finite coefficient realization and generator predicates

Source: blueprint finite comparison, coefficient paragraph
(auxiliary; not a blueprint node).

The constructions are kept separately so their coefficient-presentation lemmas can be
used by the localizing proof without a cyclic import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject
namespace AlgebraicGeometry.ProEtale

/-- View fixed-scalar module presheaves as internal modules before sheafification.
Source: blueprint finite comparison, coefficient identification in proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonPresheaf (X : Scheme.{u}) (B : Type) [CommRing B] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (X.ProEtᵒᵖ ⥤ Ab.{u + 1})
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) where
  obj F := by
    let act :
        (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)) ⊗
            (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ⟶
          (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      { app U := InternalAbelianSheafModule.ordinaryAction
          (S := ULift.{u + 1} B) (N := F.obj U)
        naturality U V f := by
          apply AddCommGrpCat.hom_ext_toIntLinearMap
          apply TensorProduct.ext'
          intro r m
          exact ((F.map f).hom.map_smul r m).symm }
    letI : ModObj
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))
        (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      ModObj.mk' _ act (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext'
        intro z m
        exact Int.cast_smul_eq_zsmul (M := F.obj U) (ULift.{u + 1} B) z.down m) (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext_threefold
        intro r s m
        exact mul_smul (α := ULift.{u + 1} B) (β := F.obj U) r s m)
    exact ⟨F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}⟩
  map f := Mod.homMk (Functor.whiskerRight f (forget₂ _ Ab.{u + 1})) (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r m
    exact (f.app U).hom.map_smul r m)
  map_id F := by apply Mod.hom_ext; rfl
  map_comp f g := by apply Mod.hom_ext; rfl

/-- Sheafify the ordinary fixed-scalar action as an internal constant-ring action.
Source: blueprint finite comparison, proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonConstantRealization (X : Scheme.{u}) (B : Type) [CommRing B] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))) :=
  sheafToPresheaf _ _ ⋙ finiteComparisonPresheaf X B ⋙
    (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod _

private noncomputable def finiteComparisonPresheafEncodingIso
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    finiteComparisonPresheaf X B ⋙
        ConstantInternalModuleSheafEncoding.modulePresheafEncoding
          (C := X.ProEt) (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) ≅
      𝟭 (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; rfl)
  · intro U V f
    ext m
    rfl
  · intro F G f
    ext U m
    rfl

private theorem finiteComparisonConstantRealization_isEquivalence
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    (finiteComparisonConstantRealization X B).IsEquivalence := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let A := ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) R
  let G := internalToModule R
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R G rfl
  let L := finiteComparisonConstantRealization X B
  let E := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ finiteComparisonPresheaf X B
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt) R G
  let adj := (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction A
  have hu (M : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (adj.unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (Mod.forget A)]
    change IsIso ((adj.unit.app (E.obj M)).hom)
    rw [Adjunction.mapModAdjunction_unit_app_hom]
    exact isIso_toSheafify J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M).property
  let η := Functor.whiskerRight (Functor.whiskerLeft E adj.unit) P
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Functor.map_isIso P (adj.unit.app (E.obj M))
  let e0 : E ⋙ P ≅ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    Functor.isoWhiskerLeft _ (finiteComparisonPresheafEncodingIso X B)
  let e : (L ⋙ H) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) ≅
      (𝟭 _) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    (asIso η).symm ≪≫ e0
  let i := ((fullyFaithfulSheafToPresheaf J (ModuleCat.{u + 1} R)).whiskeringRight _)
    |>.preimageIso e
  have : (L ⋙ H).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  exact Functor.isEquivalence_of_comp_right L H

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- Transport the sheafified scalar action along the specified coefficient ring isomorphism.
The isomorphism is exactly the pullback of the finite-discrete point identification.
Source: blueprint finite comparison, proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonRealization (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) :=
  finiteComparisonConstantRealization X B ⋙
    Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv

/-- The specified coefficient transport is an exact equivalence.
Source: blueprint finite comparison, coefficient paragraph and proof step 1
(auxiliary; not a blueprint node).

Proof: an internal presheaf action is precisely the sectionwise scalar action.
Monoidal sheafification extends it uniquely to the associated constant ring sheaf.
Restriction along constant sections is inverse: local scalar representatives and
sheaf uniqueness recover both the action and every linear map. The unit and counit
are the sheafification identifications on underlying abelian sheaves. Transport along
`finiteDiscreteSchemeRingIso` has inverse transport along its inverse ring map.
The two composite functors are inverse and retain the underlying additive sheaves,
so preserve finite limits, finite colimits, and addition. This includes the zero ring
and empty scheme. -/
theorem finiteComparisonRealization_exact (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    (finiteComparisonRealization B X eR).IsEquivalence ∧
    (finiteComparisonRealization B X eR).Additive ∧
    PreservesFiniteLimits (finiteComparisonRealization B X eR) ∧
    PreservesFiniteColimits (finiteComparisonRealization B X eR) := by
  let _ : DiscreteTopology B := inferInstance
  let _ : Finite B := inferInstance
  have : (finiteComparisonConstantRealization X B).IsEquivalence :=
    finiteComparisonConstantRealization_isEquivalence X B
  have : (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (finiteDiscreteSchemeRingIso B X eR).inv)
      |>.isEquivalence_functor
  have : (finiteComparisonRealization B X eR).IsEquivalence := by
    unfold finiteComparisonRealization
    infer_instance
  have : (finiteComparisonRealization B X eR).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- Additivity of the specified coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (auxiliary; not a blueprint node). -/
instance finiteComparisonRealization_additive (X : Scheme.{u}) :
    (finiteComparisonRealization B X eR).Additive :=
  (finiteComparisonRealization_exact B X eR).2.1

/-- Left exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (auxiliary; not a blueprint node). -/
instance finiteComparisonRealization_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.1

/-- Right exactness of the coefficient transport, from the coefficient paragraph.
Source: blueprint finite comparison (auxiliary; not a blueprint node). -/
instance finiteComparisonRealization_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (finiteComparisonRealization B X eR) :=
  (finiteComparisonRealization_exact B X eR).2.2.2

end AlgebraicGeometry.ProEtale
