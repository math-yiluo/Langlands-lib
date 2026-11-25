/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedTensorDerivation.DerivedTensorComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExternalProduct
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedPushforwardFlat

/-!
# The supported exterior product

Supported coefficients are closed direct images of constant modules. The ordinary
adjunction is normalized by the quotient from constant coefficients. Its derived
adjunction and the coefficient tensor comparison specify the supported pairing.

## References

* Stacks Tag 09BM
-/

@[expose] public section

set_option autoImplicit false

-- Check proofs synchronously before the delivery appends its axiom probe.
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Use the existing preadditive tensor structure without reopening sheafification
instance search under each tensor-complex binder. -/
noncomputable instance supportedSheaf_monoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : MonoidalPreadditive (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      :=
  Sheaf.monoidalPreadditive

/-- Small colimits of pro-etale sheaves, supplied once to the cochain tensor instances. -/
theorem supportedSheaf_smallColimitsGeneric
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (Scheme.ProEt.topology X) C) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

attribute [local instance] supportedSheaf_smallColimitsGeneric

/-- Integer-indexed colimits of pro-etale sheaves, using the direct sheaf-colimit instance.
This avoids repeatedly searching through general colimit-shrinking instances when deriving
projection inverse images. -/
theorem supportedSheaf_intColimitsGeneric
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (X : Scheme.{u}) :
    HasColimitsOfShape ℤ (Sheaf (Scheme.ProEt.topology X) C) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] supportedSheaf_intColimitsGeneric

/-- The existing support kernel maps to evaluation on the terminal object. -/
noncomputable def supportedModuleSectionsToSections
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    supportSections i A ⟶
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj
        (op (Scheme.ProEt.mk (𝟙 X))) where
  app F := kernel.ι (F.obj.map (supportRestrictionArrow i).op)
  naturality F G f := by
    dsimp [supportSections, Sheaf.supportedSectionsFunctor]
    simp

/-- The inclusion of sections supported on `Z` into all global sections, via the
identification of global sections with evaluation at the terminal object. -/
noncomputable def supportedModuleSectionsι
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    supportSections i A ⟶ Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  supportedModuleSectionsToSections A i ≫
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
      (Scheme.ProEt.isTerminalMkId X)).inv

section TensorWrappers

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The existing monoidal sheafification property, with generic coefficients. -/
noncomputable instance supportedSheaf_isMonoidalGeneric (X : Scheme.{u}) :
    ((Scheme.ProEt.topology X).W (A := C)).IsMonoidal := GrothendieckTopology.W.monoidal

/-- The existing preadditive tensor structure, with generic coefficients. -/
noncomputable instance supportedSheaf_monoidalPreadditiveGeneric (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf (Scheme.ProEt.topology X) C) := Sheaf.monoidalPreadditive

/-- The existing sheaf tensor bifunctor at a variable scheme.
-/
@[implicit_reducible]
noncomputable def supportedSheafTensorGeneric (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) C ⥤ Sheaf (Scheme.ProEt.topology X) C ⥤ Sheaf
      (Scheme.ProEt.topology X) C := curriedTensor _

/-- The signed total tensor object, using the existing total complex construction. -/
noncomputable def supportedTotalTensorGeneric (X : Scheme.{u})
    (P Q : CochainComplex (Sheaf (Scheme.ProEt.topology X) C) ℤ) :=
  HomologicalComplex.tensorObj (C := Sheaf (Scheme.ProEt.topology X) C) (c := .up ℤ) P Q

-- Retain the existing flat-resolution parameter for compatibility with callers.
set_option linter.unusedSectionVars false in
/-- Tensor two sheaf morphisms using the upstream bifunctor.
-/
noncomputable def supportedSheafTensorMapGeneric (X : Scheme.{u})
    {M M' N N' : Sheaf (Scheme.ProEt.topology X) C} (a : M ⟶ M') (b : N ⟶ N') :
    ((supportedSheafTensorGeneric C X).obj M).obj N ⟶
      ((supportedSheafTensorGeneric C X).obj M').obj N' :=
  ((supportedSheafTensorGeneric C X).map a).app N ≫
    ((supportedSheafTensorGeneric C X).obj M').map b

end TensorWrappers

section ExternalProductProof
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

open Lean Lean.Meta Lean.Elab.Tactic in
private meta def supportedStructureCongr : Nat → MVarId → TacticM Unit
  | 0, _ => throwError "structural congruence exhausted"
  | fuel + 1, g => g.withContext do
      let ty ← instantiateMVars (← g.getType)
      if let some _ := ty.eq? then
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``eq_of_heq)
        for g' in gs do supportedStructureCongr fuel g'
      else if let some (_, lhs, _, rhs) := ty.heq? then
        if lhs == rhs || (← isProof lhs) then
          g.assign (← mkHEqRefl lhs)
        else
          let f := lhs.getAppFn
          if (← isDefEq f rhs.getAppFn) && lhs.getAppNumArgs == rhs.getAppNumArgs then
            let h ← mkHCongrWithArity f lhs.getAppNumArgs
            let gs ← g.apply h.proof { synthAssignedInstances := false }
            for g' in gs do supportedStructureCongr fuel g'
          else
            unless ← isDefEq lhs rhs do
              throwError "structural congruence: different heads {f} / {rhs.getAppFn}"
            g.assign (← mkHEqRefl lhs)
      else
        g.assign (← synthInstance ty)

attribute [-instance] supportedSheaf_monoidalPreadditive
  supportedSheaf_isMonoidalGeneric supportedSheaf_monoidalPreadditiveGeneric
  supportedSheaf_smallColimitsGeneric supportedSheaf_intColimitsGeneric in
private theorem normalization_tensorHom_eq (T : Scheme.{u})
    (S M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)) :
    (S ⟶ M ⊗ N) = (S ⟶ ((derivedTensor C T).obj M).obj N) := rfl

end ExternalProductProof

attribute [local irreducible] HomologicalComplex₂.total

/-- Sheaf tensor with the specified coefficient ring. -/
noncomputable abbrev supportedSheafTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) := supportedSheafTensorGeneric (ModuleCat.{u + 1} A) X

/-- Closed supported constant coefficients. -/
noncomputable def supportedCoefficients (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    ModuleCat.{u + 1} A ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i

/-- The quotient from constant coefficients to closed supported coefficients. -/
noncomputable def supportedCoefficientQuotient (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) (M : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶
      (supportedCoefficients A i).obj M :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _)
    ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) i).hom.app M)

/-- Additivity of closed supported coefficients. -/
noncomputable instance supportedCoefficients_additive
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (supportedCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ⋙
    lowerStar (ModuleCat.{u + 1} A) i).Additive)

set_option backward.isDefEq.respectTransparency true in
/-- The two existing presentations of the derived tensor give the same morphism type. -/
theorem supportedTensorHom_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (S M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (S ⟶ M ⊗ N) = (S ⟶ ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N) := by
  refine Eq.mp ?_ (normalization_tensorHom_eq (ModuleCat.{u + 1} A) X S M N)
  run_tac do
    for g in ← Lean.Elab.Tactic.getGoals do supportedStructureCongr 40 g
    Lean.Elab.Tactic.setGoals []

section OrdinaryAdjunctionProof
set_option backward.isDefEq.respectTransparency false

private theorem adjunctionNormalization
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {LZ : C ⥤ E} {RZ : E ⥤ C}
    {I : E ⥤ D} {J : D ⥤ E} {S : D ⥤ C}
    (ax : L ⊣ R) (az : LZ ⊣ RZ) (b : I ⊣ J)
    (γ : I ⋙ R ≅ RZ) (ε : J ⋙ RZ ≅ S) (δ : S ⟶ R)
    (M : C) (F : D) (q : L.obj M ⟶ I.obj (LZ.obj M))
    (hq : ax.unit.app M ≫ R.map q ≫ γ.hom.app (LZ.obj M) = az.unit.app M)
    (hc : ε.hom.app F ≫ δ.app F = γ.inv.app (J.obj F) ≫ R.map (b.counit.app F))
    (f : M ⟶ S.obj F) :
    q ≫ (((az.comp b).ofNatIsoRight ε).homEquiv M F).symm f =
      (ax.homEquiv M F).symm (f ≫ δ.app F) := by
  have hq' : ax.unit.app M ≫ R.map q =
      az.unit.app M ≫ γ.inv.app (LZ.obj M) := by
    erw [← hq]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
  apply (ax.homEquiv M F).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_apply, Adjunction.homEquiv_counit]
  erw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hq', Category.assoc,
    ← γ.inv.naturality_assoc]
  erw [← Category.assoc, ← Adjunction.homEquiv_apply, Equiv.apply_symm_apply]
  erw [Category.assoc, ← hc, Iso.inv_hom_id_app_assoc]

private lemma constantUnit_global
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {Z X : Scheme.{u}}
    (i : Z ⟶ X) (M : C) :
    (constantSheafΓAdj (Scheme.ProEt.topology X) C).unit.app M ≫
      (Sheaf.Γ (Scheme.ProEt.topology X) C).map
        (((upperStarLowerStarAdjunction C i).unit.app _ ≫
          (lowerStar C i).map ((constantSheafCompUpperStarIso C i).hom.app M))) ≫
      (globalSectionsLowerStarIso C i).hom.app _ =
    (constantSheafΓAdj (Scheme.ProEt.topology Z) C).unit.app M := by
  let ax := constantSheafΓAdj (Scheme.ProEt.topology X) C
  let az := constantSheafΓAdj (Scheme.ProEt.topology Z) C
  let p := upperStarLowerStarAdjunction C i
  let e := globalSectionsLowerStarIso C i
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((ax.comp p).ofNatIsoRight e) az M
  rw [Adjunction.homEquiv_unit] at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc] at h
  change (ax.comp p).unit.app M ≫ e.hom.app _ ≫
    (Sheaf.Γ (Scheme.ProEt.topology Z) C).map
      ((constantSheafCompUpperStarIso C i).hom.app M) = az.unit.app M at h
  rw [← h]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← e.hom.naturality]
  rfl

private lemma lowerStar_obj_val_map
    (C : Type v) [Category.{u + 1} C] {T R : Scheme.{u}} (t : T ⟶ R)
    (G : Sheaf (Scheme.ProEt.topology T) C) {b b' : R.ProEt} (φ : b ⟶ b') :
    ((lowerStar C t).obj G).obj.map φ.op =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ t).map φ).op := rfl

section Site

variable {X : Scheme.{u}}

/-- A morphism of étale `X`-schemes whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
private lemma aux_isIso_of_isIso_left {V W : X.ProEt} (f : V ⟶ W)
    (hf : IsIso f.left) : IsIso f := by
  have := hf
  let e : V ≅ W := MorphismProperty.Over.isoMk (asIso f.left)
    (MorphismProperty.Over.w f)
  have h : e.hom = f := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  rw [← h]
  infer_instance

variable {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The counit `U ×_X U ⟶ U` at `U` of the adjunction between composition with and base change
along the open immersion `j` is an isomorphism, `j` being a monomorphism. -/
private theorem aux_isIso_mapPullbackAdj_counit_app_mk :
    IsIso ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance trivial).counit.app
      (Scheme.ProEt.mk j)) :=
  aux_isIso_of_isIso_left _ (inferInstanceAs (IsIso (pullback.fst j j)))

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

/-- The base change along the open immersion `j` of the map from `U` to the terminal étale
`X`-scheme `X` is an isomorphism `U ×_X U ≅ X ×_X U`, both being isomorphic to `U` over `U`. -/
private theorem aux_isIso_overPullback_map_isTerminalMkId_from :
    IsIso ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).map
      ((Scheme.ProEt.isTerminalMkId X).from (Scheme.ProEt.mk j))) := by
  refine aux_isIso_of_isIso_left _ ?_
  have h := MorphismProperty.Over.w ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).map
    ((Scheme.ProEt.isTerminalMkId X).from (Scheme.ProEt.mk j)))
  have : IsIso ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj (Scheme.ProEt.mk j)).hom :=
    inferInstanceAs (IsIso (pullback.snd j j))
  have : IsIso
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj (Scheme.ProEt.mk (𝟙 X))).hom :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 X) j))
  exact IsIso.of_isIso_fac_right h

end Site

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

section Restriction

attribute [local instance] aux_isIso_mapPullbackAdj_counit_app_mk

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

attribute [local instance] aux_isIso_overPullback_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `G` on `U`, the restriction `(j_* G)(X) ⟶ (j_* G)(U)` along the open immersion
`j` is an isomorphism: both are the sections of `G` over `U`. -/
private theorem aux_isIso_lowerStar_obj_map_isTerminalMkId_from
    (G : Sheaf (Scheme.ProEt.topology U) C) :
    IsIso (((j)_*[C].obj G).obj.map ((Scheme.ProEt.isTerminalMkId X).from
      (Scheme.ProEt.mk j)).op) := by
  rw [lowerStar_obj_val_map]
  infer_instance

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
/-- For a sheaf `M` on `X`, the unit `M ⟶ j_* j^* M` of the restriction along the open immersion
`j` is an isomorphism on the sections over `U`. -/
private theorem aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
    (M : Sheaf (Scheme.ProEt.topology X) C) :
    IsIso (((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
      (op (Scheme.ProEt.mk j))) :=
  inferInstanceAs (IsIso (𝟙 _ ≫ M.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    inferInstance trivial).counit.app (Scheme.ProEt.mk j)).op ≫ 𝟙 _))

attribute [local instance] aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk

/-- The restriction `Γ(X, M) ⟶ M(U)` from the global sections to the sections over `U` is the
restriction along the map from `U` to the terminal étale `X`-scheme, preceded by the isomorphism
`Γ(X, M) ≅ M(X)`. -/
private lemma aux_ΓRes_eq (M : Sheaf (Scheme.ProEt.topology X) C) :
    M.ΓRes (op (Scheme.ProEt.mk j)) =
      M.ΓRes (op (Scheme.ProEt.mk (𝟙 X))) ≫
        M.obj.map ((Scheme.ProEt.isTerminalMkId X).from (Scheme.ProEt.mk j)).op :=
  (M.ΓRes_map _).symm

private theorem aux_isIso_ΓRes_terminal (M : Sheaf (Scheme.ProEt.topology X) C) :
    IsIso (M.ΓRes (op (Scheme.ProEt.mk (𝟙 X)))) :=
  M.isLimitConeΓ.isIso_π_app_of_isInitial _ (Scheme.ProEt.isTerminalMkId X).op

attribute [local instance] aux_isIso_ΓRes_terminal
end Restriction

section Sections

attribute [local instance] aux_isIso_lowerStar_obj_map_isTerminalMkId_from
  aux_isIso_openImmersionRestrictionLowerStarAdjunction_unit_app_hom_app_mk
  aux_isIso_ΓRes_terminal
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For a sheaf `G` on `U`, the restriction `Γ(X, j_* G) ⟶ (j_* G)(U)` is an isomorphism. -/
private theorem normalization_isIso_ΓRes_lowerStar_obj (G : Sheaf (Scheme.ProEt.topology U) C) :
    IsIso (((j)_*[C].obj G).ΓRes (op (Scheme.ProEt.mk j))) := by
  rw [aux_ΓRes_eq]
  infer_instance

attribute [local instance] normalization_isIso_ΓRes_lowerStar_obj

/-- The sections over `U` of the inclusion `𝒢_Z M ⟶ M` of the supported sections vanish, so the
global sections of the inclusion restrict to zero on `U`. -/
@[reassoc]
private lemma normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes
    (M : Sheaf (Scheme.ProEt.topology X) C) :
    (Sheaf.Γ (Scheme.ProEt.topology X) C).map ((sectionsWithSupportι C j).app M) ≫
      M.ΓRes (op (Scheme.ProEt.mk j)) = 0 := by
  erw [Sheaf.ΓRes_naturality]
  have : IsZero (((sectionsWithSupport C j).obj M).obj.obj (op (Scheme.ProEt.mk j))) :=
    by
      let H := (sectionsWithSupport C j).obj M
      have hz : IsZero ((openImmersionRestriction C j).obj H) :=
        (isZero_upperStar_sectionsWithSupport C j M).of_iso
          ((upperStarIsoOpenImmersionRestriction C j).app H).symm
      have he := ((sheafSections (Scheme.ProEt.topology U) C).obj
        (op (Scheme.ProEt.mk (𝟙 U)))).map_isZero hz
      let e : (MorphismProperty.Over.map ⊤
          (inferInstance : @WeaklyEtale _ _ j)).obj (Scheme.ProEt.mk (𝟙 U)) ≅
          Scheme.ProEt.mk j :=
        MorphismProperty.Over.isoMk (Iso.refl U) (by simp)
      exact he.of_iso (H.obj.mapIso e.op)
  rw [this.eq_of_tgt (Sheaf.ΓRes _ _) 0, zero_comp]

/-- The global sections of the unit `M ⟶ j_* j^* M` are the restriction `Γ(X, M) ⟶ M(U)`
followed by the identification `M(U) ≅ (j_* j^* M)(U) ≅ Γ(X, j_* j^* M)`. -/
private lemma normalization_ΓMap_unit_app_eq (M : Sheaf (Scheme.ProEt.topology X) C) :
    (Sheaf.Γ (Scheme.ProEt.topology X) C).map ((upperStarLowerStarAdjunction C j).unit.app M) =
      M.ΓRes (op (Scheme.ProEt.mk j)) ≫
        ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M).hom.app
          (op (Scheme.ProEt.mk j)) ≫
        inv (((j)_*[C].obj ((openImmersionRestriction C j).obj M)).ΓRes
          (op (Scheme.ProEt.mk j))) ≫
        (Sheaf.Γ (Scheme.ProEt.topology X) C).map ((j)_*[C].map
          (((upperStarLowerStarAdjunction C j).leftAdjointUniq
            (openImmersionRestrictionLowerStarAdjunction C j)).inv.app M)) := by
  have h₁ := Sheaf.ΓRes_naturality ((openImmersionRestrictionLowerStarAdjunction C j).unit.app M)
    (op (Scheme.ProEt.mk j))
  rw [← reassoc_of% h₁, IsIso.hom_inv_id_assoc, ← Functor.map_comp]
  congr 1
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction C j)
    (openImmersionRestrictionLowerStarAdjunction C j), Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp

/-- The global sections of the inclusion `𝒢_Z M ⟶ M` of the sections supported on the closed
complement `Z` of `j` form a kernel of the restriction `Γ(X, M) ⟶ M(U)`: `Γ` preserves the kernel
`𝒢_Z M` of `M ⟶ j_* j^* M`, and `Γ(X, M) ⟶ Γ(X, j_* j^* M)` is the restriction `Γ(X, M) ⟶ M(U)`
followed by an isomorphism (`AlgebraicGeometry.Etale.normalization_ΓMap_unit_app_eq`). -/
private noncomputable def normalization_isLimitΓMapSectionsWithSupportι
    (M : Sheaf (Scheme.ProEt.topology X) C) :
    IsLimit (KernelFork.ofι _ (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)) :=
  isKernelOfComp _ _ (KernelFork.mapIsLimit _
    (kernelIsKernel ((upperStarLowerStarAdjunction C j).unit.app M))
      (Sheaf.Γ (Scheme.ProEt.topology X) C))
    (normalization_ΓMap_sectionsWithSupportι_app_comp_ΓRes C j M)
    (normalization_ΓMap_unit_app_eq C j M).symm

end Sections

private lemma globalTerminalIso_hom
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] (X : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology X) C) :
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) C
      (Scheme.ProEt.isTerminalMkId X)).hom.app F =
      F.ΓRes (op (Scheme.ProEt.mk (𝟙 X))) := by
  let ax := constantSheafΓAdj (Scheme.ProEt.topology X) C
  let aT := constantSheafAdj (Scheme.ProEt.topology X) C
    (Scheme.ProEt.isTerminalMkId X)
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app ax aT F
  have h' := congrArg (aT.homEquiv _ _) h
  rw [Equiv.apply_symm_apply] at h'
  change _ = _ at h'
  rw [Sheaf.ΓNatIsoSheafSections]
  rw [h']
  simp only [aT, constantSheafAdj, Adjunction.comp_homEquiv,
    Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv, Equiv.symm_trans_apply]
  erw [Adjunction.homEquiv_symm_id]
  erw [Adjunction.homEquiv_apply]
  simp [constantPresheafAdj]
  rfl

section RawSupport
variable (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i]

private lemma rawSupport_condition
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportedModuleSectionsι A i).app F ≫
      F.ΓRes (op (Scheme.ProEt.mk i.openComplement.ι)) = 0 := by
  have hr := F.ΓRes_map (supportRestrictionArrow i).op
  change F.ΓRes (op (Scheme.ProEt.mk (𝟙 X))) ≫
    F.obj.map (supportRestrictionArrow i).op = _ at hr
  rw [← globalTerminalIso_hom (ModuleCat.{u + 1} A) X F] at hr
  rw [← hr]
  simp [supportedModuleSectionsι, supportedModuleSectionsToSections]

private noncomputable def normalization_isLimitRawSupport
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    IsLimit (KernelFork.ofι _ (rawSupport_condition A i F)) := by
  let γ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId X)
  refine KernelFork.isLimitOfIsLimitOfIff
    (kernelIsKernel (F.obj.map (supportRestrictionArrow i).op))
    (F.ΓRes (op (Scheme.ProEt.mk i.openComplement.ι))) (γ.app F).symm ?_
  intro V φ
  have hr := F.ΓRes_map (supportRestrictionArrow i).op
  change F.ΓRes (op (Scheme.ProEt.mk (𝟙 X))) ≫
    F.obj.map (supportRestrictionArrow i).op = _ at hr
  rw [← globalTerminalIso_hom (ModuleCat.{u + 1} A) X F] at hr
  rw [← hr]
  simp [γ]

private noncomputable def normalization_sectionsWithSupportCompΓIso :
    sectionsWithSupport (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
      Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ≅ supportSections i A :=
  NatIso.ofComponents
    (fun (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ↦
      (normalization_isLimitΓMapSectionsWithSupportι (ModuleCat.{u + 1} A)
        i.openComplement.ι F).conePointUniqueUpToIso
        (normalization_isLimitRawSupport A i F))
    (fun {F G} f ↦ by
      apply Fork.IsLimit.hom_ext (normalization_isLimitRawSupport A i G)
      change _ ≫ (supportedModuleSectionsι A i).app G =
        _ ≫ (supportedModuleSectionsι A i).app G
      have hF := (normalization_isLimitΓMapSectionsWithSupportι (ModuleCat.{u + 1} A)
        i.openComplement.ι F).conePointUniqueUpToIso_hom_comp
        (normalization_isLimitRawSupport A i F) .zero
      have hG := (normalization_isLimitΓMapSectionsWithSupportι (ModuleCat.{u + 1} A)
        i.openComplement.ι G).conePointUniqueUpToIso_hom_comp
        (normalization_isLimitRawSupport A i G) .zero
      simp only [KernelFork.ofι, Fork.ofι_π_app] at hF hG
      simp only [Functor.comp_map, Category.assoc, hG]
      erw [(supportedModuleSectionsι A i).naturality f, reassoc_of% hF]
      erw [← Functor.map_comp, ← Functor.map_comp,
        ← (sectionsWithSupportι (ModuleCat.{u + 1} A) i.openComplement.ι).naturality f])

@[reassoc (attr := simp)]
private lemma normalization_sectionsWithSupportCompΓIso_hom_app_comp
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (normalization_sectionsWithSupportCompΓIso A i).hom.app F ≫
        (supportedModuleSectionsι A i).app F =
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        ((sectionsWithSupportι (ModuleCat.{u + 1} A) i.openComplement.ι).app F) := by
  let e := normalization_isLimitΓMapSectionsWithSupportι (ModuleCat.{u + 1} A)
    i.openComplement.ι F
  have h := e.conePointUniqueUpToIso_hom_comp (normalization_isLimitRawSupport A i F) .zero
  dsimp only [normalization_sectionsWithSupportCompΓIso, NatIso.ofComponents]
  exact h

variable [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
private theorem complementIsCompl :
    IsCompl (Set.range i.base) (Set.range i.openComplement.ι.base) := by
  rw [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement]
  exact isCompl_compl

private noncomputable def normalization_closedUpperShriekCompLowerStarIso :
    closedUpperShriek (ModuleCat.{u + 1} A) i i.openComplement.ι ⋙
        lowerStar (ModuleCat.{u + 1} A) i ≅
      sectionsWithSupport (ModuleCat.{u + 1} A) i.openComplement.ι :=
  Functor.isoWhiskerLeft
    (sectionsWithSupportLift (ModuleCat.{u + 1} A) i.openComplement.ι)
    (Functor.isoWhiskerRight
      (lowerStarLiftEquivalence (R := A) i i.openComplement.ι
        (complementIsCompl i)).unitIso.symm
      (supportedAway (ModuleCat.{u + 1} A) i.openComplement.ι).ι)

private lemma normalization_closedCounit
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStarClosedUpperShriekAdjunction (R := A) i i.openComplement.ι
      (complementIsCompl i)).counit.app F =
      (normalization_closedUpperShriekCompLowerStarIso A i).hom.app F ≫
        (sectionsWithSupportι (ModuleCat.{u + 1} A) i.openComplement.ι).app F := by
  simp only [lowerStarClosedUpperShriekAdjunction, Adjunction.ofNatIsoRight_counit,
    Adjunction.ofNatIsoLeft_counit]
  rfl

private noncomputable def normalization_closedUpperShriekCompΓIso :
    closedUpperShriek (ModuleCat.{u + 1} A) i i.openComplement.ι ⋙
      Sheaf.Γ (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ≅ supportSections i A :=
  Functor.isoWhiskerLeft _ (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (normalization_closedUpperShriekCompLowerStarIso A i) _ ≪≫
    normalization_sectionsWithSupportCompΓIso A i

private lemma normalization_closedUpperShriekCompΓIso_hom_comp
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (normalization_closedUpperShriekCompΓIso A i).hom.app F ≫
      (supportedModuleSectionsι A i).app F =
      (globalSectionsLowerStarIso (ModuleCat.{u + 1} A) i).inv.app
        ((closedUpperShriek (ModuleCat.{u + 1} A) i i.openComplement.ι).obj F) ≫
      (Sheaf.Γ (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        ((lowerStarClosedUpperShriekAdjunction (R := A) i i.openComplement.ι
          (complementIsCompl i)).counit.app F) := by
  simp only [normalization_closedUpperShriekCompΓIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc,
    normalization_sectionsWithSupportCompΓIso_hom_app_comp,
    normalization_closedCounit, Functor.map_comp]

end RawSupport
private theorem closedUnit_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app G) := by
  let C := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  let adj := upperStarLowerStarAdjunction C i
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact isCompl_compl.symm
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ ?_ ?_)
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C i) (adj.unit.app G))
    have : IsIso ((upperStar C i).map (adj.unit.app G)) := by
      have : IsIso ((upperStar C i).map (adj.unit.app G) ≫ adj.counit.app _) := by
        rw [adj.left_triangle_components G]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    exact isZero_cokernel_of_epi _
  · refine IsZero.of_iso ?_ (PreservesCokernel.iso (upperStar C j) (adj.unit.app G))
    refine IsZero.of_epi (cokernel.π _) ?_
    exact isZero_upperStar_lowerStar_of_disjoint C i j hij.disjoint _

private theorem coefficientQuotient_epi
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (M : ModuleCat.{u + 1} A) : Epi (supportedCoefficientQuotient A i M) := by
  change Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) i).hom.app M))
  have := closedUnit_epi A i
    ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)
  infer_instance

private theorem ordinaryAdjunctionExists
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    ∃ a : supportedCoefficients A i ⊣ supportSections i A,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportSections i A).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).homEquiv
          M F).symm (f ≫ (supportedModuleSectionsι A i).app F) := by
  let C := ModuleCat.{u + 1} A
  let b := lowerStarClosedUpperShriekAdjunction (R := A) i i.openComplement.ι
    (complementIsCompl i)
  let e := normalization_closedUpperShriekCompΓIso A i
  let a : supportedCoefficients A i ⊣ supportSections i A :=
    ((constantSheafΓAdj (Scheme.ProEt.topology Z) C).comp b).ofNatIsoRight e
  refine ⟨a, ?_⟩
  intro M F f
  exact adjunctionNormalization (constantSheafΓAdj (Scheme.ProEt.topology X) C)
    (constantSheafΓAdj (Scheme.ProEt.topology Z) C) b (globalSectionsLowerStarIso C i)
    e (supportedModuleSectionsι A i) M F
    (supportedCoefficientQuotient A i M) (constantUnit_global C i M)
    (normalization_closedUpperShriekCompΓIso_hom_comp A i F) f
end OrdinaryAdjunctionProof

/-- The ordinary adjunction, uniquely normalized by inclusion of the support kernel. -/
theorem exists_unique_supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    ∃! a : supportedCoefficients A i ⊣ supportSections i A,
      ∀ (M : ModuleCat.{u + 1} A)
        (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (f : M ⟶ (supportSections i A).obj F),
      supportedCoefficientQuotient A i M ≫ (a.homEquiv M F).symm f =
        ((constantSheafΓAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).homEquiv M F).symm
          (f ≫ (supportedModuleSectionsι A i).app F) := by
  obtain ⟨a, ha⟩ := ordinaryAdjunctionExists A i
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Adjunction.ext_counit
  apply NatTrans.ext
  funext F
  let M := (supportSections i A).obj F
  have := coefficientQuotient_epi A i M
  have h := (cancel_epi (supportedCoefficientQuotient A i M)).1
    ((ha' M F (𝟙 _)).trans (ha M F (𝟙 _)).symm)
  simp only [Adjunction.homEquiv_symm_apply] at h
  erw [(supportedCoefficients A i).map_id M, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency true

/-- Canonical ordinary supported-coefficient adjunction, selected from its unique
normalization. -/
noncomputable def supportedCoefficientAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    supportedCoefficients A i ⊣ supportSections i A :=
  (exists_unique_supportedCoefficientAdjunction A i).choose

/-- Exactness of closed supported coefficients. -/
theorem supportedCoefficients_exact (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    PreservesFiniteLimits (supportedCoefficients A i) ∧
      PreservesFiniteColimits (supportedCoefficients A i) := by
  have := (supportedCoefficientAdjunction A i).leftAdjoint_preservesColimits
  exact ⟨inferInstanceAs (PreservesFiniteLimits
    (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) ⋙
      lowerStar (ModuleCat.{u + 1} A) i)), inferInstance⟩

/-- The finite-limit instance from closed-support exactness. -/
noncomputable instance supportedCoefficients_preservesFiniteLimits
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    PreservesFiniteLimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).1

/-- The finite-colimit instance from closed-support exactness. -/
noncomputable instance supportedCoefficients_preservesFiniteColimits
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    PreservesFiniteColimits (supportedCoefficients A i) := (supportedCoefficients_exact A i).2

/-- The unbounded support functor, extending the bounded-below injective construction. -/
noncomputable abbrev supportedSectionsDerived
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (supportSections i A).rightDerivedFunctor

/-- The pointwise constant-presheaf tensor comparison. -/
def constantPresheafTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (Functor.const T.ProEtᵒᵖ).obj (M ⊗ N) ⟶
      (Functor.const T.ProEtᵒᵖ).obj M ⊗ (Functor.const T.ProEtᵒᵖ).obj N where
  app _ := 𝟙 _
  naturality _ _ _ := by simp

/-- Constant coefficient tensor comparison before pulling back either factor.
-/
noncomputable def supportedConstantTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A X).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)).obj
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj N) :=
  (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
      (constantPresheafTensor A X M N) ≫
    (Functor.Monoidal.μIso (presheafToSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      ((Functor.const _).obj M) ((Functor.const _).obj N)).inv

/-- Tensor comparison for constant coefficients and the two projection pullbacks. -/
noncomputable def constantExteriorTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (M N : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology (pullback f g)) (ModuleCat.{u + 1} A)).obj (M ⊗ N) ⟶
      ((supportedSheafTensor A (pullback f g)).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).obj
          ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M))).obj
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).obj
          ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)).obj N)) :=
  supportedConstantTensor A (pullback f g) M N ≫
    supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
      ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv.app M)
      ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv.app N)

/-- Supported coefficients pulled back along the first projection. -/
noncomputable abbrev supportedFirstCoefficients (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y Z : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) :=
  supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)

/-- Supported coefficients pulled back along the second projection. -/
noncomputable abbrev supportedSecondCoefficients (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X Y W : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) :=
  supportedCoefficients A j ⋙ upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)

private theorem coefficientQuotient_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {M M' : ModuleCat.{u + 1} A} (f : M ⟶ M') :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map f ≫
        supportedCoefficientQuotient A i M' =
      supportedCoefficientQuotient A i M ≫ (supportedCoefficients A i).map f := by
  let η := Functor.whiskerLeft
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit
  let ν := Functor.whiskerRight
    (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) i).hom
    (lowerStar (ModuleCat.{u + 1} A) i)
  exact (η ≫ ν).naturality f

section CoefficientTensorProof

open scoped ZeroObject in
private theorem zero_of_open_cover
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] {T : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology T) C)
    {I : Type*} {V : I → Scheme.{u}} (a : ∀ k, V k ⟶ T)
    [∀ k, IsOpenImmersion (a k)]
    (ha : ⋃ k, Set.range (a k).base = Set.univ)
    (hF : ∀ k, IsZero ((upperStar C (a k)).obj F)) : IsZero F := by
  have hc : Presieve.ofArrows V a ∈ Scheme.proetalePrecoverage T :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨by
        intro x
        have hx : x ∈ ⋃ k, Set.range (a k).base := ha ▸ Set.mem_univ x
        exact Set.mem_iUnion.1 hx, fun _ ↦ inferInstance⟩)
  have h : IsIso (0 : F ⟶ 0) := by
    apply isIso_of_isIso_localizationRestriction C (0 : F ⟶ 0) a hc
    intro k
    have hz := (hF k).of_iso
      ((upperStarIsoOpenImmersionRestriction C (a k)).app F).symm
    exact hz.isIso ((localizationRestriction C (a k) inferInstance).map_isZero
      (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

private theorem coefficient_zero_on_complement
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (a : T ⟶ X)
    (ha : Set.range a.base ⊆ (i.openComplement : Set X))
    (M : ModuleCat.{u + 1} A) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) a).obj
      ((supportedCoefficients A i).obj M)) := by
  let C := ModuleCat.{u + 1} A
  let v := i.openComplement.ι
  have hav : Set.range a.base ⊆ Set.range v.base := by
    simpa only [v, Scheme.Opens.range_ι] using ha
  let l := IsOpenImmersion.lift v a hav
  have hz : IsZero ((upperStar C v).obj ((supportedCoefficients A i).obj M)) := by
    apply isZero_upperStar_lowerStar_of_disjoint C i v
    rw [show Set.range v.base = (Set.range i.base)ᶜ by
      simp [v, Scheme.Hom.coe_openComplement]]
    exact disjoint_compl_right
  have he : l ≫ v = a := IsOpenImmersion.lift_fac v a hav
  have hz' := ((upperStar C l).map_isZero hz).of_iso
    ((upperStarComp C l v).app _)
  rw [he] at hz'
  exact hz'

private theorem tensor_zero_on_union
    (A : Type (u + 1)) [CommRing A] [Finite A] {T X Y Z W : Scheme.{u}}
    (p : T ⟶ X) (q : T ⟶ Y) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (V : T.Opens) (hV : V = p ⁻¹ᵁ i.openComplement ⊔ q ⁻¹ᵁ j.openComplement)
    (M N : ModuleCat.{u + 1} A) :
    IsZero ((upperStar (ModuleCat.{u + 1} A) V.ι).obj
      (((upperStar (ModuleCat.{u + 1} A) p).obj ((supportedCoefficients A i).obj M)) ⊗
        ((upperStar (ModuleCat.{u + 1} A) q).obj ((supportedCoefficients A j).obj N)))) := by
  let C := ModuleCat.{u + 1} A
  let F := (upperStar C p).obj ((supportedCoefficients A i).obj M)
  let G := (upperStar C q).obj ((supportedCoefficients A j).obj N)
  let O : Bool → V.toScheme.Opens := fun b ↦
    if b then V.ι ⁻¹ᵁ (p ⁻¹ᵁ i.openComplement) else V.ι ⁻¹ᵁ (q ⁻¹ᵁ j.openComplement)
  have hcov : ⋃ b, Set.range (O b).ι.base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : V.ι.base x ∈ (p ⁻¹ᵁ i.openComplement : Set T) ∪
        (q ⁻¹ᵁ j.openComplement : Set T) := by
      change V.ι.base x ∈ ((p ⁻¹ᵁ i.openComplement ⊔ q ⁻¹ᵁ j.openComplement) : T.Opens)
      rw [← hV]
      exact x.2
    rcases hx with hx | hx
    · apply Set.mem_iUnion.2
      refine ⟨true, ?_⟩
      rw [Scheme.Opens.range_ι]
      exact hx
    · apply Set.mem_iUnion.2
      refine ⟨false, ?_⟩
      rw [Scheme.Opens.range_ι]
      exact hx
  apply zero_of_open_cover C _ (fun b ↦ (O b).ι) hcov
  intro b
  let a := (O b).ι ≫ V.ι
  have hz : IsZero ((upperStar C a).obj (F ⊗ G)) := by
    cases b
    · have hq : Set.range (a ≫ q).base ⊆ (j.openComplement : Set Y) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      have h₀ := coefficient_zero_on_complement A j (a ≫ q) hq N
      have hG : IsZero ((upperStar C a).obj G) :=
        h₀.of_iso ((upperStarComp C a q).app _).symm
      exact ((tensorLeft ((upperStar C a).obj F)).map_isZero hG).of_iso
        (Functor.Monoidal.μIso (upperStar C a) F G).symm
    · have hp : Set.range (a ≫ p).base ⊆ (i.openComplement : Set X) := by
        rintro _ ⟨x, rfl⟩
        exact x.2
      have h₀ := coefficient_zero_on_complement A i (a ≫ p) hp M
      have hF : IsZero ((upperStar C a).obj F) :=
        h₀.of_iso ((upperStarComp C a p).app _).symm
      exact ((tensorRight ((upperStar C a).obj G)).map_isZero hF).of_iso
        (Functor.Monoidal.μIso (upperStar C a) F G).symm
  exact hz.of_iso ((upperStarComp C (O b).ι V.ι).app (F ⊗ G)).symm

private theorem adjunction_factorization_equation
    {D E : Type*} [Category.{w} D] [Category.{w} E]
    {L : D ⥤ E} {R : E ⥤ D} (a : L ⊣ R) {P Q : D} {T : E}
    (b : L.obj P ≅ T) [IsIso (a.unit.app Q)] (α : P ⟶ Q) :
    a.homEquiv P T b.hom ≫
      (R.map b.inv ≫ R.map (L.map α) ≫ inv (a.unit.app Q)) = α := by
  rw [Adjunction.homEquiv_apply, Category.assoc, ← Functor.map_comp_assoc, b.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  change a.unit.app P ≫ (L ⋙ R).map α ≫ inv (a.unit.app Q) = α
  rw [← a.unit.naturality_assoc]
  simp

private theorem coefficient_factorization
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] (M : ModuleCat.{u + 1} A)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (hF : IsZero ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).obj F))
    (α : (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶ F) :
    ∃! t : (supportedCoefficients A i).obj M ⟶ F,
      supportedCoefficientQuotient A i M ≫ t = α := by
  let C := ModuleCat.{u + 1} A
  let a := upperStarLowerStarAdjunction C i
  let b := constantSheafCompUpperStarIso C i
  have : IsIso (a.unit.app F) :=
    isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i i.openComplement.ι
      (by rw [i.range_eq_compl_range_openComplement_ι]; exact isCompl_compl.symm) F hF
  let t : (supportedCoefficients A i).obj M ⟶ F :=
    (lowerStar C i).map (b.inv.app M) ≫
      (lowerStar C i).map ((upperStar C i).map α) ≫ inv (a.unit.app F)
  have ht : supportedCoefficientQuotient A i M ≫ t = α := by
    exact adjunction_factorization_equation a (b.app M) α
  have := coefficientQuotient_epi A i M
  exact ⟨t, ht, fun t' ht' ↦ (cancel_epi (supportedCoefficientQuotient A i M)).1
    (ht'.trans ht.symm)⟩

end CoefficientTensorProof

/-- The supported coefficient tensor comparison is uniquely fixed by the quotient
of constant sections. -/
theorem exists_unique_supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] (M N :
      ModuleCat.{u + 1} A) :
    ∃! t : (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).obj (M ⊗ N) ⟶
        ((supportedSheafTensor A (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).obj M)).obj
          ((supportedSecondCoefficients A f g j).obj N),
      supportedCoefficientQuotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N) ≫ t =
        constantExteriorTensor A f g M N ≫
          supportedSheafTensorMapGeneric (ModuleCat.{u + 1} A) (pullback f g)
            ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).map
              (supportedCoefficientQuotient A i M))
            ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).map
              (supportedCoefficientQuotient A j N)) := by
  have hc : (Etale.supportedProductImmersion f g i j).openComplement =
      pullback.fst f g ⁻¹ᵁ i.openComplement ⊔ pullback.snd f g ⁻¹ᵁ j.openComplement := by
    apply TopologicalSpace.Opens.ext
    simp [Scheme.Hom.coe_openComplement, Etale.supportedProductImmersion,
      Scheme.Pullback.range_map, Set.compl_inter, Set.preimage_compl]
  exact coefficient_factorization A (Etale.supportedProductImmersion f g i j) (M ⊗ N) _
    (tensor_zero_on_union A (pullback.fst f g) (pullback.snd f g) i j _ hc M N) _

/-- The uniquely normalized supported coefficient tensor comparison. -/
noncomputable def supportedCoefficientTensor
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] (M N :
      ModuleCat.{u + 1} A) :=
  (exists_unique_supportedCoefficientTensor A f g i j M N).choose

private theorem constantTensor_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    {M M' N N' : ModuleCat.{u + 1} A} (a : M ⟶ M') (b : N ⟶ N') :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map (a ⊗ₘ b) ≫
        supportedConstantTensor A X M' N' =
      supportedConstantTensor A X M N ≫
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map a ⊗ₘ
          (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map b) := by
  exact (Functor.OplaxMonoidal.δ_natural
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) a b).symm

private noncomputable def coefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] [Finite A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⟶
      supportedCoefficients A i where
  app := supportedCoefficientQuotient A i
  naturality _ _ f := coefficientQuotient_naturality A i f

private noncomputable def firstCoefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) [IsClosedImmersion i] :
    constantSheaf (Scheme.ProEt.topology (pullback f g)) (ModuleCat.{u + 1} A) ⟶
      supportedFirstCoefficients A f g i :=
  (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv ≫
    Functor.whiskerRight (coefficientQuotientNat A i)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))

private noncomputable def secondCoefficientQuotientNat
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (j : W ⟶ Y) [IsClosedImmersion j] :
    constantSheaf (Scheme.ProEt.topology (pullback f g)) (ModuleCat.{u + 1} A) ⟶
      supportedSecondCoefficients A f g j :=
  (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv ≫
    Functor.whiskerRight (coefficientQuotientNat A j)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))

private theorem coefficientTensor_spec
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (M N : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N) ≫
        supportedCoefficientTensor A f g i j M N =
      supportedConstantTensor A (pullback f g) M N ≫
        ((firstCoefficientQuotientNat A f g i).app M ⊗ₘ
          (secondCoefficientQuotientNat A f g j).app N) := by
  have h := (exists_unique_supportedCoefficientTensor A f g i j M N).choose_spec.1
  change supportedCoefficientQuotient A (Etale.supportedProductImmersion f g i j) (M ⊗ N) ≫
    supportedCoefficientTensor A f g i j M N = _ at h
  rw [h]
  change (_ ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _ ≫ ((_ ≫ _) ⊗ₘ (_ ≫ _))
  rw [Category.assoc, tensorHom_comp_tensorHom]
  rfl

private theorem coefficientTensor_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    {M M' N N' : ModuleCat.{u + 1} A} (a : M ⟶ M') (b : N ⟶ N') :
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).map (a ⊗ₘ b) ≫
        supportedCoefficientTensor A f g i j M' N' =
      supportedCoefficientTensor A f g i j M N ≫
        ((supportedFirstCoefficients A f g i).map a ⊗ₘ
          (supportedSecondCoefficients A f g j).map b) := by
  have := coefficientQuotient_epi A (Etale.supportedProductImmersion f g i j) (M ⊗ N)
  apply (cancel_epi (supportedCoefficientQuotient A
    (Etale.supportedProductImmersion f g i j) (M ⊗ N))).1
  rw [← Category.assoc, ← coefficientQuotient_naturality, Category.assoc,
    coefficientTensor_spec, ← Category.assoc, constantTensor_natural, Category.assoc,
    tensorHom_comp_tensorHom, (firstCoefficientQuotientNat A f g i).naturality,
    (secondCoefficientQuotientNat A f g j).naturality, ← tensorHom_comp_tensorHom,
    ← Category.assoc, ← coefficientTensor_spec, Category.assoc]

/-- The natural bifunctor comparison for closed supported coefficients. -/
private noncomputable def coefficientTensorNatTrans
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    (Functor.postcompose₂.obj
      (supportedCoefficients A (Etale.supportedProductImmersion f g i j))).obj
        (curriedTensor (ModuleCat.{u + 1} A)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (supportedFirstCoefficients A f g i)).obj
        (supportedSecondCoefficients A f g j)).obj
          (supportedSheafTensor A (pullback f g)) where
  app M :=
    { app N := supportedCoefficientTensor A f g i j M N
      naturality N N' b := by
        change (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).map (M ◁ b) ≫
          supportedCoefficientTensor A f g i j M N' =
            supportedCoefficientTensor A f g i j M N ≫
              ((supportedFirstCoefficients A f g i).obj M ◁
                (supportedSecondCoefficients A f g j).map b)
        simpa only [CategoryTheory.Functor.map_id, id_tensorHom] using
          coefficientTensor_natural A f g i j (𝟙 M) b }
  naturality M M' a := by
    apply NatTrans.ext
    funext N
    change (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).map (a ▷ N) ≫
      supportedCoefficientTensor A f g i j M' N =
        supportedCoefficientTensor A f g i j M N ≫
          ((supportedFirstCoefficients A f g i).map a ▷
            (supportedSecondCoefficients A f g j).obj N)
    simpa only [CategoryTheory.Functor.map_id, tensorHom_id] using
      coefficientTensor_natural A f g i j a (𝟙 N)

/-- The morphism type for the signed complex coefficient comparison. -/
noncomputable def supportedCoefficientTensorComplexHom
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) : Type (u + 1) :=
  SupportedTensorDerivation.ComplexHom
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j) P Q

/-- The complete normalization of the signed complex coefficient comparison. -/
noncomputable def supportedCoefficientTensorComplexCondition
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (t : supportedCoefficientTensorComplexHom A f g i j P Q) : Prop :=
  SupportedTensorDerivation.ComplexCondition
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensor A f g i j) P Q t

/-- Totalization of the supported coefficient tensor map, characterized on every
bidegree summand, with the usual cochain signs. -/
theorem exists_unique_supportedCoefficientTensorComplex
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    ∃! t : supportedCoefficientTensorComplexHom A f g i j P Q,
      supportedCoefficientTensorComplexCondition A f g i j P Q t := by
  let G := supportedCoefficients A (Etale.supportedProductImmersion f g i j)
  have : G.IsLeftAdjoint :=
    (supportedCoefficientAdjunction A (Etale.supportedProductImmersion f g i j)).isLeftAdjoint
  exact SupportedTensorDerivation.exists_unique_complex G (supportedFirstCoefficients A f g i)
    (supportedSecondCoefficients A f g j) (coefficientTensorNatTrans A f g i j) P Q

/-- The signed total complex coefficient map, selected by its summand characterization. -/
noncomputable def supportedCoefficientTensorComplex
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    supportedCoefficientTensorComplexHom A f g i j P Q :=
  (exists_unique_supportedCoefficientTensorComplex A f g i j P Q).choose

/-- Tensor morphisms through the existing derived bifunctor at a variable scheme. -/
noncomputable def supportedDerivedTensorMap (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').obj N' :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).map a).app N ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj M').map b

/-- The morphism type for the signed derived coefficient comparison. -/
noncomputable def supportedCoefficientTensorDerivedHom
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    Type (u + 2) :=
  SupportedTensorDerivation.ComparisonHom
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)

/-- The complete normalization of the signed derived coefficient comparison. -/
noncomputable def supportedCoefficientTensorDerivedCondition
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (t : supportedCoefficientTensorDerivedHom A f g i j) : Prop :=
  SupportedTensorDerivation.ComparisonFamilyCondition
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (supportedCoefficientTensorComplex A f g i j) t

private theorem coefficients_preserveFlat
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    (supportedCoefficients A i).PreservesFlat := by
  constructor
  intro M hM
  exact lowerStar_preserves_flat_closed A i _
    (GrothendieckTopology.flat_presheafToSheaf_obj
      (ModuleCat.{u + 1} A) (Scheme.ProEt.topology Z) _ (fun _ ↦ hM))

/-- The supported coefficient functor is a left adjoint by its normalized adjunction. -/
theorem supportedCoefficients_isLeftAdjoint
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X] :
    (supportedCoefficients A i).IsLeftAdjoint :=
  (supportedCoefficientAdjunction A i).isLeftAdjoint

attribute [local instance] supportedCoefficients_isLeftAdjoint

private theorem coefficientTensorComplex_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (P Q : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    supportedCoefficientTensorComplex A f g i j P Q =
      SupportedTensorDerivation.ComplexComparison
        (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
        (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
        (coefficientTensorNatTrans A f g i j) P Q := by
  apply ((exists_unique_supportedCoefficientTensorComplex A f g i j P Q).choose_spec.2 _ ?_).symm
  exact SupportedTensorDerivation.complex_comparison_spec
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (coefficientTensorNatTrans A f g i j) P Q

/-- The coefficient comparison after localization, with its full complex-model
normalization and naturality, rather than an unspecified isomorphism. -/
theorem exists_unique_supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    ∃! t : supportedCoefficientTensorDerivedHom A f g i j,
      supportedCoefficientTensorDerivedCondition A f g i j t := by
  have : (supportedCoefficients A j).PreservesFlat := coefficients_preserveFlat A j
  have : (supportedCoefficients A j).IsLeftAdjoint :=
    (supportedCoefficientAdjunction A j).isLeftAdjoint
  have : (supportedSecondCoefficients A f g j).IsLeftAdjoint :=
    inferInstanceAs ((supportedCoefficients A j) ⋙
      upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).IsLeftAdjoint
  have : (supportedSecondCoefficients A f g j).PreservesFlat :=
    ⟨fun h ↦ Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A)
      (pullback.snd f g)) (Functor.PreservesFlat.flat_obj h)⟩
  let G := supportedCoefficients A (Etale.supportedProductImmersion f g i j)
  have : G.IsLeftAdjoint :=
    (supportedCoefficientAdjunction A (Etale.supportedProductImmersion f g i j)).isLeftAdjoint
  have hθ : supportedCoefficientTensorComplex A f g i j =
      SupportedTensorDerivation.ComplexComparison G
        (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
        (coefficientTensorNatTrans A f g i j) := by
    funext P Q
    exact coefficientTensorComplex_eq A f g i j P Q
  change ∃! t : SupportedTensorDerivation.ComparisonHom G
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j),
    SupportedTensorDerivation.ComparisonFamilyCondition G
      (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
      (supportedCoefficientTensorComplex A f g i j) t
  rw [hθ]
  exact SupportedTensorDerivation.exists_unique_comparison G
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (SupportedTensorDerivation.ComplexNatTrans G
      (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
      (coefficientTensorNatTrans A f g i j))

/-- Reexpress the comparison family with the original pro-etale tensor presentation. -/
theorem supportedCoefficientTensorDerivedHom_tensor
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)] :
    supportedCoefficientTensorDerivedHom A f g i j =
    ∀ M N : DerivedCategory (ModuleCat.{u + 1} A),
      (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) := by
  exact SupportedTensorDerivation.comparisonHom_tensor
    (supportedCoefficients A (Etale.supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (supportedTensorHom_eq A (pullback f g))

/-- The derived coefficient comparison with its uniquely specified model normalization. -/
noncomputable def supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] [Finite A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian (pullback f g)]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
      (supportedCoefficients A (Etale.supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) :=
  (cast (supportedCoefficientTensorDerivedHom_tensor A f g i j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose) M N

end AlgebraicGeometry.ProEtale
