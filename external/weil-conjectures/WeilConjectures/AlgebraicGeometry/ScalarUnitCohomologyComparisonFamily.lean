/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # The explicit module-to-abelian comparison for unit coefficients

Source: Stacks Project, Tag 03FD.
(blueprint: new-sc-scalar-unit-comparison-family).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules

/-- Forget a module Ext class and precompose with the constant-integer class of the
unit section. The source is the underlying additive group of restricted-scalar cohomology;
thus this construction is independent of the structure morphism to the field.
Source: Stacks Project, Tag 03FD, and the constant-sheaf adjunction.
(blueprint: new-sc-scalar-unit-comparison-family). -/
noncomputable def scalarUnitAbelianComparison (X : Scheme.{u}) :
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (SheafOfModules.unit X.ringCatSheaf)) →+ Sheaf.H (structureSheafAb X) 1 := by
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hasExt_of_enoughInjectives _
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  let s : Sheaf.H (T.obj (SheafOfModules.unit X.ringCatSheaf)) 0 :=
    (Sheaf.H.equiv₀ _ isTerminalTop).symm (1 : Γ(X, ⊤))
  exact (s.precomp _ (zero_add 1)).comp
    ((T.mapExtAddHom _ _ 1).comp
      (moduleExtEquiv (SheafOfModules.unit X.ringCatSheaf) 1).toAddMonoidHom)

-- Degree one needs only an injective embedding and the two Ext exact sequences.
private noncomputable def unitExtComparison (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (F : SheafOfModules.{u} X.ringCatSheaf) (n : ℕ) :
    Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F n →+
      Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) n := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  let s : Sheaf.H (T.obj (SheafOfModules.unit X.ringCatSheaf)) 0 :=
    (Sheaf.H.equiv₀ _ isTerminalTop).symm (1 : Γ(X, ⊤))
  exact (s.precomp (T.obj F) (zero_add n)).comp (T.mapExtAddHom _ F n)

private theorem unitEvaluation_bijective (X : Scheme.{u})
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    Function.Bijective (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ F ↦
      f.val.app (op ⊤) (1 : Γ(X, ⊤))) := by
  have heval : Function.Bijective (fun s : F.sections ↦ s.val (op ⊤)) := by
    constructor
    · intro s t h
      apply PresheafOfModules.sections_ext
      intro U
      have hs := s.property (homOfLE (le_top (a := U.unop))).op
      have ht := t.property (homOfLE (le_top (a := U.unop))).op
      exact hs.symm.trans ((congrArg (fun z ↦ F.val.map
        (homOfLE (le_top (a := U.unop))).op z) h).trans ht)
    · intro x
      refine ⟨PresheafOfModules.sectionsMk
        (fun U ↦ F.val.map (homOfLE (le_top (a := U.unop))).op x) ?_, ?_⟩
      · intro U V f
        change F.val.presheaf.map f (F.val.presheaf.map
          (homOfLE (le_top (a := U.unop))).op x) = _
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      · change F.val.map (𝟙 (op ⊤)) x = x
        simp
  exact heval.comp F.unitHomEquiv.bijective

private theorem unitExtComparison_zero_bijective (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    Function.Bijective (unitExtComparison X F 0) := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  have h (f : SheafOfModules.unit X.ringCatSheaf ⟶ F) :
      (Sheaf.H.equiv₀ (T.obj F) isTerminalTop)
        (unitExtComparison X F 0 (Abelian.Ext.mk₀ f)) =
      f.val.app (op ⊤) (1 : Γ(X, ⊤)) := by
    change (Sheaf.H.equiv₀ (T.obj F) isTerminalTop)
      (((Sheaf.H.equiv₀ _ isTerminalTop).symm (1 : Γ(X, ⊤))).comp
        ((Abelian.Ext.mk₀ f).mapExactFunctor T) (zero_add 0)) = _
    rw [Abelian.Ext.mapExactFunctor_mk₀]
    change (Sheaf.H.equiv₀ (T.obj F) isTerminalTop)
      (Sheaf.H.map (T.map f) 0 _) = _
    rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
    rfl
  have hb : Function.Bijective (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ F ↦
      (Sheaf.H.equiv₀ (T.obj F) isTerminalTop)
        (unitExtComparison X F 0 (Abelian.Ext.mk₀ f))) := by
    simpa only [h] using unitEvaluation_bijective X F
  have hb' : Function.Bijective (fun x ↦
      (Sheaf.H.equiv₀ (T.obj F) isTerminalTop) (unitExtComparison X F 0 x)) :=
    ((Abelian.Ext.mk₀_bijective _ F).of_comp_iff _).mp hb
  exact ((Sheaf.H.equiv₀ (T.obj F) isTerminalTop).bijective.of_comp_iff' _).mp hb'

private theorem unitExtComparison_comp (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    {F G : SheafOfModules.{u} X.ringCatSheaf} {a b c : ℕ}
    (x : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) F a)
    (y : Abelian.Ext.{u} F G b) (h : a + b = c) :
    unitExtComparison X G c (x.comp y h) =
      (unitExtComparison X F a x).comp
        (y.mapExactFunctor (SheafOfModules.toSheaf X.ringCatSheaf)) h := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  change _ = _
  dsimp only [unitExtComparison, AddMonoidHom.comp_apply]
  rw [Functor.mapExtAddHom_apply, Functor.mapExtAddHom_apply,
    Abelian.Ext.mapExactFunctor_comp]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add a) h (by omega)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem forgottenInjective_H_one_subsingleton (X : Scheme.{u})
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] :
    Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) 1) := by
  let (U : Opens X) : Unique (U ⟶ (⊤ : Opens X)) :=
    ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let e : yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents (fun U ↦
      ((FreeAbelianGroup.uniqueEquiv (U.unop ⟶ (⊤ : Opens X))).trans
        AddEquiv.ulift.symm).toAddCommGrpIso) (by
      intro U V f
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro g
      change ULift.up (FreeAbelianGroup.uniqueEquiv _
        (FreeAbelianGroup.map (fun h ↦ f.unop ≫ h) (FreeAbelianGroup.of g))) =
        ULift.up (FreeAbelianGroup.uniqueEquiv _ (FreeAbelianGroup.of g))
      simp [FreeAbelianGroup.uniqueEquiv])
  let e' := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapIso e
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : Subsingleton (Sheaf.H' (T.obj I) 1 ⊤) :=
    injective_module_abelian_acyclic ⊤ I 1 (by omega)
  have hI : Subsingleton (Abelian.Ext.{u}
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)) (T.obj I) 1) := by
    exact inferInstanceAs (Subsingleton (Sheaf.H' (T.obj I) 1 ⊤))
  exact @Function.Injective.subsingleton _ _
    (Abelian.Ext.precompAddEquiv e' (T.obj I) 1)
    (Abelian.Ext.precompAddEquiv e' (T.obj I) 1).injective hI

set_option backward.isDefEq.respectTransparency false in
private theorem unitExtComparison_one_bijective (X : Scheme.{u})
    [EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf)]
    [HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf)]
    (F : SheafOfModules.{u} X.ringCatSheaf) :
    Function.Bijective (unitExtComparison X F 1) := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hT := hS.map_of_exact T
  -- Exact forgetting preserves the extension class, so the boundary square commutes.
  have hδ (x : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₃ 0) :
      unitExtComparison X S.X₁ 1 (x.comp hS.extClass (zero_add 1)) =
        (unitExtComparison X S.X₃ 0 x).comp hT.extClass (zero_add 1) := by
    rw [unitExtComparison_comp, Abelian.Ext.mapExactFunctor_extClass]
  have hg (x : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf) S.X₂ 0) :
      unitExtComparison X S.X₃ 0 (x.comp (Abelian.Ext.mk₀ S.g) (add_zero 0)) =
        (unitExtComparison X S.X₂ 0 x).comp (Abelian.Ext.mk₀ (T.map S.g))
          (add_zero 0) := by
    rw [unitExtComparison_comp, Abelian.Ext.mapExactFunctor_mk₀]
  -- Lift a kernel class through the boundary, then lift its degree-zero representative.
  have hinj : Function.Injective (unitExtComparison X F 1) := by
    rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x
      (Abelian.Ext.eq_zero_of_injective _) (zero_add 1)
    have hy0 : (unitExtComparison X S.X₃ 0 y).comp hT.extClass (zero_add 1) = 0 := by
      rw [← hδ, hy]
      exact hx
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1) hy0
    obtain ⟨w, hw⟩ := (unitExtComparison_zero_bijective X S.X₂).surjective z
    have hwy : w.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = y :=
      (unitExtComparison_zero_bijective X S.X₃).injective (by rw [hg, hw]; exact hz)
    rw [← hy, ← hwy, Abelian.Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Abelian.Ext.comp_zero]
  -- Vanishing on the forgotten injective makes the abelian boundary surjective.
  refine ⟨hinj, ?_⟩
  intro x
  let : Subsingleton (Sheaf.H (T.obj S.X₂) 1) :=
    forgottenInjective_H_one_subsingleton X S.X₂
  obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hT x
    (show x.comp (Abelian.Ext.mk₀ (T.map S.f)) (add_zero 1) = 0 from
      Subsingleton.elim _ _) (zero_add 1)
  obtain ⟨z, hz⟩ := (unitExtComparison_zero_bijective X S.X₃).surjective y
  refine ⟨z.comp hS.extClass (zero_add 1), ?_⟩
  rw [hδ, hz, hy]

/-- The explicit comparison is bijective; no assertion about pullbacks is made here.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-sc-scalar-unit-comparison-family).

Proof: Resolve the unit module by injective module sheaves. Forgetting to abelian sheaves
is exact and the forgotten injectives are acyclic for sections by Tag 03FD. Consequently
both derived sections groups are computed by the same underlying additive sections complex.
The module Ext comparison evaluates a morphism from the unit at its section 1, as specified
by exists_moduleExtEquiv. After forgetting modules, precomposition with the integer-unit
class does exactly the same evaluation: the constant-sheaf adjunction sends that class to 1.
Thus scalarUnitAbelianComparison is the common-resolution comparison on degree-one homology,
which is an isomorphism. This also handles the empty scheme, whose sections complex is zero;
no nonemptiness or finiteness assumption is used. -/
theorem scalar_unit_abelian_comparison_bijective (X : Scheme.{u}) :
    Function.Bijective (scalarUnitAbelianComparison X) := by
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hasExt_of_enoughInjectives _
  exact (unitExtComparison_one_bijective X (SheafOfModules.unit X.ringCatSheaf)).comp
    (moduleExtEquiv (SheafOfModules.unit X.ringCatSheaf) 1).bijective

end AlgebraicGeometry.Scheme
