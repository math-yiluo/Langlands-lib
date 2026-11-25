/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Stalk criterion for scalar restriction on an open site

Source: Stacks Project, Tags 05NE, 01CB, 01AG and 0098.
(blueprint: lem-pc-open-scalar-restriction-stalk-criterion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace TopCat.Presheaf Opposite
namespace AlgebraicGeometry.RingedSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Stalks in U suffice, by extension by zero and restriction. -/
private theorem flat_open (X : RingedSpace.{u}) (F : Modules X) (U : Opens X)
    (hf : ∀ x : X, x ∈ U → Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj F)) :
    SheafOfModules.IsFlat (R := X.sheaf.over U)
      ((SheafOfModules.overFunctor (moduleRings X) U).obj F) := by
  classical
  let V := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let E := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)
  let adj := Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2
  have : Limits.PreservesFiniteLimits V := (open_restriction_adjunction_exact X U).1
  have : Limits.PreservesFiniteColimits V := (open_restriction_adjunction_exact X U).2.1
  have : Limits.PreservesFiniteLimits E := (open_restriction_adjunction_exact X U).2.2.1
  have : Limits.PreservesFiniteColimits E := (open_restriction_adjunction_exact X U).2.2.2.1
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  have : E.IsLeftAdjoint := adj.isLeftAdjoint
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  let := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalCategory (SheafOfModules.{u} ((moduleRings X).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let T := MonoidalCategory.tensorRight F
  let T' := MonoidalCategory.tensorRight (V.obj F)
  let := SheafOfModules.symmetricCategory X.sheaf
  let := SheafOfModules.symmetricCategory (X.sheaf.over U)
  have : T.Additive := inferInstance
  let : MonoidalPreadditive (SheafOfModules.{u} ((moduleRings X).over U)) :=
    Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1
  have : T'.Additive := inferInstance
  obtain ⟨η, hη⟩ := SheafOfModules.exists_open_localized_tensor_natural X.sheaf U
  let d : T ⋙ V ≅ V ⋙ T' := NatIso.ofComponents (fun A ↦ η A F) (by
    intro A A' f
    simpa [T, T'] using hη A A' F F f (𝟙 F))
  have hex : ∀ C : ShortComplex (SheafOfModules.{u} ((moduleRings X).over U)),
      C.Exact → (C.map T').Exact := by
    intro C hC
    have hE : (C.map E).Exact := hC.map E
    have ht : ((C.map E).map T).Exact := by
      apply ((module_stalk_exact X (T.map (E.map C.f))).2.2.2.2 _ _ _ _).mpr
      intro x
      let S := moduleStalkFunctor X x
      obtain ⟨Φ, _, hΦ⟩ := SheafOfModules.stalkTensorIso X x
      let e : T ⋙ S ≅ S ⋙ MonoidalCategory.tensorRight (S.obj F) :=
        NatIso.ofComponents (fun A ↦ Φ A F) (by
          intro A A' f
          simpa [T, S] using hΦ A F A' F f (𝟙 F))
      have hs : (((C.map E).map S).map
          (MonoidalCategory.tensorRight (S.obj F))).Exact := by
        by_cases hx : x ∈ U
        · have : Module.Flat (X.presheaf.stalk x) (S.obj F) := hf x hx
          have he : ((C.map E).map S).Exact :=
            ((module_stalk_exact X (E.map C.f)).2.2.2.2 _ _ _ _).mp hE x
          exact Module.Flat.rTensor_shortComplex_exact (S.obj F) _ he
        · apply ShortComplex.exact_of_isZero_X₂
          exact (MonoidalCategory.tensorRight (S.obj F)).map_isZero
            (moduleExtensionByZero_stalk_outside X U C.X₂ x hx)
      exact ShortComplex.exact_of_iso ((C.map E).mapNatIso e.symm) hs
    have hv := ht.map V
    have hd : ((C.map E).map (V ⋙ T')).Exact :=
      ShortComplex.exact_of_iso ((C.map E).mapNatIso d) hv
    have hi (A : SheafOfModules.{u} ((moduleRings X).over U)) : IsIso (adj.unit.app A) :=
      moduleExtensionByZero_unit_isIso X U A
    let e : 𝟭 _ ≅ E ⋙ V := NatIso.ofComponents (fun A ↦ asIso (adj.unit.app A))
      (by intro A B f; exact adj.unit.naturality f)
    exact ShortComplex.exact_of_iso
      (C.mapNatIso (Functor.isoWhiskerRight e T').symm) hd
  have : T'.PreservesHomology := Functor.preservesHomology_of_map_exact T' hex
  change Limits.PreservesFiniteLimits T' ∧ Limits.PreservesFiniteColimits T'
  exact ⟨Functor.preservesFiniteLimits_of_preservesHomology T',
    Functor.preservesFiniteColimits_of_preservesHomology T'⟩

/-- Restricting scalars commutes with the stalk action on germs. -/
private theorem scalar_stalk_flat (X : RingedSpace.{u})
    (R : X.carrier.Sheaf CommRingCat.{u}) (φ : R ⟶ X.sheaf) (G : Modules X) (x : X)
    (h : Module.Flat ((stalkFunctor CommRingCat.{u} x).obj R.obj)
      ((ModuleCat.restrictScalars ((stalkFunctor CommRingCat.{u} x).map φ.hom).hom).obj
        ((moduleStalkFunctor X x).obj G))) :
    let Y : RingedSpace.{u} := ⟨⟨X.carrier, R.obj⟩, R.property⟩
    let β := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map φ
    Module.Flat (Y.presheaf.stalk x)
      ((moduleStalkFunctor Y x).obj ((SheafOfModules.restrictScalars β).obj G)) := by
  let Y : RingedSpace.{u} := ⟨⟨X.carrier, R.obj⟩, R.property⟩
  let β := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).map φ
  let H := (SheafOfModules.restrictScalars β).obj G
  let N := (moduleStalkFunctor Y x).obj H
  let M := (ModuleCat.restrictScalars ((stalkFunctor CommRingCat.{u} x).map φ.hom).hom).obj
    ((moduleStalkFunctor X x).obj G)
  have lin (r : Y.presheaf.stalk x) (m : N) :
      (show M from (r • m)) = r • (show M from m) := by
    obtain ⟨U, hxU, r, rfl⟩ := Y.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.val.presheaf m
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
      ← TopCat.Presheaf.germ_res_apply H.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
    generalize Y.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r = r'
    generalize H.val.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op m = m'
    let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        (moduleStalkFunctor X x).obj G |>.isModule
    change _ = (show X.presheaf.stalk x from
      ((stalkFunctor CommRingCat.{u} x).map φ.hom)
        (Y.presheaf.germ (U ⊓ V) x hx r')) •
      (show (moduleStalkFunctor X x).obj G from
        TopCat.Presheaf.germ G.val.presheaf (U ⊓ V) x hx m')
    erw [stalkFunctor_map_germ_apply]
    have hG := PresheafOfModules.germ_smul (R := X.presheaf) G.val x
      (U ⊓ V) hx ((φ.hom.app (op (U ⊓ V))) r') m'
    have hH := PresheafOfModules.germ_smul (R := Y.presheaf) H.val x (U ⊓ V) hx r' m'
    exact hH.symm.trans hG
  let e : N ≃ₗ[Y.presheaf.stalk x] M :=
    { toFun := fun m ↦ m
      invFun := fun m ↦ m
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := lin }
  change Module.Flat (Y.presheaf.stalk x) N
  have : Module.Flat (Y.presheaf.stalk x) M := h
  exact Module.Flat.of_linearEquiv e

/-- Flatness of the restricted stalks implies flatness on the localized open site.
Source: Stacks Project, Tags 05NE, 01CB, 01AG and 0098.
(blueprint: lem-pc-open-scalar-restriction-stalk-criterion).

Proof: Regard R as the structure sheaf of a ringed space Y on the same carrier.
Restricting G scalars along φ gives an R-module H with the same additive presheaf.
Represent a scalar and a module germ on a common neighborhood. The germ formula
for φ and germ_smul show the identity of additive stalks is R_x-linear, so H_x
is flat for x in U. For an exact short complex C on the localized site, apply
exact extension by zero E, then tensor with H. In U, stalk tensor comparison
and flatness give exactness. Outside U, the middle stalk of E(C) is zero, so its
tensor is zero and the stalk complex is exact. Stalk detection gives ambient
exactness. Apply exact restriction V and the natural tensor-restriction comparison.
The invertible extension/restriction unit identifies C with V(E(C)), giving
exactness of C tensor V(H). This additive tensor functor preserves homology,
hence finite limits and colimits. Finally scalar restriction and open restriction
commute sectionwise. The same argument covers U empty and G zero without any
quasi-coherence hypothesis. -/
theorem isFlat_open_scalarRestriction_of_stalks
    (X : RingedSpace.{u}) (R : X.carrier.Sheaf CommRingCat.{u})
    (φ : R ⟶ X.sheaf) (U : Opens X) (G : Modules X)
    (hflat : ∀ (x : X), x ∈ U →
      Module.Flat ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).obj R.obj)
      ((ModuleCat.restrictScalars
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map φ.hom).hom).obj
        ((moduleStalkFunctor X x).obj G))) :
    let α := ((Opens.grothendieckTopology X).overPullback CommRingCat.{u} U).map φ
    let B := (sheafCompose ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).map α
    SheafOfModules.IsFlat ((SheafOfModules.restrictScalars B).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings X) U).obj G)) := by
  let Y : RingedSpace.{u} := ⟨⟨X.carrier, R.obj⟩, R.property⟩
  let β := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).map φ
  let H := (SheafOfModules.restrictScalars β).obj G
  change SheafOfModules.IsFlat (R := Y.sheaf.over U)
    ((SheafOfModules.overFunctor.{u} (moduleRings Y) U).obj H)
  apply flat_open Y H U
  intro x hx
  exact scalar_stalk_flat X R φ G x (hflat x hx)

end AlgebraicGeometry.RingedSpace
