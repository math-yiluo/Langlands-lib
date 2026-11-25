/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Finite native models and relative lissity -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Finite native models detect relative finite lissity, for any coefficient isomorphism.

Source: Stacks Project, Modules on Sites, Tags 03CY and 093U; finite constant coefficient
transport in Cohomology on Sites, Tag 094I.
(blueprint: lem-weil-pbc-finite-native-relative-lisse)

Proof: scalar extension along the supplied coefficient isomorphism is naturally
isomorphic to restriction along its inverse, by uniqueness of left adjoints. Its
underlying sheaf of sets therefore agrees with the underlying sheaf of the canonical
fixed-scalar encoding of the inverse image. Forget the native local module models to
finite set models. Finite coefficient rigidity refines these models so that addition
and the finitely many scalar operations are constant, hence gives finite constant
module models. The proved relative/fixed comparison transfers them to relative
constant models. The argument allows empty covering members and the zero ring. -/
theorem finite_native_models_relative_lisse {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules X (adicLisseConstantRing X B))
    (c : (adicTowerInverseImage g).obj (adicLisseConstantRing X B) ≅
      adicLisseConstantRing Y B)
    (h : ∃ T : Sieve (⊤_ Y.ProEt), T ∈ ProEt.topology Y (⊤_ Y.ProEt) ∧
      ∀ (U : Y.ProEt) (f : U ⟶ ⊤_ Y.ProEt), T f →
        ∃ V : ModuleCat.{u + 1} B, Finite V ∧
          Nonempty (((proEtaleRingModulePullback g (adicLisseConstantRing X B)
            (adicLisseConstantRing Y B) c).obj F).over U ≅
            ((adicLisseConstantModules Y B).obj V).over U)) :
    IsRelativelyFiniteLisseModule g B
      ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj F) := by
  let P := (proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj F
  let G := (CoefficientSerre.relativeRestriction g B).obj P
  let E := proEtaleScalarEquivalence Y ((adicLisseForget Y).mapIso c)
  let j := (proEtaleRingExtensionAdjunction g (adicLisseConstantRing X B)
    (adicLisseConstantRing Y B) c).leftAdjointUniq E.symm.toAdjunction
  let e : (sheafCompose (ProEt.topology Y)
      (CategoryTheory.forget (ModuleCat.{u + 1} B))).obj G ≅
      (underlying Y (adicLisseConstantRing Y B)).obj
        ((proEtaleRingModulePullback g (adicLisseConstantRing X B)
          (adicLisseConstantRing Y B) c).obj F) :=
    ((underlying Y (adicLisseConstantRing Y B)).mapIso (j.app P)).symm
  apply (CoefficientSerre.relative_finite_iff g B P).mpr
  obtain ⟨T, hT, ht⟩ := h
  apply finite_lisse_of_underlying_models Y B G T hT
  intro U f hf
  obtain ⟨V, hV, ⟨k⟩⟩ := ht U f hf
  let L := SheafOfModules.toSheaf ((adicLisseRing Y B).over U) ⋙
    sheafCompose ((ProEt.topology Y).over U)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  exact ⟨V, hV, ⟨((ProEt.topology Y).overPullback (Type (u + 1)) U).mapIso e ≪≫
    L.mapIso k ≪≫
    ((ProEt.topology Y).overPullback (Type (u + 1)) U).mapIso
      (constantUnderlying Y B V) ≪≫
    ((ProEt.topology Y).overPullbackConstantSheafIso (Type (u + 1)) U).app V⟩⟩

end AlgebraicGeometry.Scheme
