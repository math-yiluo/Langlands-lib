/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-! # Finite models for finite constant sheaves

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, coefficient dual argument.
(blueprint: lem-weil-pbc-finite-constant-model)
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- A constant sheaf with finite geometric stalks has a finitely generated constant model.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring.

Proof: On a nonempty scheme choose a point x and the geometric point with residue field
SeparableClosure κ(x). A constant model exists by constancy, and its geometric stalk is
that module. Transport finite generation from the stalk across this isomorphism.
On the empty scheme every sheaf is zero, so use the zero module as its constant model.
(blueprint: lem-weil-pbc-finite-constant-model) -/
theorem exists_finite_constant_model
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hc : F.IsConstant X.smallEtaleTopology) (hf : IsFiniteSheaf F) :
    ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
      Nonempty (F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  by_cases hX : IsEmpty X
  · let := hX
    refine ⟨0, ?_, ⟨(Etale.isZero_sheaf_of_isEmpty F).iso
      (Etale.isZero_sheaf_of_isEmpty _)⟩⟩
    exact (ModuleCat.isFinitelyGenerated_iff _).mp
      (ConcreteCategory.isFinitelyGenerated_of_isZero (isZero_zero _))
  · have : Nonempty X := not_isEmpty_iff.mp hX
    let x : X := Classical.choice inferInstance
    let Ω := SeparableClosure (X.residueField x)
    let s : Spec (.of Ω) ⟶ X := (SpecToEquivOfField Ω X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) Ω)⟩
    let := hc
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    obtain ⟨M, ⟨e⟩⟩ := F.mem_essImage_of_isConstant
    refine ⟨M, ?_, ⟨e.symm⟩⟩
    exact (ModuleCat.isFinitelyGenerated_iff _).mp
      ((hf.isFinitelyGenerated_sheafFiber Ω s).of_iso
        ((pointSmallEtale s).sheafFiber.mapIso e.symm ≪≫
          (pointSmallEtale s).sheafFiberConstantSheafIso M))

end AlgebraicGeometry.Scheme
