/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroStalkIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroCompatibility

/-! # Degree-zero identifications for the formal fibre system

Source: Stacks Project, Cohomology of Schemes, Lemma 02OD, degree-zero specialization,
and Cohomology, Tags 01E4 and 01FB
(blueprint: lem-weil-pbc-formal-functions-degree-zero-dictionary).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Degree-zero derived stalks are ordinary direct-image stalks, and the degree-zero
cohomology system of the pulled-back unit module is the system of global sections.
The identifications carry the canonical stalk maps to section pullback on germs.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OD (degree zero); Cohomology,
Tags 01E4 and 01FB
(blueprint: lem-weil-pbc-formal-functions-degree-zero-dictionary).

Proof: Direct image and global sections are left exact additive functors. Their
augmentation maps to the zeroth right derived functors are natural isomorphisms:
for an injective resolution, degree-zero cycles are the kernel of the first
resolution differential, namely the original module. Take stalks of the direct-image
isomorphism to obtain a. Tensor pullback of the unit module is the unit module:
on sections the identification sends r tensor s to r times the pullback of s;
the inverse sends r to r tensor 1. Compose this identification with H^0 = Gamma
on each infinitesimal fibre. These maps are linear over the quotient of the local
ring and thus over its completion. Naturality for the transition h-maps gives b.
For a germ of t over V, the resolution augmentation represents t as a degree-zero
cycle. The defining predicate IsFormalFunctionsTheta sends this cycle to the
pullback cycle on the inverse image of f^{-1}V. The displayed containment makes
this inverse image the whole fibre; restriction to it is invertible. Under H^0 =
Gamma and the tensor-unit identification, the cycle is precisely appLE(t).
This proves the germ formula, with no properness or Noetherian hypotheses. -/
theorem formalFunctions_degreeZero_dictionary {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0,
      ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by
  obtain ⟨a, _, b, hb⟩ := formalFunctions_degreeZero_compatibility f y
  exact ⟨a, b, hb⟩

end AlgebraicGeometry
