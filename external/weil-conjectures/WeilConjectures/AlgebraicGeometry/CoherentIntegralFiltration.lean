/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # The finite coherent integral-ideal filtration predicate

Source: Stacks Project, Cohomology of Schemes, Lemma 01YF.
(blueprint: def-weil-pbc-coherent-integral-filtration)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The exact finite-subobject-chain conclusion of Stacks Lemma 01YF.
This is a predicate on an existing module, with cokernels as successive quotients;
no filtration or ideal is chosen.
Source: Stacks Project, Cohomology of Schemes, Lemma 01YF, statement.
(blueprint: def-weil-pbc-coherent-integral-filtration) -/
def HasCoherentIntegralFiltration {X : Scheme.{u}} (F : X.Modules) : Prop :=
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      (∀ k : Fin (m + 1), RingedSpace.IsCoherent X.toRingedSpace (c k : X.Modules)) ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          I ≠ ⊥ ∧ RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
          Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules)
end AlgebraicGeometry.Scheme.Modules
