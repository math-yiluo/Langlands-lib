/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericLatticeExtension
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealSigma

/-! Generic coherent ideal lattices. Source: Stacks Project, Tag 01YE. -/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The lattice construction before proving injectivity.

Source: Stacks Project, Tag 01YE, first two paragraphs of the integral-case proof.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map-construction).

Extend a finite generic basis to an open neighbourhood. Extend that specific map
from a coherent ideal lattice of the same rank. Its finite coproduct is coherent
by the finite local generator argument, giving all the required witnesses. -/
theorem coherent_integral_generic_ideal_construction (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules) ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G),
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ) := by
  obtain ⟨r, U, hx, φ, hφ⟩ := exists_generic_free_neighbourhood Z G hG
  obtain ⟨I, hI, χ, hχ⟩ := exists_generic_ideal_extension Z G hG r U hx φ hφ
  exact ⟨r, I, hI, coherent_sigma_of_coherent_ideal Z r I hI, χ, hχ⟩

end AlgebraicGeometry.Scheme.Modules
