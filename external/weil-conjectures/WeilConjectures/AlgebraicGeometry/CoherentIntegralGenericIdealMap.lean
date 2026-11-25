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
import WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.AlgebraicGeometry.CoherentLocalIsomorphism
import WeilConjectures.AlgebraicGeometry.CoherentHomsOverOpen
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.IntegralIdealGenericStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealConstruction
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericIdealMono

/-! # An ideal-sum lattice in a coherent module on an integral scheme

Source: Stacks Project, Tag 01YE, integral case in the last paragraph of the proof.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on an integral Noetherian scheme admits a coherent ideal-sum
injection with invertible generic stalk.

Source: Stacks Project, Tag 01YE, last paragraph of the proof, including its final
injectivity assertion.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map).

Proof:
1. The generic local ring is a field. Finite type of G implies its generic stalk is
finite dimensional; choose a basis of rank r. Finite free modules are coherent. Extend
the induced free-module stalk isomorphism to a morphism over a neighbourhood U using
coherent_stalk_map_extends, shrinking U by coherent_local_isomorphism so it is invertible.
2. Give the closed complement of U its reduced induced structure and let J be its
ideal. The open complement is exactly the locus where J's stalk inclusion is surjective.
Apply coherent_homs_over_open to extend the morphism from J^n times the rank-r free
module for some n. Tensor distributes over finite sums and J^n times the structure
module is J^n, so this source is the coproduct of r copies of I = J^n. Its map χ agrees
with the free-module isomorphism on U, hence has invertible generic stalk. I and its
finite direct sum are quasi-coherent finite type, hence coherent on the Noetherian scheme.
3. The kernel of χ is coherent and has zero generic stalk by exactness. Embed it in
the rank-r free module through I's inclusion. Each coordinate image is a quasi-coherent
ideal with zero generic stalk, hence zero by integral_ideal_generic_stalk. All coordinates
of every kernel section vanish, so the kernel is zero and χ is mono. For r = 0 this
coordinate argument is vacuous and the source is the zero module; for n = 0 use the
unit ideal. No nonzero-rank assumption is needed. -/
theorem coherent_integral_generic_ideal_map (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules) ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G), Mono χ ∧
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ)
    := by
  obtain ⟨r, I, hI, hSum, χ, hχ⟩ :=
    coherent_integral_generic_ideal_construction Z G hG
  have hmono := mono_of_coherent_ideal_sum_generic_iso Z G hG r I χ hI hSum hχ
  exact ⟨r, I, hI, hSum, χ, hmono, hχ⟩

end AlgebraicGeometry.Scheme.Modules
