/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreePerfectCore
import WeilConjectures.AlgebraicGeometry.AffineFiniteFreePerfectComparison

/-!
# Local strictly perfect models from bounded finite free resolutions

Source: Stacks Project, Tag 068C, finite free resolution argument, and Tags 08C4, 08CM
(blueprint: lem-sc-affine-finite-free-resolution-perfect-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A bounded finite free algebraic chain complex resolving a sheaf on an affine
open supplies a strictly perfect model for its derived restriction to that open.
Source: Stacks Project, Tag 068C, and Definitions 08C4, 08CM
(blueprint: lem-sc-affine-finite-free-resolution-perfect-model).

Proof: Extend `K` by zero from degree `n` to cohomological degree `-n`. Its terms
vanish outside `[-r,0]`. Choose a finite basis in each algebraic term; sheafifying
its basis isomorphism identifies the term with a finite direct sum of the unit
sheaf. Transport along the affine chart and then along `Scheme.Modules.overEquiv U`
to the localized site used in `IsStrictlyPerfect`. The transported basis maps give
inverse maps to the finite free sheaf indexed by `ULift (Fin m)`; outside the bound
use rank zero. Thus the transported cochain complex is strictly perfect.
Extend the given quasi-isomorphism `q` by zero as well; its homology is unchanged
in degrees `-n` and zero in the other degrees. The localized-site equivalence
preserves homology. Invert this quasi-isomorphism in the derived category and
compose with the natural restriction-single comparison. That comparison identifies
restriction via `SheafOfModules.overFunctor` with restriction to `U.toScheme`
followed by the localized-site equivalence, and commutes with the degree-zero
single functor. The resulting derived isomorphism has precisely the asserted
source and target. This argument works for the zero ring, rank zero, and `r = 0`. -/
theorem exists_affine_finite_free_perfect_model {Y : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (K : ChainComplex (ModuleCat.{u} (Γ(Y, U) : Type u)) ℕ) (r : ℕ)
    (hfree : ∀ n, Module.Free (Γ(Y, U) : Type u) (K.X n))
    (hfinite : ∀ n, Module.Finite (Γ(Y, U) : Type u) (K.X n))
    (hzero : ∀ n, r < n → IsZero (K.X n))
    (q : ((tilde.functor Γ(Y, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K ⟶
        (ChainComplex.single₀ U.toScheme.Modules).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj M))
    [QuasiIso q] :
    ∃ L : CochainComplex
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ,
      Scheme.IsStrictlyPerfect Y U L ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≅
              DerivedCategory.Q.obj L) := by
  refine ⟨affineFiniteFreeModelComplex U hU K, ?_, ?_⟩
  · exact affine_finite_free_perfect_core U hU K r hfree hfinite hzero
  · exact affine_finite_free_perfect_comparison U hU M K q

end AlgebraicGeometry
