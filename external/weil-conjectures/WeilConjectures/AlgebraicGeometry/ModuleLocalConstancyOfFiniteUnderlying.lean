/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.FiniteOperationLocalConstancy
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Local constancy of module operations on finite locally constant sets

Source: Stacks Project, Tags 0DV5 and 093S (1).
(blueprint: lem-pod-module-local-constancy-of-finite-underlying)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module sheaf whose underlying sets are finite locally constant is locally constant
as a module sheaf. This conclusion does not assert finiteness of its constant models.
Source: Stacks Project, Tag 0DV5, proof of (2)--(3), using Tag 093S (1).
(blueprint: lem-pod-module-local-constancy-of-finite-underlying)

Proof: first trivialize the underlying sheaf on an etale cover. Its constant values may
be taken finite: on a nonempty covering member evaluate at a geometric point, where the
constant value is its finite stalk; on an empty member use the singleton. Addition has
finite constant source, and zero and negation do too. For each scalar of the finite ring
scalar multiplication also has finite constant source. By 093S (1), refine each member
so each of these finitely many maps is induced by a map of constant finite sets. A common
refinement exists because there are finitely many maps. Exclude empty members when
checking the module laws. On each nonempty member the constant-sheaf functor is faithful:
evaluation at a geometric point recovers the constant set and its maps. The diagram equalities
of the
original module sheaf therefore give the module laws on each constant value. The set
trivialization respects all the operations and hence lifts to an isomorphism of module
sheaves. Empty members have the unique sheaf and can instead be trivialized by the zero
module. Compose the refinements with the original covering; this is the required datum.
This argument applies to noncommutative rings with left scalar multiplication. -/
theorem module_localConstancy_of_finite_underlying
    {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteLocallyConstantSheafOfTypes
      ((sheafForget Y.smallEtaleTopology).obj F)) :
    IsLocallyConstantSheaf F := by
  rcases hF.1 with ⟨𝒰, h𝒰⟩
  exact module_operationCompatibleCover F _ rfl (fun Ω _ _ s ↦ hF.finite_sheafFiber Ω s)
    𝒰 h𝒰

end AlgebraicGeometry.Scheme
