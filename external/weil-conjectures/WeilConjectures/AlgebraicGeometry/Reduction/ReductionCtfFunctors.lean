/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers

/-!
# Constructible restrictions of the finite-coefficient operations

The compact-support and scalar-extension restrictions retain their existing names and
bodies. Separating these two constructions from the exceptional realization and its
chart data lets the mixed base-change statement use just the restriction interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The actual compact-support functor restricted to its full Dctf subcategories.
The witness only certifies membership and changes neither objects nor morphisms. -/
def reductionCtfCompactSupport (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y)
    (hF : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj)) :=
  (spFiniteConstructibleTor Y A).lift
    ((spFiniteConstructibleTor X A).ι ⋙ reductionCompactSupport A j p) hF

/-- Restrict the recorded scalar extension to full Dctf subcategories. -/
def reductionCtfScalar {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (hT : ∀ K : spFiniteConstructibleTorCategory T A,
      spFiniteConstructibleTor T B ((scalarExtensionFunctor φ T).obj K.obj)) :=
  (spFiniteConstructibleTor T B).lift
    ((spFiniteConstructibleTor T A).ι ⋙ scalarExtensionFunctor φ T) hT

end AlgebraicGeometry.ProEtale
