/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteConstructibilityOuterTransfer
import all WeilConjectures.AlgebraicGeometry.FiniteConstructibilityOuterTransfer

/-! Fixed-stratum scalar restriction for the finite integral coefficient triangle. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The normalized scalar restriction carries a fixed-stratum local model from either
outer finite coefficient term to the corresponding outer vertex of the triangle.
Source: blueprint latest, integral-finite-levels, first paragraph.
(blueprint: lem-pe-finite-constructibility-outer-local-transfer).

Proof: apply normalized finite scalar restriction on the specified stratum for a
consecutive coefficient transition. For the canonical residue map, induct on the number
of transitions, identifying restriction along a composite with the composite exact
derived restrictions. Finally pull the local trivializations back through the inverse
homology isomorphisms of the two displayed outer identifications. No new stratum or
refinement is chosen, and no condition on the other strata is used. -/
theorem finite_constructibility_outer_local_transfer
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ)
    (L₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X 0)))
    (Lₙ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n)))
    (Δ : CategoryTheory.Pretriangulated.Triangle
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X (n + 1)))))
    (e₀ : Δ.obj₁ ≅
      (Mod.comap (integralResidueTransition l E X (n + 1))).mapDerivedCategory.obj L₀)
    (eₙ : Δ.obj₃ ≅
      (Mod.comap (AdicCompletion.transition l E X n)).mapDerivedCategory.obj Lₙ)
    (S : Scheme.Stratification X) (i : Fin S.n) :
    (scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E 1) X S i L₀ →
      scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 2)) X S i
        Δ.obj₁) ∧
    (scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 1)) X S i Lₙ →
      scalarFiniteLocalModelsOnStratum (DerivedNakayama.quotientRing l E (n + 2)) X S i
        Δ.obj₃) := by
  constructor
  · intro h₀
    exact scalarLocal_of_iso _ X S i e₀.symm
      (native_residue_local l E X (n + 1) L₀ S i h₀)
  · intro hₙ
    exact scalarLocal_of_iso _ X S i eₙ.symm
      (native_transition_local l E X n Lₙ S i hₙ)

end AlgebraicGeometry.ProEtale
