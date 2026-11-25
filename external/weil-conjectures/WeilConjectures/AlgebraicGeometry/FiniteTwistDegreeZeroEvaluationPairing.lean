/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps

/-! # The degree-zero finite-twist evaluation as a flat single-object pairing

Source: the evaluation identification of the projective-line decomposition
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Express the fixed degree-zero evaluation using the flat single-object pairing.

Source: Stacks Tag 06YQ and the evaluation step of thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).

Proof: unfold the degree-zero evaluation and its flat tensor comparison. Use the
actual internal-Hom evaluation appearing in that definition. The positive Tate sheaf
is the finite line. The cached single-object functor is definitionally the
canonical degree-zero functor, and flatness proofs are irrelevant, so the two remaining
composites coincide. This also holds for zero coefficients and empty schemes. -/
theorem finiteTwistDegreeZeroEvaluation_pairing
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (hL : ObjectProperty.flat (Scheme.finiteEtaleTateLine T N A hA)) :
    p1DecompositionDegreeZeroEvaluation A N hN hA T hT =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1)))).app
        (ordinaryFiniteLine A N hA T) ≫
      singleFunctorFlatPairing
        (Scheme.finiteEtaleTateLine T N A hA)
        (Scheme.finiteEtaleTateSheaf A N T hA (-1))
        (ordinaryFiniteConstant A T)
        hL
        ((ihom.ev (Scheme.finiteEtaleTateLine T N A hA)).app
          (ordinaryFiniteConstant A T)) := by
  delta p1DecompositionDegreeZeroEvaluation p1DecompositionDegreeZeroTensor
    singleFunctorFlatPairing
  delta ordinaryFiniteLine ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
  rfl

end AlgebraicGeometry.Etale
