/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! # Resolving complexes are closed under isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization.RestrictionSquare

/-- A complex isomorphic to a flat K-flat complex is flat K-flat. -/
theorem resolving_of_iso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P Q : CochainComplex (Mod R) ℤ} (a : P ≅ Q) (hQ : resolving R Q) :
    resolving R P := by
  let := SheafOfModules.monoidalCategory R
  constructor
  · intro F hF
    exact HomologicalComplex.Acyclic.of_iso (hQ.1 F hF)
      ((total R).mapIso (Iso.prod (Iso.refl F) a.symm))
  · intro n
    have hcat : exactFunctor _ _ (tensorRight (Q.X n)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)) (hQ.2 n)
    have hcat' : exactFunctor _ _ (tensorRight (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        ((curriedTensor (Mod R)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso a.symm)) hcat
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm hcat'

end SheafOfModules.OpenTensorNormalization.RestrictionSquare
