/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Iterated strict étale inverse-image transitions

Source: Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The ordinary inverse image respects every normalized iterated transition.
Source: Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-pur-strict-etale-inverse-transition)

Proof: compose the underlying map of the inverse-evaluation comparison at level q
with the algebraic lift's underlying-sheaf comparison, obtaining a map a_q to the
geometric inverse image of the underlying qth level. Faithful forgetting and the
prescribed underlying formula for scalar restriction identify the claimed equation
with tau_inverse(m,n) followed by a_n = a_m followed by inverse image of tau(m,n).
For equal indices this follows from normalized identity transitions and preservation
of identities. The successor case is the ordinary image package's inverseTransition.
For n ≤ m+1 factor the iterated transition through level m. Apply the induction
hypothesis, then the successor case, and use preservation of composition. The
normalization fields identify these composites with the prescribed iterated
transitions on both sides. Faithfulness gives the original module-map equation.
This is the already proved ordinaryInverseTransition calculation, specialized to
small étale sites; no property of an open immersion is required. -/
theorem strictEtaleInverseTransition (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) (I : StrictEtaleOrdinaryImage O t j)
    (PX : StrictEtaleEvaluation X O t) (PZ : StrictEtaleEvaluation Z O t)
    {m n : ℕ} (h : n ≤ m) (N : strictEtaleCoefficientSystem Z O t) :
    (PX.strictTransition h).app (I.inverse.obj N) ≫
        (coefficientRestriction (J := X.smallEtaleTopology) O t h).map
          ((I.inverseEvaluation n).hom.app N) =
      (I.inverseEvaluation m).hom.app N ≫
        (I.lift m).modules.map ((PZ.strictTransition h).app N) ≫
          (I.restrictInverse h).hom.app (N.level n) := by
  exact SheafOfModules.ordinaryInverseTransition O t _ _ _ I PZ PX h N

end AlgebraicGeometry
