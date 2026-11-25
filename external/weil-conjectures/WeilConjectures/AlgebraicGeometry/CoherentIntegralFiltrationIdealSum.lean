/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumZero
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumStep

/-! # Filtering a finite sum of an integral ideal pushforward

Source: Stacks Project, Tag 01YF, final paragraph (the source filtration).
(blueprint: lem-weil-pbc-coherent-integral-filtration-ideal-sum)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The pushforward of a finite sum of one nonzero coherent ideal on an integral
closed subscheme has the required filtration.
Source: Stacks Project, Tag 01YF (`lemma-coherent-filter`), final paragraph,
the filtration of the source of the generic-point inclusion.
(blueprint: lem-weil-pbc-coherent-integral-filtration-ideal-sum)

Proof: a closed immersion into a locally Noetherian scheme makes Z locally
Noetherian. Its finite pushforward sends a coherent ideal to a coherent module.
It preserves finite sums: on every open, pushforward just evaluates the source
sheaf on its inverse image, and finite sums of modules are finite products.
For k = 0,...,r, take the subobject defined by the inclusion of the first k
summands into the r-fold sum of i_*I. These inclusions are split monomorphisms,
ordered by k, with zero and full endpoints. The subobjects are coherent by
finite-sum closure. The cokernel of each consecutive inclusion is isomorphic
to the next summand i_*I by the split sum identities. Use Z, i and I as the
integral-ideal witness for each quotient. Transport the chain along the finite
sum comparison isomorphism to i_*(I^{⊕r}). For r = 0, use the zero-length chain
on the zero object; there are no quotient conditions. -/
theorem coherentIntegralFiltration_ideal_sum
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (r : ℕ) (I : Z.IdealSheafData) (hne : I ≠ ⊥)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules) :
    HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules)) := by
  induction r with
  | zero => exact coherentIntegralFiltration_ideal_sum_zero i I
  | succ r ih => exact coherentIntegralFiltration_ideal_sum_succ i r I hne hI ih

end AlgebraicGeometry.Scheme.Modules
