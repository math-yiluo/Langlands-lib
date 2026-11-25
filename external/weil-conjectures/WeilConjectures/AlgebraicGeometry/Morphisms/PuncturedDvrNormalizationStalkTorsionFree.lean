/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedDvrNormalizationStalkDomain
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedDvrNormalizationStalkMapInjective

/-! # Torsion-freeness of normalization stalks over a punctured DVR

## References

* Stacks Project, Tags 0307, 035I and 0539
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- The normalization stalk over a punctured DVR is torsion-free. -/
theorem punctured_dvr_normalization_stalk_torsionFree
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    letI := ((p ≫ U.ι).fromNormalization.stalkMap x).hom.toAlgebra
    Module.IsTorsionFree (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))
      ((p ≫ U.ι).normalization.presheaf.stalk x) := by
  let _ := ((p ≫ U.ι).fromNormalization.stalkMap x).hom.toAlgebra
  let _ : IsDomain ((p ≫ U.ι).normalization.presheaf.stalk x) :=
    punctured_dvr_normalization_stalk_isDomain U p hetale x hs
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  exact punctured_dvr_normalization_stalkMap_injective U p hetale x hs

end AlgebraicGeometry.Scheme
