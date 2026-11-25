import Langlands.Algebra.BrauerComparison.AbsoluteComparison
import Langlands.Cohomology.Profinite.Comparison.Continuous
import Langlands.GaloisCohomology.Field.Modules

/-!
# The Brauer group as the second cohomology of the units

For a separable closure `L` of `K`, `Br(K) ≅ H²(Gal(L/K), Lˣ)`, in the cochain model of
`Langlands.ProfiniteCohomology`: the Library's `Langlands.BrauerComparison.brauerContinuousEquiv`
(the isomorphism with Mathlib's continuous cohomology of the discrete module `Lˣ`) followed by the
comparison isomorphism `isoContinuousCohomology`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology ClassFieldTheory.Local CategoryTheory

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The underlying representation of the Library's discrete units module is smooth (it is the
units module). -/
instance isSmoothRep_underlyingRep_discreteUnitsRepresentation [Algebra.IsIntegral K L] :
    IsSmoothRep (underlyingRep (discreteUnitsRepresentation K L)) :=
  inferInstanceAs (IsSmoothRep (unitsModule K L))

/-- The cohomology of the units module in the cochain model is the Library's continuous
cohomology `continuousUnitCohomology K L n` (Mathlib's `continuousCohomology` of the discrete
module `Lˣ`). -/
noncomputable def unitsModuleContinuousEquiv [IsGalois K L] (n : ℕ) :
    cohomology (unitsModule K L) n ≃ₗ[IntegerScalars.{u}]
      (BrauerComparison.continuousUnitCohomology K L n : Type u) :=
  linearEquivContinuousCohomology (discreteUnitsRepresentation K L) n

/-- The Brauer group of `K` is `H²(Gal(L/K), Lˣ)` for a separable closure `L` of `K`. -/
noncomputable def brauerEquiv [IsSepClosure K L] :
    BrauerGroup.{u, u} K ≃+ cohomology (unitsModule K L) 2 :=
  (BrauerComparison.brauerContinuousEquiv K L).trans
    (unitsModuleContinuousEquiv K L 2).symm.toAddEquiv

/-- `brauerEquiv` followed by the comparison with continuous cohomology is the Library's
`brauerContinuousEquiv`. -/
theorem unitsModuleContinuousEquiv_brauerEquiv [IsSepClosure K L] (x : BrauerGroup.{u, u} K) :
    unitsModuleContinuousEquiv K L 2 (brauerEquiv K L x) =
      BrauerComparison.brauerContinuousEquiv K L x :=
  (unitsModuleContinuousEquiv K L 2).apply_symm_apply _

theorem brauerEquiv_symm_apply [IsSepClosure K L] (y : cohomology (unitsModule K L) 2) :
    (brauerEquiv K L).symm y =
      (BrauerComparison.brauerContinuousEquiv K L).symm (unitsModuleContinuousEquiv K L 2 y) :=
  rfl

end Langlands.GaloisCohomology
