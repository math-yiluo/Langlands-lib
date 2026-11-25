import Langlands.Cohomology.PointProductAcyclic
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison

/-! # Compact acyclicity of analytic étale point products -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct Langlands.Cohomology.PointProductAcyclic

universe u v uL wI w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

private local instance {S : Type w} [CommRing S] :
    HasProducts.{wI} (ModuleCat.{max wI w} S) := by
  let := hasLimitsOfSizeShrink.{wI, wI, w, w} (ModuleCat.{max wI w} S)
  infer_instance

/-- An actual analytic point product has an injective resolution obtained by
resolving its independent module coefficients. -/
def etalePointProductInjectiveResolution
    (M : Discrete ((localizedFieldPointFunctor L).obj X) ⥤
      ModuleCat.{max u (v + 1) uL} R) :
    haveI := etale_hasSheafify.{u, v, uL} X R
    InjectiveResolution
      ((coefficientProductFunctor.{max u v uL, max u (v + 1) uL}
        (etalePoints L h) R).obj M) :=
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  coefficientProductInjectiveResolution.{max u v uL, max u (v + 1) uL}
    (etalePoints L h) R M

/-- The existing positive compact étale cohomology vanishes on an actual
point product with arbitrary module coefficients. -/
theorem isZero_etaleCompactCohomology_coefficientPointProduct
    (M : Discrete ((localizedFieldPointFunctor L).obj X) ⥤
      ModuleCat.{max u (v + 1) uL} R) (q : ℕ) :
    IsZero ((etaleCompactCohomology L h R (q + 1)).obj
      ((coefficientProductFunctor.{max u v uL, max u (v + 1) uL}
        (etalePoints L h) R).obj M)) := by
  let := pointTopology L X
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etale_hasSheafify.{u, v, uL} X R
  have := etale_enoughInjectives.{u, v, uL} X R
  exact isZero_compactDerived_coefficientProduct.{max u v uL, max u (v + 1) uL}
    (etalePoints L h) R M (etaleSelf X) q

/-- The family presentation of analytic point products has the same vanishing. -/
theorem isZero_etaleCompactCohomology_pointProduct
    (M : (localizedFieldPointFunctor L).obj X → ModuleCat.{max u (v + 1) uL} R)
    (q : ℕ) :
    IsZero ((etaleCompactCohomology L h R (q + 1)).obj
      ((productFunctor (etalePoints L h) (ModuleCat.{max u (v + 1) uL} R)).obj M)) :=
  isZero_etaleCompactCohomology_coefficientPointProduct.{u, v, uL} L h R (Discrete.functor M) q

end Langlands.Sheaf.Equivariant.Analytic
