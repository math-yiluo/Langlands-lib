import Langlands.GroupScheme.IntegralModel.HenselianTransporter
import Langlands.Geometry.Building.ConjugateApartmentRealization

/-! # Integral transporters preserve containment in translated apartments -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G}
  {H : GroupScheme (Spec (CommRingCat.of R))}
  {k : Type u} [Field k] [Algebra R k]
  {j₁ j₂ : H ⟶ M.group}
  {g₀ : Over.mk (Spec.algebraMap R k) ⟶ M.group.X}
  (A : M.TransporterData j₁ j₂ g₀)
  {T : CommGroupScheme (Spec (CommRingCat.of K))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : Kˣ → ℝ} (D : KPApartmentData i ω)

/-- The chart translated first by `q` and then by the actual generic point
of an integral transporter. -/
def integralTransporterApartmentMap (q : rationalPoints G) (x : D.Apartment) :
    D.ReducedBuilding :=
  (A.genericPoint * q) • D.apartmentMap x

/-- If all model integral points fix a subset, translating a covering chart
by the integral transporter preserves its coverage of that subset. -/
theorem subset_range_integralTransporterApartmentMap
    {Y : Set D.ReducedBuilding}
    (hM : M.integralPoints ≤ fixingSubgroup (rationalPoints G) Y)
    (q : rationalPoints G)
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x)) :
    Y ⊆ Set.range (D.integralTransporterApartmentMap A q) := by
  intro y hy
  obtain ⟨x, hx⟩ := hY hy
  change q • D.apartmentMap x = y at hx
  refine ⟨x, ?_⟩
  change (A.genericPoint * q) • D.apartmentMap x = y
  rw [mul_smul, hx]
  exact ((mem_fixingSubgroup_iff _).mp (hM A.genericPoint_mem_integralPoints)) y hy

/-- When the translated chart is realized as an actual conjugate valuation
apartment, that same conjugate apartment contains the fixed subset. -/
theorem subset_range_integralTransporter_conjugateApartmentMap
    {T' : CommGroupScheme (Spec (CommRingCat.of K))}
    {i' : T'.toGrp ⟶ G} [Mono i'.hom.hom.left]
    {Y : Set D.ReducedBuilding}
    (hM : M.integralPoints ≤ fixingSubgroup (rationalPoints G) Y)
    (q : rationalPoints G)
    (hY : Y ⊆ Set.range (fun x : D.Apartment => q • D.apartmentMap x))
    (e : T ≅ T')
    (h : i ≫ (G.innerIso (A.genericPoint * q)).hom =
      CommGroupScheme.groupHom e.hom ≫ i') :
    Y ⊆ Set.range (D.conjugateApartmentMap e (A.genericPoint * q) h) := by
  intro y hy
  obtain ⟨x, hx⟩ := D.subset_range_integralTransporterApartmentMap A hM q hY hy
  refine ⟨D.apartmentTransportEquiv e (G.innerIso (A.genericPoint * q)) h x, ?_⟩
  rw [D.conjugateApartmentMap_transport]
  exact hx

end Langlands.Geometry.Building.KPApartmentData
