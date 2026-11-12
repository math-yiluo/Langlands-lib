import Langlands.Geometry.Building.ValuationBuildingChartIso
import Langlands.Geometry.Building.CrossTorusBuildingComparison
import Langlands.Geometry.Building.IntegerValuationLocalComparison

/-!
# Chart isomorphisms from transports over one field

Equal apartment data, a change of the field order along an equality, and the transport of
apartment data along simultaneous isomorphisms of the torus and the ambient group give chart
isomorphisms of reduced buildings.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]

section SameTorus

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω ω' : kˣ → ℝ}

/-- Equal apartment data are related by a chart isomorphism along the identity. -/
theorem exists_isChartIso_of_eq {D E : KPApartmentData i ω} (h : D = E) :
    ∃ (e : D.Apartment ≃ᵃ[ℝ] E.Apartment) (Φ : D.ReducedBuilding ≃ E.ReducedBuilding),
      IsChartIso D E (MonoidHom.id _) 1 e Φ := by
  subst h
  exact ⟨_, _, IsChartIso.refl D⟩

/-- Reindexing the field order along an equality is a chart isomorphism along the identity. -/
theorem isChartIso_reindexOrder (D : KPApartmentData i ω) (h : ω = ω') :
    IsChartIso D (D.reindexOrder h) (MonoidHom.id _) 1 (D.reindexOrderApartment h)
      (D.reindexOrderBuilding h) := by
  cases h
  exact IsChartIso.refl D

end SameTorus

section Transport

variable {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω) (E : KPApartmentData j ω)

/-- The comparison of reduced buildings with independently supplied matching data is a chart
isomorphism along the ambient point map, with base point `1`. -/
theorem isChartIso_reducedBuildingTransportEquivOfMem (x₀ : D.Apartment)
    (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier) :
    IsChartIso D E (rationalPoints.map f.hom) 1
      (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀)
      (D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀) where
  map_smul_apartmentMap g x := by
    rw [reducedBuildingTransportEquivOfMem_smul, reducedBuildingTransportEquivOfMem_apartmentMap,
      mul_one]
  transportedRoots_eq := D.transported_affineRoots_of_mem e f h E x₀ h₀

/-- If the transport of `D` is `E`, the reduced buildings of `D` and `E` are related by a chart
isomorphism along the ambient point map, with base point `1`. -/
theorem exists_isChartIso_of_transport_eq (hDE : D.transport e f h = E) :
    ∃ (c : D.Apartment ≃ᵃ[ℝ] E.Apartment) (Φ : D.ReducedBuilding ≃ E.ReducedBuilding),
      IsChartIso D E (rationalPoints.map f.hom) 1 c Φ := by
  obtain ⟨x₀, h₀⟩ := (D.transport_eq_iff_exists_mem e f h E).1 hDE
  exact ⟨_, _, isChartIso_reducedBuildingTransportEquivOfMem e f h D E x₀ h₀⟩

/-- Transporting `E` back along the inverse isomorphisms and then forward recovers `E`. -/
theorem transport_transport_symm :
    (E.transport e.symm f.symm (torusTransport_inverse_square e f h)).transport e f h = E :=
  (transportEquiv e f h).apply_symm_apply E

/-- The reduced buildings of the inverse transport of `E` and of `E` are related by a chart
isomorphism along the ambient point map, with base point `1`. -/
theorem exists_isChartIso_transport_symm :
    ∃ (c : (E.transport e.symm f.symm (torusTransport_inverse_square e f h)).Apartment ≃ᵃ[ℝ]
        E.Apartment)
      (Φ : (E.transport e.symm f.symm (torusTransport_inverse_square e f h)).ReducedBuilding ≃
        E.ReducedBuilding),
      IsChartIso (E.transport e.symm f.symm (torusTransport_inverse_square e f h)) E
        (rationalPoints.map f.hom) 1 c Φ :=
  exists_isChartIso_of_transport_eq e f h _ E (transport_transport_symm e f h E)

end Transport

end Langlands.Geometry.Building.KPApartmentData
