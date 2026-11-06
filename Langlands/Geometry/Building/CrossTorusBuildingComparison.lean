import Langlands.Geometry.Building.CrossTorusApartmentComparison
import Langlands.Geometry.Building.CrossTorusAffineRoots
import Langlands.Geometry.Building.CrossTorusReducedBuilding
import Langlands.Geometry.Building.AffineWeylTransport

/-! # Actual roots and reduced quotients for a separately supplied target class -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}
  (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
  (D : KPApartmentData i ω) (E : KPApartmentData j ω)
  (x₀ : D.Apartment)
  (h₀ : RootFunctionFamily.transportEquiv e f x₀.val ∈ E.carrier)

private theorem comparison_self :
    D.apartmentTransportAffineEquivOfMem e f h (D.transport e f h) x₀
        (show RootFunctionFamily.transportEquiv e f x₀.val ∈
          (D.transport e f h).carrier from ⟨x₀.val, x₀.mem, rfl⟩) =
      D.apartmentTransportAffineEquiv e f h := by
  apply AffineEquiv.ext
  intro x
  apply Apartment.ext
  rfl

private theorem functional_transport (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    AffineRootSystem.affineFunctionalTransport (D.apartmentTransportAffineEquiv e f h) ψ =
      D.affineFunctionalTransportEquiv e f h ψ := by
  apply AffineMap.ext
  intro x
  rfl

/-- Extended-root membership for the chosen target class is preserved and reflected. -/
theorem mem_extendedAffineRoots_comparison_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    AffineRootSystem.affineFunctionalTransport
        (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀) ψ ∈ E.extendedAffineRoots ↔
      ψ ∈ D.extendedAffineRoots := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  rw [comparison_self, functional_transport]
  exact D.mem_extendedAffineRoots_transport_iff e f h ψ

/-- The ordinary-root noncontainment test, including the double root, is unchanged. -/
theorem mem_affineRoots_comparison_iff (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    AffineRootSystem.affineFunctionalTransport
        (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀) ψ ∈ E.affineRoots ↔
      ψ ∈ D.affineRoots := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  rw [comparison_self, functional_transport]
  exact D.mem_affineRoots_transport_iff e f h ψ

/-- Equality of the entire extended-root sets follows from the single matching family. -/
theorem transported_extendedAffineRoots_of_mem :
    AffineRootSystem.transportedRoots
        (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀) D.extendedAffineRoots =
      E.extendedAffineRoots := by
  let c := D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀
  ext ψ'
  obtain ⟨ψ, rfl⟩ := (AffineRootSystem.affineFunctionalTransport c).surjective ψ'
  constructor
  · rintro ⟨ζ, hζ, hζψ⟩
    have hζeq := (AffineRootSystem.affineFunctionalTransport c).injective hζψ
    subst ζ
    exact (D.mem_extendedAffineRoots_comparison_iff e f h E x₀ h₀ ψ).2 hζ
  · intro hψ
    exact ⟨ψ, (D.mem_extendedAffineRoots_comparison_iff e f h E x₀ h₀ ψ).1 hψ, rfl⟩

/-- Equality of the entire ordinary affine-root sets uses the same comparison. -/
theorem transported_affineRoots_of_mem :
    AffineRootSystem.transportedRoots
        (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀) D.affineRoots = E.affineRoots := by
  let c := D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀
  ext ψ'
  obtain ⟨ψ, rfl⟩ := (AffineRootSystem.affineFunctionalTransport c).surjective ψ'
  constructor
  · rintro ⟨ζ, hζ, hζψ⟩
    have hζeq := (AffineRootSystem.affineFunctionalTransport c).injective hζψ
    subst ζ
    exact (D.mem_affineRoots_comparison_iff e f h E x₀ h₀ ψ).2 hζ
  · intro hψ
    exact ⟨ψ, (D.mem_affineRoots_comparison_iff e f h E x₀ h₀ ψ).1 hψ, rfl⟩

/-- The actual reduced quotient comparison to independently supplied matching data. -/
def reducedBuildingTransportEquivOfMem : D.ReducedBuilding ≃ E.ReducedBuilding :=
  (D.reducedBuildingTransportEquiv e f h).trans
    (Equiv.cast (congrArg (fun A : KPApartmentData j ω => A.ReducedBuilding)
      (D.transport_eq_of_mem e f h E x₀ h₀)))

/-- The comparison is actual ambient transport on every original quotient representative. -/
@[simp] theorem reducedBuildingTransportEquivOfMem_mk
    (g : rationalPoints G) (x : D.Apartment) :
    D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀
        (ApartmentQuotient.mk D.sharpFixerFamily (g, x)) =
      ApartmentQuotient.mk E.sharpFixerFamily
        (rationalPoints.map f.hom g, D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x) := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  rfl

/-- The chosen canonical apartment chart commutes with both comparison maps. -/
@[simp] theorem reducedBuildingTransportEquivOfMem_apartmentMap (x : D.Apartment) :
    D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀ (D.apartmentMap x) =
      E.apartmentMap (D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀ x) := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  exact D.reducedBuildingTransportEquiv_apartmentMap e f h x

/-- The existing quotient actions intertwine through the actual ambient-point map. -/
theorem reducedBuildingTransportEquivOfMem_smul (g : rationalPoints G)
    (q : D.ReducedBuilding) :
    D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀ (g • q) =
      rationalPoints.map f.hom g •
        D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀ q := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  exact D.reducedBuildingTransportEquiv_smul e f h g q

/-- Full stabilizers have exactly the actual ambient subgroup images. -/
theorem map_reducedFixer_comparison (q : D.ReducedBuilding) :
    (D.reducedFixer q).map (rationalPoints.map f.hom) =
      E.reducedFixer (D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀ q) := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  exact D.map_reducedFixer_transport e f h q

/-- The quotient comparison is independent of the witness matching the full classes. -/
theorem reducedBuildingTransportEquivOfMem_independent (x₁ : D.Apartment)
    (h₁ : RootFunctionFamily.transportEquiv e f x₁.val ∈ E.carrier) :
    D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀ =
      D.reducedBuildingTransportEquivOfMem e f h E x₁ h₁ := rfl

include e f h D x₀ h₀ in
/-- The actual apartment chart is injective on one side exactly when it is on the other. -/
theorem apartmentMap_injective_comparison_iff :
    Function.Injective E.apartmentMap ↔ Function.Injective D.apartmentMap := by
  have hDE := D.transport_eq_of_mem e f h E x₀ h₀
  subst E
  exact D.apartmentMap_injective_transport_iff e f h

end Langlands.Geometry.Building.KPApartmentData
