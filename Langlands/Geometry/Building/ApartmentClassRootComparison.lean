import Langlands.Geometry.Building.ConjugateApartmentIndependence
import Langlands.Geometry.Building.AffineFacetTransport

/-! # Actual affine roots for equal valuation classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.Geometry.Building.AffineRootSystem

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D E : KPApartmentData i ω)
  (hDE : D.carrier = E.carrier)

attribute [simp] apartmentAffineEquivOfCarrierEq_val apartmentAffineEquivOfCarrierEq_linear

/-- The comparison intertwines the original normalizer actions. -/
theorem apartmentAffineEquivOfCarrierEq_smul (n : normalizerPoints i) (x : D.Apartment) :
    apartmentAffineEquivOfCarrierEq D E hDE (n • x) =
      n • apartmentAffineEquivOfCarrierEq D E hDE x := by
  apply Apartment.ext
  rfl

/-- The actual filtration subgroups agree at corresponding points and levels. -/
theorem filtration_apartmentAffineEquivOfCarrierEq (x : D.Apartment)
    (a : characterLattice S) (r : ℝ) :
    E.filtration (apartmentAffineEquivOfCarrierEq D E hDE x) a r =
      D.filtration x a r := by
  apply Subgroup.ext
  intro g
  rfl

/-- Inverse precomposition preserves the actual affine root subgroup. -/
theorem affineRootGroup_apartmentAffineEquivOfCarrierEq (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    E.affineRootGroup a
        (affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE) ψ) =
      D.affineRootGroup a ψ := by
  let e := apartmentAffineEquivOfCarrierEq D E hDE
  apply Subgroup.ext
  intro g
  simp only [affineRootGroup, Subgroup.mem_iInf]
  constructor
  · intro hg x
    have hx := hg (e x)
    simpa only [affineFunctionalTransport_apply, e, AffineEquiv.symm_apply_apply,
      filtration_apartmentAffineEquivOfCarrierEq] using hx
  · intro hg y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [affineFunctionalTransport_apply, e, AffineEquiv.symm_apply_apply,
      filtration_apartmentAffineEquivOfCarrierEq] using hg x

/-- The strict affine root subgroup also agrees under the same comparison. -/
theorem affineRootGroupPlus_apartmentAffineEquivOfCarrierEq (a : characterLattice S)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    E.affineRootGroupPlus a
        (affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE) ψ) =
      D.affineRootGroupPlus a ψ := by
  apply Subgroup.ext
  intro g
  rw [mem_affineRootGroupPlus, mem_affineRootGroupPlus]
  have hconst (c : ℝ) :
      affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE)
          (ψ + AffineMap.const ℝ D.Apartment c) =
        affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE) ψ +
          AffineMap.const ℝ E.Apartment c := by
    ext y
    rfl
  constructor
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rwa [← hconst, affineRootGroup_apartmentAffineEquivOfCarrierEq] at hg
  · rintro ⟨c, hc, hg⟩
    refine ⟨c, hc, ?_⟩
    rwa [← hconst, affineRootGroup_apartmentAffineEquivOfCarrierEq]

/-- Since the derivative is the identity, the derivative of each functional is unchanged. -/
theorem affineFunctionalTransport_carrierEq_linear (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    (affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE) ψ).linear =
      ψ.linear := by
  apply LinearMap.ext
  intro v
  exact affineFunctionalTransport_linear_apply
    (apartmentAffineEquivOfCarrierEq D E hDE) ψ v

/-- Both the actual root derivative and the double-root noncontainment test agree. -/
theorem mem_affineRoots_apartmentAffineEquivOfCarrierEq_iff
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    affineFunctionalTransport (apartmentAffineEquivOfCarrierEq D E hDE) ψ ∈
        E.affineRoots ↔ ψ ∈ D.affineRoots := by
  simp only [affineRoots, Set.mem_ofPred_eq, affineFunctionalTransport_carrierEq_linear,
    affineRootGroup_apartmentAffineEquivOfCarrierEq,
    affineRootGroupPlus_apartmentAffineEquivOfCarrierEq]

/-- The complete actual affine root sets are identified, not just their derivatives. -/
theorem transportedRoots_apartmentAffineEquivOfCarrierEq :
    transportedRoots (apartmentAffineEquivOfCarrierEq D E hDE) D.affineRoots =
      E.affineRoots := by
  ext ψ
  constructor
  · rintro ⟨ψ₀, hψ₀, rfl⟩
    exact (mem_affineRoots_apartmentAffineEquivOfCarrierEq_iff D E hDE ψ₀).2 hψ₀
  · intro hψ
    let ψ₀ := (affineFunctionalTransport
      (apartmentAffineEquivOfCarrierEq D E hDE)).symm ψ
    refine ⟨ψ₀, ?_, (affineFunctionalTransport
      (apartmentAffineEquivOfCarrierEq D E hDE)).apply_symm_apply ψ⟩
    apply (mem_affineRoots_apartmentAffineEquivOfCarrierEq_iff D E hDE ψ₀).1
    simpa only [ψ₀, LinearEquiv.apply_symm_apply] using hψ

/-- Consequently the full sign-defined apartment facets agree. -/
theorem isFacet_image_apartmentAffineEquivOfCarrierEq_iff (Fa : Set D.Apartment) :
    IsFacet E.affineRoots (apartmentAffineEquivOfCarrierEq D E hDE '' Fa) ↔
      IsFacet D.affineRoots Fa :=
  isFacet_image_iff_of_transportedRoots_eq (apartmentAffineEquivOfCarrierEq D E hDE)
    (transportedRoots_apartmentAffineEquivOfCarrierEq D E hDE) Fa

/-- Equal valuation classes give an actual equivalence between their full
apartment facets, with the original valuation-preserving point map. -/
def apartmentFacetEquivOfCarrierEq :
    {Fa : Set D.Apartment // IsFacet D.affineRoots Fa} ≃
      {Fb : Set E.Apartment // IsFacet E.affineRoots Fb} :=
  facetEquivOfTransportedRootsEq (apartmentAffineEquivOfCarrierEq D E hDE)
    (transportedRoots_apartmentAffineEquivOfCarrierEq D E hDE)

@[simp] theorem apartmentFacetEquivOfCarrierEq_apply
    (Fa : {Fa : Set D.Apartment // IsFacet D.affineRoots Fa}) :
    (apartmentFacetEquivOfCarrierEq D E hDE Fa).val =
      apartmentAffineEquivOfCarrierEq D E hDE '' Fa.val := rfl

/-- Equal valuation classes likewise give an equivalence of chambers. -/
def apartmentChamberEquivOfCarrierEq :
    {Ca : Set D.Apartment // IsChamber D.affineRoots Ca} ≃
      {Cb : Set E.Apartment // IsChamber E.affineRoots Cb} :=
  chamberEquivOfTransportedRootsEq (apartmentAffineEquivOfCarrierEq D E hDE)
    (transportedRoots_apartmentAffineEquivOfCarrierEq D E hDE)

@[simp] theorem apartmentChamberEquivOfCarrierEq_apply
    (Ca : {Ca : Set D.Apartment // IsChamber D.affineRoots Ca}) :
    (apartmentChamberEquivOfCarrierEq D E hDE Ca).val =
      apartmentAffineEquivOfCarrierEq D E hDE '' Ca.val := rfl

end Langlands.Geometry.Building.KPApartmentData
