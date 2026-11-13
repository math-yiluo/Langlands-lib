import Langlands.Geometry.Building.ValuationBuildingQuotientMap
import Langlands.Geometry.Building.CrossTorusCentralizerCompatibility
import Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessProof
import Langlands.Geometry.Building.FullValidity.InnerBuildingComparison
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-!
# Comparison of two valuation-building data for the same group

`KPApartmentData.Transfer.ofTransport` is the transfer given by transport of an apartment class
along simultaneous isomorphisms of tori and groups. With the conjugacy of maximal split tori and
KP Proposition 6.2.6 (`omegaCompatibleApartmentUniqueness`), any two `ValuationBuildingData`
for the same group have a transfer along an inner automorphism, and their reduced buildings are
identified by an equivariant building isomorphism along the identity of `G(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData.Transfer

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {ω : kˣ → ℝ}

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
private theorem pointMap_bijective (f : G ≅ H) : Function.Bijective (rationalPoints.map f.hom) :=
  (isoPointsEquiv f (Over.mk (𝟙 _))).bijective

/-- Transport of an apartment class along simultaneous isomorphisms of the tori and the groups
is a transfer along the induced map of rational points. -/
def ofTransport (e : S ≅ S') (f : G ≅ H) (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (D : KPApartmentData i ω) :
    Transfer D (D.transport e f h) (rationalPoints.map f.hom) where
  e := D.apartmentTransportAffineEquiv e f h
  map_mem_normalizerPoints n := (normalizerPointsTransportEquiv e f h n).2
  e_smul n x := D.apartmentTransportEquiv_smul e f h n x
  map_sharpFixer x := by
    rw [D.map_sharpFixer_transport e f h {x}, Set.image_singleton]
    rfl
  mem_normalizerPoints_of_map g hg := by
    obtain ⟨n, hn⟩ := (normalizerPointsTransportEquiv e f h).surjective ⟨_, hg⟩
    have hng : rationalPoints.map f.hom n = rationalPoints.map f.hom g :=
      congrArg Subtype.val hn
    rw [← (pointMap_bijective f).injective hng]
    exact n.2
  exists_mul h' := by
    obtain ⟨g, rfl⟩ := (pointMap_bijective f).surjective h'
    exact ⟨g, 1, by simp⟩
  transportedRoots_eq := by
    ext ψ'
    obtain ⟨ψ, rfl⟩ := (D.affineFunctionalTransportEquiv e f h).surjective ψ'
    have hfun : ∀ ζ : D.Apartment →ᵃ[ℝ] ℝ,
        AffineRootSystem.affineFunctionalTransport (D.apartmentTransportAffineEquiv e f h) ζ =
          D.affineFunctionalTransportEquiv e f h ζ := fun ζ => AffineMap.ext fun _ => rfl
    constructor
    · rintro ⟨ζ, hζ, hζψ⟩
      rw [hfun] at hζψ
      rw [← (D.affineFunctionalTransportEquiv e f h).injective hζψ]
      exact (D.mem_affineRoots_transport_iff e f h ζ).2 hζ
    · intro hψ
      exact ⟨ψ, (D.mem_affineRoots_transport_iff e f h ψ).1 hψ, hfun ψ⟩

variable {S₂ : CommGroupScheme (Spec (CommRingCat.of k))}
  {G₂ : GroupScheme (Spec (CommRingCat.of k))}
  {i₂ : S₂.toGrp ⟶ G₂} [Mono i₂.hom.hom.left] [IsAffineHom G₂.X.hom]

/-- Replace the target apartment class of a transfer by an equal one. -/
def congrRight {D₁ : KPApartmentData i ω} {D₂ D₂' : KPApartmentData i₂ ω}
    {θ : rationalPoints G →* rationalPoints G₂} (t : Transfer D₁ D₂ θ) (hD : D₂ = D₂') :
    Transfer D₁ D₂' θ :=
  hD ▸ t

end KPApartmentData.Transfer

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Two valuation-building data for the same group admit a transfer along an inner
automorphism: conjugate the maximal split torus of `B₁` onto that of `B₂`, transport the
apartment class of `B₁`, and identify the result with that of `B₂` by KP Proposition 6.2.6. -/
theorem exists_transfer_innerIso (B₁ B₂ : ValuationBuildingData G) :
    ∃ g : rationalPoints G,
      Nonempty (B₁.apartment.Transfer B₂.apartment (rationalPoints.map (G.innerIso g).hom)) := by
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G B₁.isConnectedReductive).1
    B₁.S B₂.S B₁.i B₂.i B₁.isMaximalSplitTorus B₂.isMaximalSplitTorus
  let σ : B₁.S ≅ B₂.S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hσ : B₁.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ B₂.i := he
  have hEq : B₁.apartment.transport σ (G.innerIso g) hσ = B₂.apartment :=
    omegaCompatibleApartmentUniqueness F G B₂.isConnectedReductive B₂.S B₂.i
      B₂.isMaximalSplitTorus B₂.centralizer _ _
      (B₁.isOmegaCompatible.transport_basedIso B₁.centralizer B₂.centralizer σ
        (G.innerIso g) hσ)
      B₂.isOmegaCompatible
  exact ⟨g, ⟨(KPApartmentData.Transfer.ofTransport σ (G.innerIso g) hσ B₁.apartment).congrRight
    hEq⟩⟩

/-- Any two valuation-building data for the same group have reduced buildings identified by
an equivariant building isomorphism along the identity of `G(F)`. -/
theorem exists_isEquivariantBuildingIso_id (B₁ B₂ : ValuationBuildingData G) :
    ∃ Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding,
      IsEquivariantBuildingIso B₁ B₂ (MonoidHom.id _) Φ := by
  obtain ⟨g, ⟨t⟩⟩ := exists_transfer_innerIso B₁ B₂
  have hΦ := Transfer.isEquivariantBuildingIso t
  refine ⟨t.reducedBuildingEquiv.trans (MulAction.toPerm g⁻¹),
    hΦ.1.trans (isBuildingIso_smul B₂ g⁻¹), fun k y => ?_⟩
  change g⁻¹ • t.reducedBuildingEquiv (k • y) = k • (g⁻¹ • t.reducedBuildingEquiv y)
  rw [hΦ.2, rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self, mul_smul,
    mul_smul, inv_smul_smul, ← mul_smul]

/-- An equivariant building isomorphism to one valuation-building datum of the target group
gives one to any other datum of that group. -/
theorem IsEquivariantBuildingIso.exists_retarget {F₁ : Type u} [Field F₁] [ValuativeRel F₁]
    [TopologicalSpace F₁] [IsNonarchimedeanLocalField F₁]
    {G₁ : GroupScheme (Spec (CommRingCat.of F₁))} [IsAffineHom G₁.X.hom]
    {B₁ : ValuationBuildingData G₁} {B₂ B₂' : ValuationBuildingData G}
    {θ : rationalPoints G₁ →* rationalPoints G} {Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding}
    (hΦ : IsEquivariantBuildingIso B₁ B₂ θ Φ) :
    ∃ Ψ : B₁.ReducedBuilding ≃ B₂'.ReducedBuilding, IsEquivariantBuildingIso B₁ B₂' θ Ψ := by
  obtain ⟨Φ', hΦ'⟩ := exists_isEquivariantBuildingIso_id B₂ B₂'
  have h := hΦ.trans hΦ'
  rw [MonoidHom.id_comp] at h
  exact ⟨Φ.trans Φ', h⟩

/-- An equivariant building isomorphism from one valuation-building datum of the source group
gives one from any other datum of that group. -/
theorem IsEquivariantBuildingIso.exists_resource {F₂ : Type u} [Field F₂] [ValuativeRel F₂]
    [TopologicalSpace F₂] [IsNonarchimedeanLocalField F₂]
    {G₂ : GroupScheme (Spec (CommRingCat.of F₂))} [IsAffineHom G₂.X.hom]
    {B₁ B₁' : ValuationBuildingData G} {B₂ : ValuationBuildingData G₂}
    {θ : rationalPoints G →* rationalPoints G₂} {Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding}
    (hΦ : IsEquivariantBuildingIso B₁ B₂ θ Φ) :
    ∃ Ψ : B₁'.ReducedBuilding ≃ B₂.ReducedBuilding, IsEquivariantBuildingIso B₁' B₂ θ Ψ := by
  obtain ⟨Φ', hΦ'⟩ := exists_isEquivariantBuildingIso_id B₁' B₁
  have h := hΦ'.trans hΦ
  rw [MonoidHom.comp_id] at h
  exact ⟨Φ'.trans Φ, h⟩

end ValuationBuildingData

end Langlands.Geometry.Building
