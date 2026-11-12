import Langlands.Geometry.Building.FullValidity.DatumTransport.AffineApartment
import Langlands.Geometry.Building.ValuationBuildingRootReflectionTransport
import Langlands.Geometry.Building.ValuationBuildingAxiomTransport

/-!
# Axiom 4.1.6 under based group isomorphisms

AS 1 (the elements `m(u)` fix the hyperplanes `H_u`), V 7 with AS 2–AS 5, and AS 6 are carried
from building data `B` of `G` to the transported data of `H`. Root groups, opposite factor pairs,
filtrations and normalizer points correspond under `f`; affine functionals, affine roots and
facets correspond under the apartment comparison.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace DatumTransport

section Roots

variable {F : Type u} [Field F]
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
  (e : S ≅ S') (f : G ≅ H) (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include h

/-- Opposite factor pairs correspond under `f`. -/
theorem isOppositeFactorPair_transport_iff (a : characterLattice S) (u : rationalPoints G)
    (p : rationalPoints G × rationalPoints G) :
    RelativeRoot.IsOppositeFactorPair j (characterLattice.congr e a) (rationalPoints.map f.hom u)
        (rationalPoints.map f.hom p.1, rationalPoints.map f.hom p.2) ↔
      RelativeRoot.IsOppositeFactorPair i a u p := by
  change (rationalPoints.map f.hom p.1 ∈ rootGroupPoints j (-(characterLattice.congr e a)) ∧
      rationalPoints.map f.hom p.2 ∈ rootGroupPoints j (-(characterLattice.congr e a)) ∧
      rationalPoints.map f.hom p.1 * rationalPoints.map f.hom u * rationalPoints.map f.hom p.2 ∈
        normalizerPoints j) ↔
    (p.1 ∈ rootGroupPoints i (-a) ∧ p.2 ∈ rootGroupPoints i (-a) ∧
      p.1 * u * p.2 ∈ normalizerPoints i)
  rw [← map_neg, rootGroupPoints_transport_iff e f h, rootGroupPoints_transport_iff e f h,
    ← map_mul, ← map_mul]
  exact and_congr Iff.rfl (and_congr Iff.rfl (mem_normalizerPoints_transport_iff e f h _))

variable [ValuativeRel F] [TopologicalSpace F] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- V 7 is carried by the family transport: `f` restricts to homeomorphisms of the root groups
matching the filtrations, and carries bounded sets to bounded sets. -/
theorem isTopologyCompatible_transport {φ : RootFunctionFamily S G}
    (hφ : IsTopologyCompatible i φ) :
    IsTopologyCompatible j (RootFunctionFamily.transportEquiv e f φ) := by
  unfold IsTopologyCompatible at hφ ⊢
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  intro b hb
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective b
  have ha : a ∈ relativeRoots i := (roots_mem_of_transport_iff e f h a).1 hb
  obtain ⟨hbasis, hr⟩ := hφ a ha
  have hcont₁ : Continuous (rationalPoints.map f.hom) :=
    continuous_rationalPointMap F f.hom.hom.hom
  have hcont₂ : Continuous (rationalPoints.map f.inv) :=
    continuous_rationalPointMap F f.inv.hom.hom
  have hmem₁ (x : rootGroupPoints i a) :
      rationalPoints.map f.hom x ∈ rootGroupPoints j (characterLattice.congr e a) :=
    (rootGroupPoints_transport_iff e f h a x).2 x.2
  have hmem₂ (y : rootGroupPoints j (characterLattice.congr e a)) :
      rationalPoints.map f.inv y ∈ rootGroupPoints i a := by
    rw [← rootGroupPoints_transport_iff e f h, map_hom_map_inv]
    exact y.2
  let Ψ : rootGroupPoints j (characterLattice.congr e a) ≃ₜ rootGroupPoints i a :=
    { toFun := fun y => ⟨rationalPoints.map f.inv y, hmem₂ y⟩
      invFun := fun x => ⟨rationalPoints.map f.hom x, hmem₁ x⟩
      left_inv := fun y => Subtype.ext (map_hom_map_inv f y)
      right_inv := fun x => Subtype.ext (map_inv_map_hom f x)
      continuous_toFun := (hcont₂.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hcont₁.comp continuous_subtype_val).subtype_mk _ }
  have hpre (r : ℝ) :
      Ψ ⁻¹' (((↑) : rootGroupPoints i a → rationalPoints G) ⁻¹' rootFiltration i φ a r) =
        ((↑) : rootGroupPoints j (characterLattice.congr e a) → rationalPoints H) ⁻¹'
          rootFiltration j (RootFunctionFamily.transportEquiv e f φ)
            (characterLattice.congr e a) r := by
    ext y
    change rationalPoints.map f.inv y ∈ rootFiltration i φ a r ↔ _
    rw [← rootFiltration_transport_iff e f h, map_hom_map_inv]
    exact Iff.rfl
  have h1 : Ψ.symm 1 = 1 := Subtype.ext (map_one (rationalPoints.map f.hom))
  refine ⟨?_, fun r => ⟨?_, ?_⟩⟩
  · have hb' := hbasis.comap Ψ
    rw [Ψ.comap_nhds_eq, h1] at hb'
    simpa only [hpre] using hb'
  · rw [← hpre]
    exact (hr r).1.preimage Ψ.continuous
  · rw [← image_rootFiltration_transport e f h]
    exact (hr r).2.image_rationalPointsMap f.hom

end Roots

end DatumTransport

open DatumTransport

namespace ValuationBuildingData

/-! ### AS 6 along building isomorphisms between different groups -/

section Facets

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₁ G₂ : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G₁.X.hom]
  [IsAffineHom G₂.X.hom]
  {B₁ : ValuationBuildingData G₁} {B₂ : ValuationBuildingData G₂}
  (Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding) (A : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)
  (hmap : ∀ x : B₁.Apartment, Φ (B₁.apartmentMap x) = B₂.apartmentMap (A x))
  (hroots : AffineRootSystem.transportedRoots A B₁.affineRoots = B₂.affineRoots)
  (hiso : IsBuildingIso B₁ B₂ Φ)

include hmap hroots hiso in
/-- AS 6 is carried by a building isomorphism compatible with an apartment comparison that
matches the affine roots. -/
theorem HasCompatibleApartmentFacets.of_buildingIso (hB : B₁.HasCompatibleApartmentFacets) :
    B₂.HasCompatibleApartmentFacets where
  injective := by
    intro x y hxy
    have heq : Φ (B₁.apartmentMap (A.symm x)) = Φ (B₁.apartmentMap (A.symm y)) := by
      simpa only [hmap, A.apply_symm_apply] using hxy
    exact A.symm.injective (hB.injective (Φ.injective heq))
  exists_isFacet_of_isFacet Y hY hmeet := by
    let Y₁ : Set B₁.ReducedBuilding := Φ ⁻¹' Y
    have himage : Φ '' Y₁ = Y := Set.image_preimage_eq _ Φ.surjective
    have hY₁ : B₁.IsFacet Y₁ := (hiso.isFacet_image_iff Y₁).1 (himage ▸ hY)
    obtain ⟨q, hqY, x, hxq⟩ := hmeet
    have hmeet₁ : (Y₁ ∩ B₁.apartmentImage).Nonempty := by
      refine ⟨B₁.apartmentMap (A.symm x), ?_, A.symm x, rfl⟩
      change Φ (B₁.apartmentMap (A.symm x)) ∈ Y
      rw [hmap, A.apply_symm_apply, hxq]
      exact hqY
    obtain ⟨Fa, hFa, hYFa⟩ := hB.exists_isFacet_of_isFacet Y₁ hY₁ hmeet₁
    refine ⟨A '' Fa,
      (AffineRootSystem.isFacet_image_iff_of_transportedRoots_eq A hroots Fa).2 hFa, ?_⟩
    rw [← himage, hYFa, Set.image_image, Set.image_image]
    congr 1
    funext x
    exact hmap x

end Facets

/-! ### The transported data -/

section Transport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (B : ValuationBuildingData G) {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {j : S.toGrp ⟶ H} (σ : B.S ≅ S) (f : G ≅ H)
  (h : B.i ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ j)

/-- The transported apartment point carries the transported valuation family. -/
theorem basedApartmentEquiv_val (x : B.Apartment) :
    (B.basedApartmentEquiv σ f h x).val = RootFunctionFamily.transportEquiv σ f x.val :=
  rfl

/-- Values of the transported point at transported inputs are unchanged. -/
theorem basedApartmentEquiv_value (x : B.Apartment) (a : characterLattice B.S)
    (g : rationalPoints G) :
    (B.basedApartmentEquiv σ f h x).val (characterLattice.congr σ a) (rationalPoints.map f.hom g) =
      x.val a g :=
  RootFunctionFamily.transportEquiv_apply_map σ f x.val a g

/-- The extended affine roots `Ψ′` of the target are the transported ones. -/
theorem transportedRoots_extendedAffineRoots_basedApartmentEquiv :
    AffineRootSystem.transportedRoots (B.basedApartmentEquiv σ f h)
        B.apartment.extendedAffineRoots =
      (B.basedTransport σ f h).apartment.extendedAffineRoots := by
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  have hfunc (ψ : B.Apartment →ᵃ[ℝ] ℝ) :
      AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h) ψ =
        B.apartment.affineFunctionalTransportEquiv σ f h ψ := by
    ext y
    rfl
  ext ψ'
  obtain ⟨ψ, rfl⟩ :=
    (AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h)).surjective ψ'
  constructor
  · rintro ⟨ψ₀, hψ₀, heq⟩
    have hψ₀' :=
      (AffineRootSystem.affineFunctionalTransport (B.basedApartmentEquiv σ f h)).injective heq
    subst ψ₀
    rw [hfunc]
    exact (B.apartment.mem_extendedAffineRoots_transport_iff σ f h ψ).mpr hψ₀
  · intro hψ
    rw [hfunc] at hψ
    exact ⟨ψ, (B.apartment.mem_extendedAffineRoots_transport_iff σ f h ψ).mp hψ, rfl⟩

/-- The derivative of the apartment comparison carries the root forms onto the root forms. -/
theorem derivativeTransport_range_rootForm_basedApartmentEquiv :
    AffineRootSystem.derivativeTransport (B.basedApartmentEquiv σ f h) ''
        Set.range (rootForm B.i) = Set.range (rootForm j) :=
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  B.apartment.derivativeTransport_range_rootForm_basedIso σ f h

/-- Conjugating by the apartment comparison carries the action of `n` to that of `f(n)`. -/
theorem affineConjugation_normalizerAction_basedTransport (n : normalizerPoints B.i) :
    AffineRootSystem.affineConjugation (B.basedApartmentEquiv σ f h) (B.normalizerAction n) =
      (B.basedTransport σ f h).normalizerAction (normalizerPointsTransportEquiv σ f h n) := by
  apply AffineEquiv.ext
  intro y
  change B.basedApartmentEquiv σ f h (B.normalizerAction n ((B.basedApartmentEquiv σ f h).symm y))
    = _
  rw [normalizerAction_basedTransport, AffineEquiv.apply_symm_apply]

/-- The image of `N(F)` in the affine automorphisms of the apartment is carried by conjugation. -/
theorem map_normalizerAction_range_basedTransport :
    B.normalizerAction.range.map
        (AffineRootSystem.affineConjugation (B.basedApartmentEquiv σ f h)).toMonoidHom =
      (B.basedTransport σ f h).normalizerAction.range := by
  ext g
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨normalizerPointsTransportEquiv σ f h n,
      (B.affineConjugation_normalizerAction_basedTransport σ f h n).symm⟩
  · rintro ⟨n, rfl⟩
    let m := (normalizerPointsTransportEquiv σ f h).symm n
    refine ⟨B.normalizerAction m, ⟨m, rfl⟩, ?_⟩
    change AffineRootSystem.affineConjugation (B.basedApartmentEquiv σ f h)
      (B.normalizerAction m) = _
    rw [affineConjugation_normalizerAction_basedTransport]
    exact congrArg _ ((normalizerPointsTransportEquiv σ f h).apply_symm_apply n)

/-- AS 1 for `G` gives AS 1 for `H`. -/
theorem HasRootReflections.basedTransport (hB : B.HasRootReflections) :
    (B.basedTransport σ f h).HasRootReflections := by
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  intro β u hu h1 p hp y hy
  obtain ⟨α, rfl⟩ := (relativeRootsTransportEquiv σ f h).surjective β
  obtain ⟨u, rfl⟩ : ∃ u₀, rationalPoints.map f.hom u₀ = u := (pointsEquiv f).surjective u
  obtain ⟨q, rfl⟩ : ∃ q : rationalPoints G × rationalPoints G,
      (rationalPoints.map f.hom q.1, rationalPoints.map f.hom q.2) = p :=
    ⟨((pointsEquiv f).symm p.1, (pointsEquiv f).symm p.2), by
      simp only [pointsEquiv_symm_apply, map_hom_map_inv]⟩
  obtain ⟨x, rfl⟩ := (B.basedApartmentEquiv σ f h).surjective y
  have hu₀ : u ∈ B.rootGroup α := (rootGroupPoints_transport_iff σ f h α u).1 hu
  have h1₀ : u ≠ 1 := fun h' => h1 (by rw [h', map_one])
  have hp₀ := (isOppositeFactorPair_transport_iff σ f h α u q).1 hp
  have hx : x ∈ B.reflectionHyperplane α u := by
    change (B.basedApartmentEquiv σ f h x).val (characterLattice.congr σ α)
      (rationalPoints.map f.hom u) = 0 at hy
    rwa [basedApartmentEquiv_value] at hy
  have hfix := hB α u hu₀ h1₀ q hp₀ x hx
  have hn : normalizerPointsTransportEquiv σ f h (B.reflectionElement hp₀) =
      (B.basedTransport σ f h).reflectionElement hp := by
    apply Subtype.ext
    change rationalPoints.map f.hom (q.1 * u * q.2) =
      rationalPoints.map f.hom q.1 * rationalPoints.map f.hom u * rationalPoints.map f.hom q.2
    rw [map_mul, map_mul]
  have hact := B.normalizerAction_basedTransport σ f h (B.reflectionElement hp₀) x
  rw [hn, B.normalizerAction_apply, (B.basedTransport σ f h).normalizerAction_apply, hfix] at hact
  exact hact.symm

/-- V 7 and AS 2–AS 5 for `G` give them for `H`. -/
theorem SatisfiesApartmentAxioms.basedTransport (hB : B.SatisfiesApartmentAxioms) :
    (B.basedTransport σ f h).SatisfiesApartmentAxioms := by
  have := mono_of_isMaximalSplitTorus (B.isMaximalSplitTorus_of_basedIso σ f h)
  let A := B.basedApartmentEquiv σ f h
  have hext := B.transportedRoots_extendedAffineRoots_basedApartmentEquiv σ f h
  have hroots : AffineRootSystem.transportedRoots A B.apartment.affineRoots =
      (B.basedTransport σ f h).apartment.affineRoots :=
    B.transportedRoots_basedApartmentEquiv σ f h
  have hrange := B.map_normalizerAction_range_basedTransport σ f h
  have hforms := B.derivativeTransport_range_rootForm_basedApartmentEquiv σ f h
  have hW := AffineRootSystem.map_affineWeylGroup A B.affineRoots
  rw [show AffineRootSystem.transportedRoots A B.affineRoots =
    (B.basedTransport σ f h).affineRoots from hroots] at hW
  have hWe := AffineRootSystem.map_extendedAffineWeylGroup A B.affineRoots
  rw [show AffineRootSystem.transportedRoots A B.affineRoots =
    (B.basedTransport σ f h).affineRoots from hroots] at hWe
  refine ⟨(B.basedTransport σ f h).isOmegaCompatible, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨x, hx⟩ := A.surjective (⟨φ, hφ⟩ : (B.basedTransport σ f h).Apartment)
    have hc := isTopologyCompatible_transport σ f h (hB.topologyCompatible x.val x.mem)
    rw [← B.basedApartmentEquiv_val σ f h x,
      show B.basedApartmentEquiv σ f h x = ⟨φ, hφ⟩ from hx] at hc
    exact hc
  · rw [← hext]
    exact hB.isAffineRootSystem_extendedAffineRoots.transport A
  · rw [← hext, AffineRootSystem.derivativeRoots_transportedRoots,
      hB.derivativeRoots_extendedAffineRoots]
    exact hforms
  · rw [← hroots]
    exact hB.isAffineRootSystem_affineRoots.transport A
  · rw [← hroots, AffineRootSystem.derivativeRoots_transportedRoots, hB.derivativeRoots_affineRoots]
    exact hforms
  · intro ψ hψ
    rw [← hext] at hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    rcases hB.mem_or_two_smul_mem φ hφ with h' | h'
    · apply Or.inl
      rw [← hroots]
      exact ⟨φ, h', rfl⟩
    · apply Or.inr
      rw [← hroots]
      exact ⟨(2 : ℝ) • φ, h', map_smul _ _ _⟩
  · rw [← hrange, ← hW]
    exact Subgroup.map_mono hB.affineWeylGroup_le_range
  · rw [← hrange, ← hWe]
    exact Subgroup.map_mono hB.range_le_extendedAffineWeylGroup
  · intro hsc
    rw [← hrange, ← hW,
      hB.range_eq_affineWeylGroup_of_isSimplyConnected (IsSimplyConnected.of_iso f hsc)]
  · intro hqs had
    rw [← hrange, ← hWe, hB.range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint
      (IsQuasiSplit.of_iso f hqs) (IsAdjoint.of_iso f had)]

/-- AS 6 for `G` gives AS 6 for `H`. -/
theorem HasCompatibleApartmentFacets.basedTransport (hB : B.HasCompatibleApartmentFacets) :
    (B.basedTransport σ f h).HasCompatibleApartmentFacets :=
  hB.of_buildingIso (B.basedBuildingEquiv σ f h) (B.basedApartmentEquiv σ f h)
    (B.basedBuildingEquiv_apartmentMap σ f h) (B.transportedRoots_basedApartmentEquiv σ f h)
    (B.isBuildingIso_basedBuildingEquiv σ f h)

end Transport

end ValuationBuildingData

end Langlands.Geometry.Building
