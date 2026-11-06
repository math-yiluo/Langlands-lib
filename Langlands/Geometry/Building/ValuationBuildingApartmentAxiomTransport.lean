import Langlands.Geometry.Building.ValuationBuildingAffineApartmentTransport
import Langlands.Geometry.Building.CrossTorusApartmentComparison
import Langlands.Geometry.Building.AffineExtendedWeylTransport

/-! # Transport of the apartment axioms on actual valuation-building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Geometry.Building.AffineRootSystem
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

section Topology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ G}
  (σ : S ≅ S') (hσ : i = CommGroupScheme.groupHom σ.hom ≫ j)

include hσ

omit [ValuativeRel F] [TopologicalSpace F] [IsAffineHom G.X.hom] in
/-- Reparametrizing the same embedded torus leaves each actual root subgroup unchanged. -/
theorem rootGroupPoints_eq_of_torusIso (a : characterLattice S) :
    rootGroupPoints j (characterLattice.congr σ a) = rootGroupPoints i a := by
  have hs : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ j := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  apply Subgroup.ext
  intro g
  simpa only [Iso.refl_hom, rationalPoints.map_apply, Grp.id_hom_hom,
    Category.comp_id] using rootGroupPoints_transport_iff σ (Iso.refl G) hs a g

omit [ValuativeRel F] [TopologicalSpace F] [IsAffineHom G.X.hom] in
/-- The same reindexing preserves every filtration set at its original real level. -/
theorem rootFiltration_eq_of_torusIso (φ : RootFunctionFamily S G)
    (a : characterLattice S) (r : ℝ) :
    rootFiltration j (RootFunctionFamily.transportEquiv σ (Iso.refl G) φ)
        (characterLattice.congr σ a) r = rootFiltration i φ a r := by
  have hs : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ j := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  ext g
  simpa only [Iso.refl_hom, rationalPoints.map_apply, Grp.id_hom_hom,
    Category.comp_id] using rootFiltration_transport_iff σ (Iso.refl G) hs φ a r g

/-- V7 transports with the canonical topology on the same rational-point group. -/
theorem IsTopologyCompatible.transport_torusIso {φ : RootFunctionFamily S G}
    (hφ : IsTopologyCompatible i φ) :
    IsTopologyCompatible j (RootFunctionFamily.transportEquiv σ (Iso.refl G) φ) := by
  unfold IsTopologyCompatible at hφ ⊢
  intro b hb
  obtain ⟨a, rfl⟩ := (characterLattice.congr σ).surjective b
  have hs : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom σ.hom ≫ j := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  have ha := (roots_mem_of_transport_iff σ (Iso.refl G) hs a).1 hb
  have hgroup := rootGroupPoints_eq_of_torusIso σ hσ a
  rw [hgroup]
  simpa only [rootFiltration_eq_of_torusIso σ hσ] using hφ a ha

end Topology

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B₁ B₂ : ValuationBuildingData G)
  (σ : B₁.S ≅ B₂.S)
  (hσ : B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i)
  (e : B₁.Apartment ≃ᵃ[ℝ] B₂.Apartment)

include hσ

/-- Actual family comparison at every corresponding apartment point transfers V7. -/
theorem isTopologyCompatible_of_family_comparison
    (hfamily : ∀ x : B₁.Apartment,
      (e x).val = RootFunctionFamily.transportEquiv σ (Iso.refl G) x.val)
    (hB : B₁.IsTopologyCompatible) : B₂.IsTopologyCompatible := by
  intro φ hφ
  obtain ⟨x, hx⟩ := e.surjective (⟨φ, hφ⟩ : B₂.Apartment)
  have h := (hB x.val x.mem).transport_torusIso σ hσ
  rw [← hfamily, hx] at h
  exact h

variable
  (hact : ∀ (n : normalizerPoints B₁.i) (x : B₁.Apartment),
    e (B₁.normalizerAction n x) =
      B₂.normalizerAction (normalizerEquivOfTorusIso B₁ B₂ σ hσ n) (e x))

include hact

/-- The entire actual normalizer-action image is conjugated by the apartment comparison. -/
theorem map_normalizerAction_range_of_comparison :
    B₁.normalizerAction.range.map (affineConjugation e).toMonoidHom =
      B₂.normalizerAction.range := by
  have hn (n : normalizerPoints B₁.i) :
      affineConjugation e (B₁.normalizerAction n) =
        B₂.normalizerAction (normalizerEquivOfTorusIso B₁ B₂ σ hσ n) := by
    apply AffineEquiv.ext
    intro y
    change e (B₁.normalizerAction n (e.symm y)) = _
    rw [hact, e.apply_symm_apply]
  ext g
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨normalizerEquivOfTorusIso B₁ B₂ σ hσ n, (hn n).symm⟩
  · rintro ⟨n, rfl⟩
    let m := (normalizerEquivOfTorusIso B₁ B₂ σ hσ).symm n
    refine ⟨B₁.normalizerAction m, ⟨m, rfl⟩, ?_⟩
    change affineConjugation e (B₁.normalizerAction m) = B₂.normalizerAction n
    simpa only [m, MulEquiv.apply_symm_apply] using hn m

/-- Affine conjugation restricts to an equivalence of the full actual action images. -/
def normalizerActionRangeEquivOfComparison :
    B₁.normalizerAction.range ≃* B₂.normalizerAction.range :=
  ((affineConjugation e).subgroupMap B₁.normalizerAction.range).trans
    (MulEquiv.subgroupCongr
      (map_normalizerAction_range_of_comparison B₁ B₂ σ hσ e hact))

@[simp] theorem normalizerActionRangeEquivOfComparison_apply
    (g : B₁.normalizerAction.range) :
    (normalizerActionRangeEquivOfComparison B₁ B₂ σ hσ e hact g).val =
      affineConjugation e g.val := rfl

omit hact in
/-- The natural quotient derivative transports precisely the full set of actual root forms. -/
theorem derivativeTransport_range_rootForm
    (hlinear : e.linear = translationSpaceTransportEquiv σ (Iso.refl G)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hσ)) :
    derivativeTransport e '' Set.range (rootForm B₁.i) = Set.range (rootForm B₂.i) := by
  let hs : B₁.i ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom σ.hom ≫ B₂.i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hσ
  have heq (a : relativeRoots B₁.i) :
      derivativeTransport e (rootForm B₁.i a) =
        rootForm B₂.i (relativeRootsTransportEquiv σ (Iso.refl G) hs a) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.linear.surjective w
    change rootForm B₁.i a (e.linear.symm (e.linear v)) = _
    rw [e.linear.symm_apply_apply, hlinear, rootForm_translationSpaceTransportEquiv]
  ext f
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨relativeRootsTransportEquiv σ (Iso.refl G) hs a, (heq a).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (relativeRootsTransportEquiv σ (Iso.refl G) hs).surjective b
    exact ⟨rootForm B₁.i a, ⟨a, rfl⟩, heq a⟩

/-- V7 and every AS2–AS5 field transfer under the full actual comparison hypotheses. -/
theorem satisfiesApartmentAxioms_of_comparison
    (hfamily : ∀ x : B₁.Apartment,
      (e x).val = RootFunctionFamily.transportEquiv σ (Iso.refl G) x.val)
    (hlinear : e.linear = translationSpaceTransportEquiv σ (Iso.refl G)
      (by simpa only [Iso.refl_hom, Category.comp_id] using hσ))
    (hext : transportedRoots e B₁.apartment.extendedAffineRoots =
      B₂.apartment.extendedAffineRoots)
    (hroots : transportedRoots e B₁.affineRoots = B₂.affineRoots)
    (hB : B₁.SatisfiesApartmentAxioms) : B₂.SatisfiesApartmentAxioms := by
  have hroots' : transportedRoots e B₁.apartment.affineRoots =
      B₂.apartment.affineRoots := hroots
  have hrange := map_normalizerAction_range_of_comparison B₁ B₂ σ hσ e hact
  have hforms := derivativeTransport_range_rootForm B₁ B₂ σ hσ e hlinear
  have hW := map_affineWeylGroup e B₁.affineRoots
  rw [hroots] at hW
  have hWe := map_extendedAffineWeylGroup e B₁.affineRoots
  rw [hroots] at hWe
  refine ⟨B₂.isOmegaCompatible,
    isTopologyCompatible_of_family_comparison B₁ B₂ σ hσ e hfamily hB.topologyCompatible,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hext]
    exact hB.isAffineRootSystem_extendedAffineRoots.transport e
  · rw [← hext, derivativeRoots_transportedRoots, hB.derivativeRoots_extendedAffineRoots]
    exact hforms
  · rw [← hroots']
    exact hB.isAffineRootSystem_affineRoots.transport e
  · rw [← hroots', derivativeRoots_transportedRoots, hB.derivativeRoots_affineRoots]
    exact hforms
  · intro ψ hψ
    rw [← hext] at hψ
    obtain ⟨φ, hφ, rfl⟩ := hψ
    rcases hB.mem_or_two_smul_mem φ hφ with h | h
    · apply Or.inl
      rw [← hroots']
      exact ⟨φ, h, rfl⟩
    · apply Or.inr
      rw [← hroots']
      exact ⟨(2 : ℝ) • φ, h, map_smul _ _ _⟩
  · rw [← hrange, ← hW]
    exact Subgroup.map_mono hB.affineWeylGroup_le_range
  · rw [← hrange, ← hWe]
    exact Subgroup.map_mono hB.range_le_extendedAffineWeylGroup
  · intro hsc
    rw [← hrange, ← hW, hB.range_eq_affineWeylGroup_of_isSimplyConnected hsc]
  · intro hqs had
    rw [← hrange, ← hWe,
      hB.range_eq_extendedAffineWeylGroup_of_isQuasiSplit_of_isAdjoint hqs had]

end ValuationBuildingData

end Langlands.Geometry.Building
