import Langlands.Geometry.Building.ChamberSimpleParahoricFactorization

/-! # Simple-wall factorization from chamber exchange -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Chamber exchange suffices for simple-wall factorization, without a Dynamic
ordered-product hypothesis. -/
theorem parahoric_subset_reflection_mul_wall_of_exchange
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} {psi : P.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {alpha : relativeRoots P.i} (hwall : psi.linear = rootForm P.i alpha)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots psi v) :
    (P.parahoric C : Set (rationalPoints G)) ⊆
      (P.parahoric (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
      (P.apartment.affineRootGroup alpha psi : Set (rationalPoints G)) := by
  classical
  have hC := hpsi.2.2.1
  obtain ⟨x, hx⟩ := hC.nonempty
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := P.isConnectedReductive.smooth
    infer_instance
  have hfinite := hT.finite_relativeRoots P.i
  have hspan := relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  obtain ⟨nu, hnu, hpos⟩ :=
    RelativeRoot.exists_genericCocharacter_pairing_pos P.i hT alpha.property.1
  have hcore := P.apartment.sharpFixer_subset_mul_of_mem_chamber
    hT hfinite hspan hrank hA.isAffineRootSystem_extendedAffineRoots
    hA.derivativeRoots_extendedAffineRoots hA.mem_or_two_smul_mem hC hx nu hnu
  have hpositive :=
    P.apartment.positiveChamberRootGroups_eq_sharpUnipotentPoints_of_core x nu hcore
  intro g hg
  obtain ⟨z, hz, b, hb, hzb⟩ := P.mem_parahoric_iff.mp hg
  have hbx : b ∈ P.apartment.sharpFixer {x} :=
    P.apartment.sharpFixer_anti (Set.singleton_subset_iff.mpr hx) hb
  obtain ⟨np, ⟨n, hn, p, hp, rfl⟩, c, hc, hnpc⟩ := hcore hbx
  have hpS := P.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x nu hp
  have hcpS : c⁻¹ * p * c ∈ P.apartment.sharpUnipotentPoints nu {x} := by
    refine ⟨?_, (P.apartment.sharpFixer {x}).mul_mem
        ((P.apartment.sharpFixer {x}).mul_mem
        ((P.apartment.sharpFixer {x}).inv_mem hc.2) hpS.2) hc.2⟩
    change c⁻¹ * p * c ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ P.i)).carrier (Over.mk (𝟙 _))
    simpa only [inv_inv] using
      KPApartmentData.centralizer_conj_mem_dynamicUnipotent nu
        ((centralizerPoints P.i).inv_mem hc.1) hpS.1
  have hcp : c⁻¹ * p * c ∈
      (⨆ a : positiveRelativeRoots P.i nu,
        P.apartment.chamberRootGroup x false a : Subgroup (rationalPoints G)) := by
    rw [hpositive]
    exact hcpS
  have hcZ : c ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
    rw [← P.centralizer_inf_parahoric_eq_of_rankOneFactorization hA hrank hZ
      (Set.singleton_nonempty x)]
    exact ⟨hc.1, P.sharpFixer_le_parahoric {x} hc.2⟩
  let R := AffineRootSystem.affineReflection psi hv.1 '' C
  have hnR : n ∈ P.parahoric R :=
    P.sharpFixer_le_parahoric R
      (P.apartment.negativeChamberRootGroups_le_reflection
        hA.isAffineRootSystem_affineRoots hA.mem_or_two_smul_mem
        hpsi hwall hpos hx hv hn)
  have hzR : rationalPoints.map P.centralizer.j z ∈ P.parahoric R :=
    P.map_centralizerZero_le_parahoric R ⟨z, hz, rfl⟩
  have hcR : c ∈ P.parahoric R := P.map_centralizerZero_le_parahoric R hcZ
  obtain ⟨w, hw, u, hu, hwu⟩ :=
    P.apartment.positiveChamberRootGroups_subset_reflection_mul_wall hT hfinite
      hA.isAffineRootSystem_affineRoots hA.isAffineRootSystem_extendedAffineRoots
      hA.derivativeRoots_extendedAffineRoots hA.mem_or_two_smul_mem
      hpsi hwall hpos hx hv hcp
  change w * u = _ at hwu
  change n * p * c = b at hnpc
  refine ⟨rationalPoints.map P.centralizer.j z * n * c * w,
    (P.parahoric R).mul_mem
      ((P.parahoric R).mul_mem ((P.parahoric R).mul_mem hzR hnR) hcR)
      (P.sharpFixer_le_parahoric R hw), u, hu, ?_⟩
  calc
    rationalPoints.map P.centralizer.j z * n * c * w * u =
        rationalPoints.map P.centralizer.j z * (n * c * (w * u)) := by group
    _ = rationalPoints.map P.centralizer.j z * (n * c * (c⁻¹ * p * c)) := by rw [hwu]
    _ = rationalPoints.map P.centralizer.j z * (n * p * c) := by group
    _ = g := by rw [hnpc]; exact hzb

/-- The exact membership conclusion required for a chamber-simple wall. -/
theorem simpleFactorization_of_exchange
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} {psi : P.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {alpha : relativeRoots P.i} (hwall : psi.linear = rootForm P.i alpha)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots psi v)
    {g : rationalPoints G} (hg : g ∈ P.parahoric C) :
    ∃ b' ∈ P.parahoric (AffineRootSystem.affineReflection psi hv.1 '' C),
      ∃ u ∈ P.apartment.affineRootGroup alpha psi, g = b' * u := by
  obtain ⟨b', hb', u, hu, hbu⟩ :=
    P.parahoric_subset_reflection_mul_wall_of_exchange hA hrank hZ hpsi hwall hv hg
  exact ⟨b', hb', u, hu, hbu.symm⟩

/-- The ambient identity inclusion supplied by chamber exchange. -/
def chamberSimpleParahoricProductInclusion_of_exchange
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} {psi : P.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {alpha : relativeRoots P.i} (hwall : psi.linear = rootForm P.i alpha)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots psi v) :
    P.parahoric C →
      ↥((P.parahoric (AffineRootSystem.affineReflection psi hv.1 '' C) :
          Set (rationalPoints G)) *
        (P.apartment.affineRootGroup alpha psi : Set (rationalPoints G))) :=
  fun g => ⟨g, P.parahoric_subset_reflection_mul_wall_of_exchange
    hA hrank hZ hpsi hwall hv g.property⟩

end Langlands.Geometry.Building.ParahoricBuildingData
