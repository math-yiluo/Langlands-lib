import Langlands.Geometry.Building.ChamberWallProductAssembly
import Langlands.Geometry.Building.ChamberIwahoriLocalReduction
import Langlands.GroupScheme.Rational.RootFactorPairExistenceReduction

/-! # Full parahoric factorization across a chamber-simple wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The generated negative chamber subgroup lies in the reflected sharp fixer
when the wall derivative is positive on the chosen cocharacter. -/
theorem negativeChamberRootGroups_le_reflection
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {alpha : relativeRoots i} (hwall : psi.linear = rootForm i alpha)
    {nu : cocharacterLattice S} (hpos : 0 < latticePairing S alpha nu)
    {x : D.Apartment} (hx : x ∈ C)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    (⨆ b : positiveRelativeRoots i (-nu), D.chamberRootGroup x false b :
      Subgroup (rationalPoints G)) ≤
      D.sharpFixer (AffineRootSystem.affineReflection psi hv.1 '' C) := by
  refine iSup_le fun b g hg => ?_
  let beta : relativeRoots i := ⟨b, b.property.1⟩
  have hfix : D.rootFixer beta C = D.filtration x b 0 :=
    (D.rootFixer_eq_filtration_of_isFacet hAS4 hpsi.2.2.1.isFacet hx b.property.1).1
  have hroot : g ∈ D.rootFixer beta C := hfix.symm ▸ hg
  have hb : latticePairing S beta nu < 0 := by simpa [beta] using b.property.2
  have hrefl : g ∈ D.rootFixer beta
      (AffineRootSystem.affineReflection psi hv.1 '' C) :=
    D.rootFixer_le_reflection_of_pairing_neg hAS4 hpsi hsys hwall hpos hb hv hroot
  exact D.rootFixer_le_sharpFixer beta _ hrefl

end KPApartmentData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The existing local algebraic inputs imply full chamber-simple parahoric
factorization; no separate chamber-decomposition premise is needed. -/
theorem parahoric_subset_reflection_mul_wall_of_rankOneFactorization
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
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
  obtain ⟨nu, hnu, hpos⟩ :=
    RelativeRoot.exists_genericCocharacter_pairing_pos P.i hT alpha.property.1
  obtain ⟨nneg, aneg, hineg, hrneg⟩ :=
    RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots P.i (-nu) hfinite
  obtain ⟨npos, apos, hipos, hrpos⟩ :=
    RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots P.i nu hfinite
  obtain ⟨_, hfull, _⟩ :=
    P.chamberIwahoriDecomposition_of_rankOneFactorization hrank hZ hprod hA C x nu hC hx hnu
  rcases hfull with ⟨_, _, _, _, _, _, hblocks⟩
  have hrange := (hblocks false nneg npos aneg apos hineg hrneg hipos hrpos).2.2.2.2.2
  intro g hg
  obtain ⟨t, rfl⟩ := (show g ∈ Set.range
      (P.orderedIwahoriChamberProduct x false aneg apos) by rw [hrange]; exact hg)
  have hn : P.apartment.orderedChamberBlockProduct x false aneg t.1 ∈
      (⨆ b : positiveRelativeRoots P.i (-nu),
        P.apartment.chamberRootGroup x false b : Subgroup (rationalPoints G)) := by
    exact (P.apartment.range_orderedPositiveChamberBlockProduct_eq_iSup
      hA.isAffineRootSystem_extendedAffineRoots hA.derivativeRoots_extendedAffineRoots
      x false (-nu) aneg hrneg).subset (Set.mem_range_self t.1)
  have hp : P.apartment.orderedChamberBlockProduct x false apos t.2.2 ∈
      (⨆ b : positiveRelativeRoots P.i nu,
        P.apartment.chamberRootGroup x false b : Subgroup (rationalPoints G)) := by
    exact (P.apartment.range_orderedPositiveChamberBlockProduct_eq_iSup
      hA.isAffineRootSystem_extendedAffineRoots hA.derivativeRoots_extendedAffineRoots
      x false nu apos hrpos).subset (Set.mem_range_self t.2.2)
  let R := AffineRootSystem.affineReflection psi hv.1 '' C
  have hnR : P.apartment.orderedChamberBlockProduct x false aneg t.1 ∈ P.parahoric R :=
    P.sharpFixer_le_parahoric R
      (P.apartment.negativeChamberRootGroups_le_reflection hA.isAffineRootSystem_affineRoots
        hA.mem_or_two_smul_mem hpsi hwall hpos hx hv hn)
  have hzR : rationalPoints.map P.centralizer.j
      (t.2.1 : rationalPoints P.centralizer.Z) ∈ P.parahoric R :=
    P.map_centralizerZero_le_parahoric R (Subgroup.mem_map.mpr ⟨t.2.1, t.2.1.property, rfl⟩)
  obtain ⟨w, hw, u, hu, hwu⟩ :=
    P.apartment.positiveChamberRootGroups_subset_reflection_mul_wall hT hfinite
      hA.isAffineRootSystem_affineRoots hA.isAffineRootSystem_extendedAffineRoots
      hA.derivativeRoots_extendedAffineRoots hA.mem_or_two_smul_mem hpsi hwall hpos hx hv hp
  change w * u = _ at hwu
  refine ⟨P.apartment.orderedChamberBlockProduct x false aneg t.1 *
      rationalPoints.map P.centralizer.j (t.2.1 : rationalPoints P.centralizer.Z) * w,
    (P.parahoric R).mul_mem ((P.parahoric R).mul_mem hnR hzR)
      (P.sharpFixer_le_parahoric R hw), u, hu, ?_⟩
  change _ * _ * w * u = _ * _ * _
  rw [mul_assoc _ w u, hwu]

/-- Membership form of the full chamber-simple factorization. -/
theorem simpleFactorization_of_rankOneFactorization
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} {psi : P.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {alpha : relativeRoots P.i} (hwall : psi.linear = rootForm P.i alpha)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots psi v)
    {g : rationalPoints G} (hg : g ∈ P.parahoric C) :
    ∃ b' ∈ P.parahoric (AffineRootSystem.affineReflection psi hv.1 '' C),
      ∃ u ∈ P.apartment.affineRootGroup alpha psi, g = b' * u := by
  obtain ⟨b', hb', u, hu, hbu⟩ :=
    P.parahoric_subset_reflection_mul_wall_of_rankOneFactorization hA hrank hZ hprod
      hpsi hwall hv hg
  exact ⟨b', hb', u, hu, hbu.symm⟩

/-- The ambient identity inclusion into the reflected parahoric times wall group. -/
def chamberSimpleParahoricProductInclusion_of_rankOneFactorization
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} {psi : P.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {alpha : relativeRoots P.i} (hwall : psi.linear = rootForm P.i alpha)
    {v : TranslationSpace P.i} (hv : AffineRootSystem.IsCoroot P.affineRoots psi v) :
    P.parahoric C →
      ↥((P.parahoric (AffineRootSystem.affineReflection psi hv.1 '' C) :
          Set (rationalPoints G)) *
        (P.apartment.affineRootGroup alpha psi : Set (rationalPoints G))) :=
  fun g => ⟨g, P.parahoric_subset_reflection_mul_wall_of_rankOneFactorization
    hA hrank hZ hprod hpsi hwall hv g.property⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
