import Langlands.Geometry.Building.ChamberIwahoriLocalReduction

/-! # Chamber decompositions and saturation from local point injectivity -/

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

/-- Rational-point injectivity of the actual unfiltered root product restricts
to the existing chamber block maps at either depth and every apartment point. -/
theorem orderedChamberBlockInjectivity_of_orderedRootPointInjectivity
    (hinj : RelativeRoot.OrderedRootPointInjectivity i) (x : D.Apartment) :
    D.OrderedChamberBlockInjectivity x := by
  intro strict ν n a ha hrange
  have hroot (r : Fin n) : a r ∈ relativeRoots i :=
    (show a r ∈ RelativeRoot.indivisiblePositiveRoots i ν from
      hrange ▸ Set.mem_range_self r).1.1
  let lift (t : ∀ r, D.chamberRootBlock x strict (a r)) :
      ∀ r, rootGroupPoints i (a r) := fun r =>
    ⟨t r, D.chamberRootBlock_subset_rootGroupPoints x strict (hroot r) (t r).property⟩
  intro s t hst
  have hcoords : lift s = lift t := hinj ν n a ha hrange hst
  funext r
  exact Subtype.ext (congrArg (fun z => (z r : rationalPoints G)) hcoords)

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The full sharp chamber and facet statement needs only actual rank-one
factorization and root-product injectivity for this one torus embedding. -/
theorem chamberSharpDecomposition_of_localRootInjectivity
    (hrank : RelativeRoot.HasRankOneFactorization B.i)
    (hinj : RelativeRoot.OrderedRootPointInjectivity B.i) :
    B.ChamberSharpDecompositionStatement := by
  intro hD C x ν hC hx hν
  have hG := B.isConnectedReductive
  have hi := B.isMaximalSplitTorus
  have hT : IsSplitTorus B.S.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  have hfinite := hT.finite_relativeRoots B.i
  have hspan := relativeRootsRestrictedCharactersSpan F G hG B.S B.i hi
  have hsharp := B.apartment.chamberSharpConclusion_of_core_of_blockInjectivity
    hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
    hD.mem_or_two_smul_mem hC hx
    (B.apartment.orderedChamberBlockInjectivity_of_orderedRootPointInjectivity hinj x)
    (fun mu hmu => KPApartmentData.sharpFixer_subset_mul_of_mem_chamber hT hfinite hspan hrank
      hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
      hD.mem_or_two_smul_mem hC hx mu hmu) ν hν
  refine ⟨hsharp, fun Fa hFC hPos => ?_⟩
  exact B.apartment.chamberSharpFacetConclusion_of_chamberSharpConclusion
    hD.mem_or_two_smul_mem hD.isAffineRootSystem_affineRoots hC hFC hPos hx hsharp

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The existing full chamber decomposition follows from three inputs for the
actual datum, without a global ordered-product premise. -/
theorem chamberIwahoriDecomposition_of_localRootInjectivity
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i) :
    P.ChamberIwahoriDecompositionStatement :=
  chamberIwahoriDecomposition_of_sharp
    (P.toValuationBuildingData.chamberSharpDecomposition_of_localRootInjectivity hrank hinj)
    (P.centralizerParahoricIntersection_of_rankOneFactorization hrank hZ)

/-- Local actual-root injectivity suffices for the restricted-normalizer
intersection equality once actual rank-one and cover comparison hold. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_of_localRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity
    hP hrank hinj (P.chamberIwahoriDecomposition_of_localRootInjectivity hrank hZ hinj) hC

/-- The local three-input reduction retains the exact membership quantifiers
of the published chamber-conjugate intersection statement. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_of_localRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent_of_orderedRootInjectivity
    hP hrank hinj (P.chamberIwahoriDecomposition_of_localRootInjectivity hrank hZ hinj) hC hg

/-- The actual restricted-normalizer chamber intersection is identified with
the centralizer-zero image through the identity on ambient rational points. -/
def chamberConjugateParahoricEquivCentralizerZeroImage_of_localRootInjectivity
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) ≃*
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr
    (P.iInf_parahoric_normalizerZeroComponent_eq_of_localRootInjectivity
      hP hrank hZ hinj hC)

/-- The equivalence preserves the ambient rational point. -/
@[simp] theorem chamberConjugateParahoricEquivCentralizerZeroImage_of_localRootInjectivity_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hinj : RelativeRoot.OrderedRootPointInjectivity P.i)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (g : ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C))) :
    ((P.chamberConjugateParahoricEquivCentralizerZeroImage_of_localRootInjectivity
      hP hrank hZ hinj hC g :
        P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building
