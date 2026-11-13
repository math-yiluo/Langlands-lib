import Langlands.Geometry.Building.ValuationBuildingPullbackComparison
import Langlands.Geometry.Building.ValuationBuildingSameGroupComparison
import Langlands.Geometry.Building.DerivedCentralizer
import Langlands.Geometry.Building.CentralIsogenyCentralizer
import Langlands.Geometry.Building.CentralizerDatumConstruction
import Langlands.BruhatTits.Cartan.CentralizerValuationComparisonProof
import Langlands.GroupScheme.Derived.MaximalSplitTorusProof
import Langlands.GroupScheme.Derived.CentralSplitTorusProductProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.SplitCentralEmbedding
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductProof
import Langlands.GroupScheme.Rational.DerivedCoverNormalizerLift
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusProof

/-!
# Reduced buildings of the derived subgroup and of its simply connected cover

For a derived subgroup `d : G_der → G` and a simply connected cover `π : G_sc → G_der`, the
reduced building of any valuation-building datum of `G_der` (resp. `G_sc`) is identified with
that of any valuation-building datum of `G` by an equivariant building isomorphism along
`d` (resp. `π ≫ d`).

The source apartment class is the derived pullback of the target class (followed by the
central-isogeny pullback through `π`), with the structural tori of
`derivedMaximalSplitTorus` (resp. `simplyConnectedDerivedCoverSplitTorus`); KP Fact 2.6.22
(`simplyConnectedCentralizerProduct`) gives `G(F) = (π ≫ d)(G_sc(F)) · N(F)`, and
`DerivedCoverNormalizerLift.mem_normalizerPoints` pulls the normalizer back.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

namespace Langlands.Geometry.Building.ValuationBuildingData

theorem map_comp_rationalPoints {k : Type u} [Field k]
    {C D G : GroupScheme (Spec (CommRingCat.of k))} (π : C ⟶ D) (d : D ⟶ G) :
    (rationalPoints.map d).comp (rationalPoints.map π) = rationalPoints.map (π ≫ d) := by
  ext y
  simp only [MonoidHom.comp_apply, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- KP Fact 2.6.22 in the form `G(F) = (π ≫ d)(G_sc(F)) · N(F)`. -/
theorem exists_eq_map_mul_normalizer {G D C : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] (B : ValuationBuildingData G) (d : D ⟶ G) (π : C ⟶ D)
    (hdπ : IsSimplyConnectedDerivedCover d π) (g : rationalPoints G) :
    ∃ (c : rationalPoints C) (n : normalizerPoints B.i),
      g = rationalPoints.map (π ≫ d) c * n := by
  obtain ⟨c, z, hz⟩ := simplyConnectedCentralizerProduct F B.S G B.centralizer.Z C D B.i
    B.centralizer.j d π hdπ B.isMaximalSplitTorus B.centralizer.isRepresentedBy g
  exact ⟨c, ⟨_, centralizerPoints_le_normalizerPoints B.i
    (map_mem_centralizerPoints B.centralizer.isRepresentedBy z)⟩, hz⟩

/-- **The derived-subgroup comparison.** For a derived subgroup `d : G_der → G`, any
valuation-building data `B` of `G_der` and `B'` of `G` have reduced buildings identified by an
equivariant building isomorphism along `d`. -/
theorem exists_isEquivariantBuildingIso_derivedSubgroup
    {G Gder : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [IsAffineHom Gder.X.hom] (d : Gder ⟶ G) (hd : IsDerivedSubgroup d)
    (B : ValuationBuildingData Gder) (B' : ValuationBuildingData G) :
    ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
      IsEquivariantBuildingIso B B' (rationalPoints.map d) Φ := by
  have hG := B'.isConnectedReductive
  have : Smooth G.X.hom := hG.smooth
  have : Smooth Gder.X.hom := B.isConnectedReductive.smooth
  have : Mono d.hom.hom.left := by
    have : IsClosedImmersion d.hom.hom.left := hd.1
    infer_instance
  obtain ⟨T, j, e, hj, he, h⟩ :=
    derivedMaximalSplitTorus F G Gder d hG hd B'.S B'.i B'.isMaximalSplitTorus
  obtain ⟨A, a, ha⟩ := (splitComponentStatement F G hG).1
  obtain ⟨c, hca, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus B'.isMaximalSplitTorus
  have hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c) :=
    derivedCentralSplitTorusProduct F G Gder d hG hd B'.S T A B'.i j e a c
      B'.isMaximalSplitTorus hj he h ha hca
  have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.flat
  have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.surjective
  have : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hj
  have hA : IsSplitTorus A.toGrp := ha.isCentralSplitTorus.1.1
  have hc : IsCentral (CommGroupScheme.groupHom c ≫ B'.i) := by
    rw [hca]
    exact ha.isCentralSplitTorus.2
  obtain ⟨C, π, hπ⟩ :=
    simplyConnectedCoverExistence F Gder (derivedSubgroupSemisimple F G Gder d hG hd)
  have hdπ : IsSimplyConnectedDerivedCover d π := ⟨hG, hd, hπ⟩
  let CD := CentralizerDatum.ofValuationComparison Cartan.centralizerValuationComparison
    B.isConnectedReductive j hj
  let BX : ValuationBuildingData Gder :=
    { isConnectedReductive := B.isConnectedReductive
      S := T
      i := j
      isMaximalSplitTorus := hj
      apartment := B'.apartment.derivedPullback e c j B'.i d hd h hj.1.1
        B'.isMaximalSplitTorus.1.1 hA hc B'.isMaximalSplitTorus
      centralizer := CD
      isOmegaCompatible := B'.isOmegaCompatible.derivedPullback e c j B'.i d h hj.1.1 hA hc CD
        B'.centralizer hd B'.isMaximalSplitTorus.1.1 B'.isMaximalSplitTorus }
  let t : BX.apartment.Transfer B'.apartment (rationalPoints.map d) :=
    { toComparison := B'.apartment.derivedComparison e c j B'.i d hd h hj.1.1
        B'.isMaximalSplitTorus.1.1 hA hc B'.isMaximalSplitTorus
      mem_normalizerPoints_of_map := fun g hg =>
        DerivedCoverNormalizerLift.mem_normalizerPoints (𝟙 Gder) d (isCentralIsogeny_of_isIso _)
          j hj B'.i e (by rw [Category.id_comp]; exact h) g (by rwa [Category.id_comp])
      exists_mul := fun g => by
        obtain ⟨x, n, hx⟩ := exists_eq_map_mul_normalizer B' d π hdπ g
        refine ⟨rationalPoints.map π x, n, ?_⟩
        rw [hx, ← map_comp_rationalPoints]
        rfl }
  exact (Transfer.isEquivariantBuildingIso t).exists_resource

/-- **The simply-connected-cover comparison.** For a derived subgroup `d : G_der → G` and a
simply connected cover `π : G_sc → G_der`, any valuation-building data `B` of `G_sc` and `B'`
of `G` have reduced buildings identified by an equivariant building isomorphism along
`π ≫ d`. -/
theorem exists_isEquivariantBuildingIso_simplyConnectedCover
    {G Gder Gsc : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [IsAffineHom Gsc.X.hom] (d : Gder ⟶ G) (π : Gsc ⟶ Gder)
    (hdπ : IsSimplyConnectedDerivedCover d π)
    (B : ValuationBuildingData Gsc) (B' : ValuationBuildingData G) :
    ∃ Φ : B.ReducedBuilding ≃ B'.ReducedBuilding,
      IsEquivariantBuildingIso B B' (rationalPoints.map (π ≫ d)) Φ := by
  have hG := B'.isConnectedReductive
  have hDred := hdπ.isSimplyConnectedCover.isSemisimple.isConnectedReductive
  have hπc := hdπ.isSimplyConnectedCover.isCentralIsogeny
  have hd := hdπ.isDerivedSubgroup
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom Gder.X.hom := hDred.isAffineHom
  have : Smooth Gder.X.hom := hDred.smooth
  have : Smooth Gsc.X.hom := B.isConnectedReductive.smooth
  have : Mono d.hom.hom.left := by
    have : IsClosedImmersion d.hom.hom.left := hd.1
    infer_instance
  obtain ⟨T, j, e, hj, he, h, U, k, f, hk, h', hf, hcomp, -⟩ :=
    simplyConnectedDerivedCoverSplitTorus F G Gder Gsc d π hdπ B'.S B'.i B'.isMaximalSplitTorus
  obtain ⟨A, a, ha⟩ := (splitComponentStatement F G hG).1
  obtain ⟨c, hca, -, -⟩ := ha.exists_commFactor_of_isMaximalSplitTorus B'.isMaximalSplitTorus
  have hp : IsCentralIsogeny (RelativeRoot.centralComplementProduct e c) :=
    derivedCentralSplitTorusProduct F G Gder d hG hd B'.S T A B'.i j e a c
      B'.isMaximalSplitTorus hj he h ha hca
  have : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.flat
  have : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left := hp.surjective
  have : Mono j.hom.hom.left := mono_of_isMaximalSplitTorus hj
  have : Mono k.hom.hom.left := mono_of_isMaximalSplitTorus hk
  have hA : IsSplitTorus A.toGrp := ha.isCentralSplitTorus.1.1
  have hc : IsCentral (CommGroupScheme.groupHom c ≫ B'.i) := by
    rw [hca]
    exact ha.isCentralSplitTorus.2
  let CD := CentralizerDatum.ofValuationComparison Cartan.centralizerValuationComparison hDred j hj
  let CC := CentralizerDatum.ofValuationComparison Cartan.centralizerValuationComparison
    B.isConnectedReductive k hk
  let X := B'.apartment.derivedPullback e c j B'.i d hd h hj.1.1
    B'.isMaximalSplitTorus.1.1 hA hc B'.isMaximalSplitTorus
  have hX : X.IsOmegaCompatible CD :=
    B'.isOmegaCompatible.derivedPullback e c j B'.i d h hj.1.1 hA hc CD
      B'.centralizer hd B'.isMaximalSplitTorus.1.1 B'.isMaximalSplitTorus
  let BY : ValuationBuildingData Gsc :=
    { isConnectedReductive := B.isConnectedReductive
      S := U
      i := k
      isMaximalSplitTorus := hk
      apartment := X.centralIsogenyPullback π hπc hk.1.1 hj.1.1 f h' hf.isIsogeny
      centralizer := CC
      isOmegaCompatible :=
        hX.centralIsogenyPullback π f h' hf.isIsogeny CC CD hπc hk.1.1 hj.1.1 }
  let t : BY.apartment.Transfer B'.apartment (rationalPoints.map (π ≫ d)) :=
    { toComparison :=
        ((X.centralIsogenyComparison π hπc hk.1.1 hj.1.1 f h' hf.isIsogeny).trans
          (B'.apartment.derivedComparison e c j B'.i d hd h hj.1.1
            B'.isMaximalSplitTorus.1.1 hA hc B'.isMaximalSplitTorus)).congrHom
          (map_comp_rationalPoints π d)
      mem_normalizerPoints_of_map := fun g hg =>
        DerivedCoverNormalizerLift.mem_normalizerPoints π d hπc k hk B'.i (f ≫ e) hcomp g hg
      exists_mul := fun g => exists_eq_map_mul_normalizer B' d π hdπ g }
  exact (Transfer.isEquivariantBuildingIso t).exists_resource

end Langlands.Geometry.Building.ValuationBuildingData
