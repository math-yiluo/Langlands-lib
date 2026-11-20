import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourcePresentation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylFibers
import Langlands.Representation.Plancherel.RationalPlancherelConstantConjugation

/-! # Source scalars under semistandard Weyl conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.DynamicUnipotentContainment Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceConstants

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}

open RationalDynamicSource in
private theorem image_roots_with_pairing [Mono i.hom.hom.left]
    (n : normalizerPoints i) (zeta : cocharacterLattice S) (condition : ℤ → Prop) :
    weylAction i n '' {alpha | alpha ∈ relativeRoots i ∧ condition (latticePairing S alpha zeta)} =
      {alpha | alpha ∈ relativeRoots i ∧
        condition (latticePairing S alpha (cocharacterAut (normalizingAut i n) zeta))} := by
  ext alpha
  obtain ⟨beta, rfl⟩ := (weylAction i n).surjective alpha
  rw [(weylAction i n).injective.mem_set_image]
  change (beta ∈ relativeRoots i ∧ condition (latticePairing S beta zeta)) ↔
    (weylAction i n beta ∈ relativeRoots i ∧
      condition (latticePairing S (weylAction i n beta) (cocharacterAut (normalizingAut i n) zeta)))
  rw [relativeRoots_eq_roots, weylAction_mem_roots_iff]
  change (beta ∈ roots i ∧ condition (latticePairing S beta zeta)) ↔
    (beta ∈ roots i ∧ condition (latticePairing S (characterAut (normalizingAut i n) beta)
      (cocharacterAut (normalizingAut i n) zeta)))
  rw [latticePairing_characterAut_cocharacterAut]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalDynamicSource in
/-- With the torus fixed, the normalizer permutes the actual rank-one factors.
A lift in the compact preserves the Haar normalization at each factor. -/
theorem rankOneGammaProduct_eq_of_normalizer_mem_compact [Mono i.hom.hom.left]
    (n : normalizerPoints i) (zeta : cocharacterLattice S)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hn : (n : rationalPoints G) ∈ K) :
    rankOneGammaProduct i (cocharacterAut (normalizingAut i n) zeta) K hK =
      rankOneGammaProduct i zeta K hK := by
  let e := cocharacterAut (normalizingAut i n)
  let move (N : Submodule ℤ (cocharacterLattice S)) := N.map e.toLinearMap
  have hpos : weylAction i n '' positiveRelativeRoots i zeta = positiveRelativeRoots i (e zeta) :=
    image_roots_with_pairing n zeta (0 < ·)
  have hlevi : weylAction i n '' leviRelativeRoots i zeta = leviRelativeRoots i (e zeta) :=
    image_roots_with_pairing n zeta (· = 0)
  have hroots (beta : characterLattice S) :
      weylAction i n '' insert beta (leviRelativeRoots i zeta) =
        insert (weylAction i n beta) (leviRelativeRoots i (e zeta)) := by
    rw [Set.image_insert_eq, hlevi]
  have hmove (beta : characterLattice S) : move (rankOneCocharacters i zeta beta) =
      rankOneCocharacters i (e zeta) (weylAction i n beta) := by
    change (rankOneCocharacters i zeta beta).map e.toLinearMap = _
    ext alpha
    obtain ⟨xi, rfl⟩ := e.surjective alpha
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    exact (cocharacterAut_mem_annihilator_iff (normalizingAut i n) (hroots beta) xi).symm
  have hset : move '' rankOneCocharacterSet i zeta = rankOneCocharacterSet i (e zeta) := by
    rw [rankOneCocharacterSet, rankOneCocharacterSet, ← hpos, Set.image_image, Set.image_image]
    exact Set.image_congr fun beta _ => hmove beta
  unfold rankOneGammaProduct
  change (∏ᶠ N ∈ rankOneCocharacterSet i (e zeta), rankOneGamma i (e zeta) K hK N) = _
  rw [← hset, finprod_mem_image (Submodule.map_injective_of_injective e.injective).injOn]
  apply finprod_mem_congr rfl
  rintro _ ⟨beta, _, rfl⟩
  change rankOneGamma i (e zeta) K hK (move (rankOneCocharacters i zeta beta)) = _
  rw [hmove beta]
  unfold rankOneGamma
  have hchi : CommGroupScheme.groupHom (e zeta) ≫ i =
      (CommGroupScheme.groupHom zeta ≫ i) ≫ (G.innerIso (n : rationalPoints G)).hom :=
    groupHom_cocharacterAut_comp i n zeta
  rw [hchi]
  let g : rationalPoints G := n
  have hcompact (x : rationalPoints G) : g * x * g⁻¹ ∈ K ↔ x ∈ K := by
    simpa only [conjugateCompact_eq_self g K hn] using mem_conjugateCompact g x K
  have htransport : cocharacterSubmoduleCentralizer i (rankOneCocharacters i zeta beta) =
      (cocharacterSubmoduleCentralizer i (rankOneCocharacters i (e zeta) (weylAction i n beta))).comap
        (G.innerIso g).hom := by
    simpa only [cocharacterSubmoduleCentralizer_rankOneCocharacters] using
      cocharacterAnnihilatorCentralizer_eq_comap i n (hroots beta)
  refine leviGamma_eq_of_conjugation (CommGroupScheme.groupHom zeta ≫ i) g K K hK hK
    _ _ _ _ hcompact fun x => ?_
  rw [htransport, SubgroupFunctor.mem_comap, comp_innerIso_hom, constantPoint_rationalPoint]

variable {hG : IsConnectedReductive G} (hi : IsMaximalSplitTorus i)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})

/-- Evaluate the source synthesis weight on an intrinsic triple, using the
actual parabolic fiber and the literal ambient and Levi Weyl groups. -/
def unquotientedWeightAtIndex (p : SemistandardSpectralIndex i) : ℝ :=
  unquotientedWeight (CocharacterPresentation.ofCoverage hG hD hi p) K hK

theorem unquotientedWeightAtIndex_eq {p : SemistandardSpectralIndex i}
    (r : CocharacterPresentation hG p) :
    unquotientedWeightAtIndex (hG := hG) hi K hK hD p = unquotientedWeight r K hK := by
  let s := CocharacterPresentation.ofCoverage hG hD hi p
  obtain ⟨hg, _, hc⟩ := eq_of_presentation hi K hK s r
  have hgReal : gammaReal s K hK = gammaReal r K hK := congrArg ENNReal.toReal hg
  have hcReal : cReal s K hK = cReal r K hK := congrArg ENNReal.toReal hc
  change unquotientedWeight s K hK = _
  unfold unquotientedWeight
  rw [hgReal, hcReal]

/-- Conjugating the entire triple by a normalizer lift in the chosen compact
preserves both index-level constants. -/
theorem eq_at_normalizerConjugateIndex (p : SemistandardSpectralIndex i)
    (n : normalizerPoints i) (hn : (n : rationalPoints G) ∈ K) :
    gammaAtIndex (hG := hG) hi K hK hD (normalizerConjugateIndex hG hi hD n p) =
      gammaAtIndex (hG := hG) hi K hK hD p ∧
    cAtIndex (hG := hG) hi K hK hD (normalizerConjugateIndex hG hi hD n p) =
      cAtIndex (hG := hG) hi K hK hD p := by
  let := hi.isSplitSubtorus.mono
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  let s : CocharacterPresentation hG (normalizerConjugateIndex hG hi hD n p) :=
    ⟨cocharacterAut (normalizingAut i n) r.cocharacter, rfl⟩
  rw [gammaAtIndex_eq hi K hK hD s, cAtIndex_eq hi K hK hD s]
  have he : s.hom = r.hom ≫ (G.innerIso (n : rationalPoints G)).hom :=
    groupHom_cocharacterAut_comp i n r.cocharacter
  have hgamma : gamma s K hK = gamma r K hK := by
    unfold gamma
    rw [he]
    exact RationalDynamicSource.gamma_conjugate_of_mem_compact r.hom (n : rationalPoints G) K hK hn
  refine ⟨hgamma, ?_⟩
  change (gamma s K hK)⁻¹ * RationalDynamicSource.rankOneGammaProduct i s.cocharacter K hK =
    (gamma r K hK)⁻¹ * RationalDynamicSource.rankOneGammaProduct i r.cocharacter K hK
  rw [hgamma]
  exact congrArg _ (rankOneGammaProduct_eq_of_normalizer_mem_compact n r.cocharacter K hK hn)

/-- A Weyl element transports the index-level constants to its literal conjugate
parabolic. The compact Weyl-representative property fixes the normalization. -/
theorem eq_at_weylParabolicFiber
    (hW : HasWeylRepresentatives i (K : Subgroup (rationalPoints G)))
    (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
    (w : relativeWeylGroup i) (p : SemistandardSpectralParabolicFiber i M) :
    gammaAtIndex (hG := hG) hi K hK hD (weylParabolicFiberEquiv hG hi hD M hM w p).val =
      gammaAtIndex (hG := hG) hi K hK hD p.val ∧
    cAtIndex (hG := hG) hi K hK hD (weylParabolicFiberEquiv hG hi hD M hM w p).val =
      cAtIndex (hG := hG) hi K hK hD p.val := by
  obtain ⟨n, hn, rfl⟩ := hW w
  rw [weylParabolicFiberEquiv_mk]
  exact eq_at_normalizerConjugateIndex hi K hK hD p.val n hn

/-- Transport to any parabolic over the conjugate Levi uses exactly the
common-Levi source-normalization proposition. -/
theorem eq_at_weylConjugateLevi (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (hSpecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (p q : SemistandardSpectralIndex i) (hM : torusCentralizer i ≤ p.toLevi.val)
    (w : relativeWeylGroup i) (hq : q.levi = (weylConjugateLevi hG hi hD p.toLevi hM w).val) :
    gammaAtIndex (hG := hG) hi K hK hD q = gammaAtIndex (hG := hG) hi K hK hD p ∧
    cAtIndex (hG := hG) hi K hK hD q = cAtIndex (hG := hG) hi K hK hD p := by
  let p' := weylParabolicFiberEquiv hG hi hD p.toLevi hM w ⟨p, rfl⟩
  have hp' := eq_at_weylParabolicFiber (hG := hG) hi K hK hD hSpecial.2.2.1 p.toLevi hM w ⟨p, rfl⟩
  have hsame := hI hi nu hnu K hK hSpecial q p'.val
    (CocharacterPresentation.ofCoverage hG hD hi q)
    (CocharacterPresentation.ofCoverage hG hD hi p'.val) (hq.trans p'.property.symm)
  exact ⟨hsame.1.trans hp'.1, hsame.2.trans hp'.2⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceConstants
