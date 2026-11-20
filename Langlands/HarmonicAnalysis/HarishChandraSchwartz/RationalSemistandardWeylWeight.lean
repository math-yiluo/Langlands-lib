import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylSource

/-! # Weyl transport of the unquotiented semistandard weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (M : SemistandardSpectralLevi i) (hM : torusCentralizer i ≤ M.val)
  (w : relativeWeylGroup i)

private theorem map_leviRelativeWeylSubgroup_conj :
    (semistandardLeviRelativeWeylSubgroup i M).map (MulAut.conj w).toMonoidHom =
      semistandardLeviRelativeWeylSubgroup i (weylConjugateLevi hG hi hD M hM w) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  let M' := weylConjugateLevi hG hi hD M hM (QuotientGroup.mk n)
  have hM' := semistandardLeviCentralizerContainment_of_dynamicCoverage hD F G hG S i hi M'
  ext v
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective v
  change QuotientGroup.mk m ∈
    (semistandardLeviRelativeWeylSubgroup i M).map
      (MulAut.conj (QuotientGroup.mk n : relativeWeylGroup i)).toMonoidHom ↔
    QuotientGroup.mk m ∈ semistandardLeviRelativeWeylSubgroup i M'
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    mk_mem_semistandardLeviRelativeWeylSubgroup_iff i M hM,
    mk_mem_semistandardLeviRelativeWeylSubgroup_iff i M' hM']
  dsimp only [M']
  rw [weylConjugateLevi_mk, SubgroupFunctor.rationalPoints_comap_innerIso_inv,
    Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

/-- Ambient Weyl conjugation restricts to the literal relative Weyl groups of
an intrinsic Levi and its conjugate. -/
def weylConjugateLeviWeylEquiv : semistandardLeviRelativeWeylSubgroup i M ≃*
    semistandardLeviRelativeWeylSubgroup i (weylConjugateLevi hG hi hD M hM w) :=
  ((MulAut.conj w).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_leviRelativeWeylSubgroup_conj hG hi hD M hM w))

@[simp] theorem weylConjugateLeviWeylEquiv_coe (x : semistandardLeviRelativeWeylSubgroup i M) :
    (weylConjugateLeviWeylEquiv hG hi hD M hM w x : relativeWeylGroup i) = w * x.val * w⁻¹ :=
  rfl

namespace SourceConstants

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

/-- The real VI.3 and VII.2 weight agrees at the source index and any target
index over the conjugate Levi, conditional on the exact common-Levi scalar law. -/
theorem unquotientedWeightAtIndex_eq_at_weylConjugateLevi
    (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hSpecial : SpecialCompactProperties F i nu (K : Subgroup (rationalPoints G)))
    (p q : SemistandardSpectralIndex i) (hp : torusCentralizer i ≤ p.levi)
    (w : relativeWeylGroup i) (hq : q.levi = (weylConjugateLevi hG hi hD p.toLevi hp w).val) :
    unquotientedWeightAtIndex (hG := hG) hi K hK hD q =
      unquotientedWeightAtIndex (hG := hG) hi K hK hD p := by
  obtain ⟨hg, hc⟩ := eq_at_weylConjugateLevi hi K hK hD hI nu hnu hSpecial p q hp w hq
  let r := CocharacterPresentation.ofCoverage hG hD hi p
  let s := CocharacterPresentation.ofCoverage hG hD hi q
  have hgReal : gammaReal s K hK = gammaReal r K hK := congrArg ENNReal.toReal hg
  have hcReal : cReal s K hK = cReal r K hK := congrArg ENNReal.toReal hc
  have hq' : q.toLevi = weylConjugateLevi hG hi hD p.toLevi hp w := Subtype.ext hq
  have hcardW := Nat.card_congr (weylConjugateLeviWeylEquiv hG hi hD p.toLevi hp w).toEquiv.symm
  have hcardP := card_weylConjugateParabolicFiber hG hi hD p.toLevi hp w
  change unquotientedWeight s K hK = unquotientedWeight r K hK
  unfold unquotientedWeight
  rw [hgReal, hcReal, hq', hcardW, hcardP]

end SourceConstants

end Langlands.HarishChandraSchwartz.RationalSemistandard
