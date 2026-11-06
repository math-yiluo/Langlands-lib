import Langlands.GroupScheme.Reductive.RootReducednessReduction
import Langlands.GroupScheme.Reductive.RankOneRootReducednessAssembly
import Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly
import Langlands.GroupScheme.Rational.RankOneCocharacterSymmetrization
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Proof: the roots of a split maximal torus of a connected reductive group are reduced -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RootReducedness

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, if any two roots of a split maximal torus of a connected
reductive group are integrally dependent, then the negative of a root is a root: a proper Borel
subgroup containing the torus gives a nonidentity Weyl class, which negates every root. -/
theorem neg_mem_roots_of_rankOne_algClosed [IsAlgClosed k] (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} :
    haveI := hG.isAffineHom
    α ∈ roots i → -α ∈ roots i := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  intro hα
  obtain ⟨B, b, t, hpair, -, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    solvableMaximalTorusConjugacy k B hpair.1.isSolvableGroupScheme
  let D := hpair.1.properQuotientData_of_solvableProperFixedPoint solvableProperFixedPoint
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive i hi hT hα b hpair.1.isClosedSubgroup
    hpair.1.isSolvableGroupScheme t ht hconj D.projection D.fibers
  let := hi.2.1.mono
  rw [← hG.weylAction_eq_neg_of_rankOne i hi hT hdep n.val n.property α hα]
  exact weylAction_mapsTo_relativeRoots i n.val hα

/-- If any two roots of a split maximal torus of a connected reductive group are integrally
dependent, then the negative of a root is a root. This is the algebraically closed case after
base change to an algebraic closure. -/
theorem neg_mem_roots_of_rankOne (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} :
    haveI := hG.isAffineHom
    α ∈ roots i → -α ∈ roots i := by
  have := hG.isAffineHom
  have := hG.smooth
  intro hα
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  let Tc := (CommGroupScheme.baseChange b).obj T
  let ic : Tc.toGrp ⟶ Gc := (GroupScheme.baseChange b).map i
  have hGc : IsConnectedReductive Gc := hG.baseChange_toAlgebraicClosure
  have := hGc.isAffineHom
  have hic : IsMaximalTorus ic :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T i hi.1 hi.2.1).mp hi
  have hdepc : ∀ α ∈ roots ic, ∀ β ∈ roots ic, ¬ LinearIndependent ℤ ![α, β] :=
    (roots_pairwise_dependent_baseChange_iff (K := AlgebraicClosure k) G T hT i).mpr hdep
  have hαc := (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i α).mpr hα
  have h := neg_mem_roots_of_rankOne_algClosed hGc (hT.baseChange b) ic hic hdepc hαc
  rw [← map_neg] at h
  exact (mem_roots_baseChange_iff (K := AlgebraicClosure k) G T hT i (-α)).mp h

/-- **Reducedness of the roots in semisimple rank one.** The negation step is
`neg_mem_roots_of_rankOne`; uniqueness of the root positive on a cocharacter is the published
projective Borel route, whose centralizer input is supplied by the published proofs of
`DynamicCentralizerReductiveStatement` and `SolvableTorusQuotientStatement`. -/
theorem rankOneRootReducedness : RankOneRootReducednessStatement.{u} := by
  have hpos : RankOnePositiveRootUniquenessStatement.{u} :=
    rankOnePositiveRootUniqueness_of_projectiveBorelInputs
      (algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
        solvableTorusQuotient)
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  intro hdep α hα β hβ
  set ν := hT.positiveCocharacter hα.1
  have hαν : 0 < latticePairing T α ν := hT.latticePairing_positiveCocharacter_pos hα.1
  have hβν : latticePairing T β ν ≠ 0 :=
    hT.latticePairing_ne_zero_of_not_linearIndependent hβ.1 (hdep α hα β hβ) hαν.ne'
  rcases lt_or_gt_of_ne hβν with hlt | hgt
  · right
    have hβ' : -β ∈ roots i := neg_mem_roots_of_rankOne hG hT i hi hdep hβ
    refine hpos k G hG T hT i hi hdep ν α hα (-β) hβ' hαν ?_
    rw [map_neg, LinearMap.neg_apply]
    exact neg_pos.mpr hlt
  · left
    exact hpos k G hG T hT i hi hdep ν α hα β hβ hαν hgt

end RootReducedness

/-- **Reducedness of the roots** (Milne, Theorem 21.11(b)): for a connected reductive group with
a split maximal torus, two integrally dependent roots are equal or opposite. -/
theorem rootReducedness : RootReducednessStatement.{u} :=
  rootReducedness_of_rankOne RootReducedness.rankOneRootReducedness dynamicCentralizerReductive

end Langlands.GroupScheme
