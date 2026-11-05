import Langlands.GroupScheme.Rational.RootSubgroupLieImage
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly

/-! # Full root tangent bounds from prescribed rank-one quotient curves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- If a character is positive on a cocharacter, the entire intrinsic root
tangent, including every positive integral multiple weight, lies in the
dynamic unipotent tangent for that cocharacter. -/
theorem tangentSubmodule_subgroup_le_unipotent
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {α : characterLattice T}
    (hpos : 0 < latticePairing T α ν) :
    tangentSubmodule (subgroup i α) ≤
      tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) := by
  have hα : α ≠ 0 := by
    rintro rfl
    simp at hpos
  rw [tangentSubmodule_subgroup i α hT hα, semigroupWeightSpan]
  refine iSup_le fun χ => ?_
  obtain ⟨n, _, hn, hχ⟩ := χ.property
  rw [← hχ, actionWeightSpace_conjugation]
  apply weightSpace_le_tangentSubmodule_unipotent hT i ν
  rw [map_nsmul]
  change 0 < n • latticePairing T α ν
  simpa only [nsmul_eq_mul] using
    mul_pos (Int.natCast_pos.mpr hn) hpos

/-- The inclusion retains the original tangent vector and includes all
positive integral root weights. -/
def rootTangentToUnipotent
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {α : characterLattice T}
    (hpos : 0 < latticePairing T α ν) :
    tangentSubmodule (subgroup i α) →ₗ[k]
      tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) :=
  Submodule.inclusion (tangentSubmodule_subgroup_le_unipotent hT i ν hpos)

/-- A bound on a dynamic unipotent tangent bounds the full intrinsic tangent
of any character positive on its cocharacter. -/
theorem finrank_tangentSubmodule_subgroup_le_of_unipotent
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) {α : characterLattice T}
    (hpos : 0 < latticePairing T α ν)
    (hdim : Module.finrank k (tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))) ≤ 1) :
    Module.finrank k (tangentSubmodule (subgroup i α)) ≤ 1 :=
  (Submodule.finrank_mono
    (tangentSubmodule_subgroup_le_unipotent hT i ν hpos)).trans hdim

end RelativeRoot

namespace HomogeneousQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    (b : B ⟶ G) (q : G.X ⟶ Q)
    (hfib : ∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier Y)
    [QuasiCompact q.left] [Smooth q.left] [Surjective q.left] [IsSeparated Q.hom]

include q hfib in
/-- A supplied exact rank-one quotient curve bounds the entire intrinsic
root tangent for every root positive on the original cocharacter. The bound
uses both signed dynamic tangent dimensions, not only root uniqueness. -/
theorem finrank_rootTangent_le_one_of_rankOne_curve
    (hG : IsConnectedReductive G) (hb : IsClosedSubgroup b)
    (hB : IsSolvableGroupScheme B) (hproper : ¬ IsIso b)
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ B)
    (hi : IsMaximalTorus (t ≫ b))
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots (t ≫ b), ∀ β ∈ roots (t ≫ b),
        ¬ LinearIndependent ℤ ![α, β])
    (n : normalizerPoints (t ≫ b))
    (hn : (QuotientGroup.mk n : relativeWeylGroup (t ≫ b)) ≠ 1)
    (ν : cocharacterLattice T)
    (hc : torusCentralizer (t ≫ b) ≤ SubgroupFunctor.range b)
    (hdimQ : topologicalKrullDim Q.left ≤ 1)
    {α : characterLattice T}
    (hα : haveI := hG.isAffineHom
      α ∈ roots (t ≫ b))
    (hpos : 0 < latticePairing T α ν) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule
      (RelativeRoot.subgroup (t ≫ b) α)) ≤ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  let D := regularSignedCurveUnipotentDataOfIsConnectedReductive
    b q hfib hG hb hB hproper hT t hi hdep n hn ν hc hdimQ
  have hdim : Module.finrank k (RelativeRoot.tangentSubmodule
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (regularNormalizerSymmetrizedCocharacter hT (t ≫ b) n ν) ≫ (t ≫ b)))) ≤ 1 := by
    rcases D.finrank_tangent_le_one_or_neg with h | h
    · exact h
    · exact (hG.finrank_tangentSubmodule_unipotent_normalizerSymmetrized_eq_neg
        (t ≫ b) hi hT hdep n (regularRefinement hT (t ≫ b) ν)).le.trans h
  exact RelativeRoot.finrank_tangentSubmodule_subgroup_le_of_unipotent hT (t ≫ b)
    (regularNormalizerSymmetrizedCocharacter hT (t ≫ b) n ν)
    (hG.regularNormalizerSymmetrizedCocharacter_pos
      (t ≫ b) hi hT hdep n hn ν hα hpos) hdim

end HomogeneousQuotient

/-- A prescribed Borel and the generic proper-fixed-point and projective
fixed-point inputs give the full root tangent bound in semisimple rank one.
The quotient curve and nonidentity normalizer class are constructed. -/
theorem finrank_rootTangent_le_one_of_prescribedBorel
    {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (b : B ⟶ G) (hB : IsBorelSubgroup b) (hproper : ¬ IsIso b)
    (t : T.toGrp ⟶ B) (ht : t ≫ b = i)
    (hconj : MaximalToriAreConjugate B)
    (hc : torusCentralizer i ≤ SubgroupFunctor.range b)
    {α : characterLattice T}
    (hα : haveI := hG.isAffineHom
      α ∈ roots i) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule
      (RelativeRoot.subgroup i α)) ≤ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  subst i
  let E := prescribedBorelProjectiveCurveData
    hFix hProj hG (t ≫ b) hi hT hdep b hB t rfl hconj hc
  let D := E.val
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive (t ≫ b) hi hT hα b hB.isClosedSubgroup
    hB.isSolvableGroupScheme t rfl hconj D.projection D.fibers
  obtain ⟨d, hd, ν, hν⟩ := hT.exists_pairing_eq_pos hα.1
  apply HomogeneousQuotient.finrank_rootTangent_le_one_of_rankOne_curve
    b D.projection D.fibers hG hB.isClosedSubgroup hB.isSolvableGroupScheme
    hproper hT t hi hdep n.val n.property ν hc E.property hα
  rw [hν]
  exact Int.natCast_pos.mpr hd

/-- Four generic structural inputs imply the complete intrinsic root tangent
bound in the algebraically closed rank-one case. All four inputs remain
explicit; this theorem does not establish their truth. -/
theorem rankOne_rootTangent_le_one_of_projectiveBorelInputs
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hConj : SolvableMaximalTorusConjugacyStatement.{u})
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T}
    (hα : haveI := hG.isAffineHom
      α ∈ roots i) :
    haveI := hG.isAffineHom
    Module.finrank k (RelativeRoot.tangentSubmodule
      (RelativeRoot.subgroup i α)) ≤ 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨B, b, t, hpair, hproper, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    hConj k B hpair.1.isSolvableGroupScheme
  have hc : torusCentralizer i ≤ SubgroupFunctor.range b := by
    rw [hCent k G hG T i hi]
    intro Y g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    refine SubgroupFunctor.mem_range.mpr ⟨x ≫ t.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, ht]
  exact finrank_rootTangent_le_one_of_prescribedBorel
    hFix hProj hG i hi hT hdep b hpair.1 hproper t ht hconj hc hα

end Langlands.GroupScheme
