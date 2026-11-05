import Langlands.GroupScheme.Reductive.RankOneProjectiveBorelAssembly
import Langlands.GroupScheme.Reductive.RankOneBorelDynamicStatement
import Langlands.GroupScheme.Rational.RankOneDependentCocharacters
import Langlands.GroupScheme.Rational.GenericCentralizerProof

/-! # Prescribed Borel curve data for the original rank-one cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

omit [IsAlgClosed k] in
/-- Pairwise root dependence makes the original nonorthogonal cocharacter
generic, so its dynamic centralizer is the whole-torus centralizer. -/
theorem IsConnectedReductive.centralizer_eq_torusCentralizer_of_rankOne
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom
      α ∈ roots i) (ν : cocharacterLattice T)
    (hν : latticePairing T α ν ≠ 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = torusCentralizer i := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  exact genericCentralizer k G hG T i (hi.isMaximalSplitTorus hT) ν
    (hT.isRegularCocharacter_of_rankOne i hdep hα hν)

/-- The actual prescribed quotient, its curve bound and the centralizer
containment needed for dynamic parabolic comparison. The rational root rank
and properness of the subgroup inclusion are also retained. -/
structure PrescribedBorelDynamicCurveData
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (b : B ⟶ G)
    extends IsBorelSubgroup.ProperQuotientData b where
  dimension_le_one : topologicalKrullDim quotient.left ≤ 1
  centralizer_le :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b
  rootRank_eq_one : haveI := hG.isAffineHom
    Module.finrank ℚ (relativeRootSpan i) = 1
  inclusion_not_isIso : ¬ IsIso b

/-- Construct the actual curve data for every prescribed Borel and every
cocharacter nonorthogonal to a root, from four explicit structural inputs. -/
def prescribedBorelDynamicCurveData
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hConj : SolvableMaximalTorusConjugacyStatement.{u})
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    {α : characterLattice T} (hα : haveI := hG.isAffineHom
      α ∈ roots i) (ν : cocharacterLattice T)
    (hν : latticePairing T α ν ≠ 0)
    (b : B ⟶ G) (hB : IsBorelSubgroup b)
    (t : T.toGrp ⟶ B) (ht : t ≫ b = i) :
    PrescribedBorelDynamicCurveData hG i ν b := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Smooth B.X.hom := hB.smooth
  have : IsAffineHom B.X.hom := hB.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hB.connectedSpace
  have hconj : MaximalToriAreConjugate B := hConj k B hB.isSolvableGroupScheme
  have hc : torusCentralizer i ≤ SubgroupFunctor.range b := by
    rw [hCent k G hG T i hi]
    intro Y g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    refine SubgroupFunctor.mem_range.mpr ⟨x ≫ t.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, ht]
  let E := prescribedBorelProjectiveCurveData
    hFix hProj hG i hi hT hdep b hB t ht hconj hc
  exact {
    E.val with
    dimension_le_one := E.property
    centralizer_le := by
      rw [hG.centralizer_eq_torusCentralizer_of_rankOne i hi hT hdep hα ν hν]
      exact hc
    rootRank_eq_one := hT.finrank_relativeRootSpan_eq_one_of_rankOne i hdep hα
    inclusion_not_isIso := not_isIso_of_relativeRoot_of_isSolvable
      hG.isPseudoReductive i hT hα b hB.isSolvableGroupScheme
  }

end Langlands.GroupScheme
