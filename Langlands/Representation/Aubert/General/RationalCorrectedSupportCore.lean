import Langlands.Representation.Aubert.General.CorrectedSupportCore
import Langlands.Representation.Aubert.General.RationalCorrectedSupportComparison
import Langlands.Representation.Aubert.General.RationalStandardComplex

/-! # Rational realization of corrected support cores -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The union of the actual base-parabolic double cosets in the literal
decreasing-length prefix, before taking any larger parabolic core. -/
def rankOrderedBaseCellSupport [Fintype (Weyl i)] [DecidableEq (Weyl i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM) (j : ℕ) :
    Set (RationalPoint k G.X) :=
  CorrectedFiltration.cellSupport (torusPoints i)
    (parabolic i ν ∅) (parabolic i ν ∅)
    (Support.rankOrderedSupport cs.length j)

variable (hPoints : StandardParabolicPointsStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLevi : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)

include hPoints hG hi hν hN hZ cs hLevi

/-- The rational double-coset comparison has exactly the generic support
interface, for every pair of finite root subsets. -/
theorem cellDoubleCosetComparison_of_standardParabolicPoints
    (J I : Finset (SimpleRoot i ν)) :
    CorrectedFiltration.CellDoubleCosetComparison (torusPoints i)
      (parabolic i ν J) (parabolic i ν I)
      (standardSubgroup cs J) (standardSubgroup cs I) :=
  parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints
    i ν hPoints hG hi hν hN hZ cs hLevi J I

/-- At the empty root subsets the comparison separates the actual base
cells by their full-centralizer Weyl indices. -/
theorem cellIndexSeparation_of_standardParabolicPoints :
    CorrectedFiltration.CellIndexSeparation (torusPoints i) (parabolic i ν ∅) := by
  intro n n' hnn'
  have hw := (parabolic_doubleCoset_mk_eq_iff_of_standardParabolicPoints
    i ν hPoints hG hi hν hN hZ cs hLevi ∅ ∅ n n').mp hnn'
  rw [standardSubgroup_empty, DoubleCoset.eq] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  have ha' : a = 1 := ha
  have hb' : b = 1 := hb
  simpa only [ha', hb', one_mul, mul_one] using hab.symm

section FixedOrder

variable [LinearOrder (SimpleRoot i ν)] [Fintype (SimpleRoot i ν)]
  [Fintype (Weyl i)] [DecidableEq (Weyl i)]
  (hOrder : StandardParabolicOrderStatement.{u})

include hOrder

/-- At every literal rank prefix, the implemented rational support is the
largest actual parabolic core of the corresponding base-cell union. -/
theorem groupSupport_eq_twoSidedCore_of_standardParabolicPoints
    (I s : Finset (SimpleRoot i ν)) (j : ℕ) :
    CorrectedFiltration.groupSupport (parabolic i ν) (torusPoints i) cs I s j =
      Support.twoSidedCore (parabolic i ν (Finset.univ \ s)) (parabolic i ν I)
        (rankOrderedBaseCellSupport i ν cs j) :=
  CorrectedFiltration.groupSupport_eq_twoSidedCore
    (parabolic i ν) (torusPoints i) cs I s j
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (isBruhatCover_of_standardParabolicPoints i ν hPoints hG hi hν ∅)
    (cellIndexSeparation_of_standardParabolicPoints i ν hPoints hG hi hν hN hZ cs hLevi)
    (cellDoubleCosetComparison_of_standardParabolicPoints
      i ν hPoints hG hi hν hN hZ cs hLevi (Finset.univ \ s) I)

/-- Every corrected rational support is invariant under the actual left
parabolic action. -/
theorem groupSupport_mul_left_of_standardParabolicPoints
    (I s : Finset (SimpleRoot i ν)) (j : ℕ)
    {p g : RationalPoint k G.X}
    (hp : p ∈ parabolic i ν (Finset.univ \ s))
    (hg : g ∈ CorrectedFiltration.groupSupport
      (parabolic i ν) (torusPoints i) cs I s j) :
    p * g ∈ CorrectedFiltration.groupSupport
      (parabolic i ν) (torusPoints i) cs I s j :=
  CorrectedFiltration.groupSupport_mul_left_of_doubleCosetComparison
    (parabolic i ν) (torusPoints i) cs I s j
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (isBruhatCover_of_standardParabolicPoints i ν hPoints hG hi hν I)
    (cellDoubleCosetComparison_of_standardParabolicPoints
      i ν hPoints hG hi hν hN hZ cs hLevi (Finset.univ \ s) I) hp hg

/-- At a surviving position of the implemented order, the actual rational
support difference is the whole parabolic double coset of the inverse lift. -/
theorem groupSupport_succ_sdiff_eq_of_standardParabolicPoints
    (I s : Finset (SimpleRoot i ν)) (j : ℕ)
    (hj : j < (Support.rankOrderedList cs.length).length)
    (m : Group.RelativeWeyl.normalizer (torusPoints i))
    (hm : (QuotientGroup.mk m : Weyl i) =
      (Support.rankOrderedElement cs.length j hj)⁻¹)
    (hmin : IsMinimal cs (Finset.univ \ s) I
      (Support.rankOrderedElement cs.length j hj)) :
    CorrectedFiltration.groupSupport (parabolic i ν) (torusPoints i) cs I s (j + 1) \
        CorrectedFiltration.groupSupport (parabolic i ν) (torusPoints i) cs I s j =
      {g | ∃ p ∈ parabolic i ν (Finset.univ \ s), ∃ q ∈ parabolic i ν I,
        g = p * (m : RationalPoint k G.X)⁻¹ * q} :=
  CorrectedFiltration.groupSupport_succ_sdiff_eq_of_doubleCosetComparison
    (parabolic i ν) (torusPoints i) cs I s j hj
    (standardParabolic_monotone i ν hOrder hG hi hν)
    (isBruhatCover_of_standardParabolicPoints i ν hPoints hG hi hν I)
    (cellDoubleCosetComparison_of_standardParabolicPoints
      i ν hPoints hG hi hν hN hZ cs hLevi (Finset.univ \ s) I) m hm hmin

end FixedOrder

end Langlands.Aubert.General.RationalPointFamily
