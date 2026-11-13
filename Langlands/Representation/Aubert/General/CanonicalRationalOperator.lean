import Langlands.Representation.Aubert.General.RationalSupportInduction
import Langlands.Representation.Aubert.General.RationalStandardFiniteLength
import Langlands.Representation.Plancherel.RationalTwistStabilizer
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # The rational-point operator with published structural inputs -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)

section StandardData

variable [IsAffineHom G.X.hom]

local instance canonicalRationalOperatorPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- Closedness of each actual standard unipotent subgroup, with the published
standard cocharacter theorem supplied. -/
theorem canonicalStandardUnipotent_isClosed (I : Finset (SimpleRoot i ν)) :
    IsClosed (unipotent i ν I : Set (RationalPoint k G.X)) := by
  let : T2Space k := BruhatTits.localField_t2Space k
  exact standardUnipotent_isClosed_of_standardCocharacterStatement
    i ν standardCocharacter hG hi hν I

variable
  (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
  (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

include hiFl hrFl in
/-- The exact-K0 prerequisite for a standard parabolic, with all subgroup
regularity supplied and with the two finite-length inputs still explicit. -/
theorem canonicalStandardParabolicFiniteLength (I : Finset (SimpleRoot i ν)) :
    ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν standardCocharacter hG hi hν I)
      (canonicalStandardUnipotent_isClosed hG i ν hi hν I) :=
  standardParabolicFiniteLength i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl) I

end StandardData

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hi : IsMaximalSplitTorus i)
  (hν : haveI := hG.isAffineHom; IsGenericCocharacter i ν)
  (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
  (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})

include hG i ν hi hν hiFl hrFl in
/-- Aubert's unadjusted operator on actual rational points over an arbitrary
nonarchimedean local field. Only induction and Jacquet finite-length
preservation remain representation-theoretic inputs. -/
def canonicalRationalAlternatingOperator :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    FiniteLengthGrothendieckGroup.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X) := by
  letI := hG.isAffineHom
  letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) := Plancherel.rationalPoints_nonarchimedeanGroup G
  letI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  letI := hi.isSplitSubtorus.mono
  exact rationalAlternatingOperator i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)
    (relativeRootSystem k G hG T i hi)

/-- The actual-functor class formula of the canonical construction. -/
theorem canonicalRationalAlternatingOperator_ofRepresentation :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : Smooth G.X.hom := hG.smooth
    letI : T2Space k := BruhatTits.localField_t2Space k
    letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    letI : NonarchimedeanGroup (RationalPoint k G.X) := Plancherel.rationalPoints_nonarchimedeanGroup G
    letI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    letI := hi.isSplitSubtorus.mono
    let _ := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
      hi.isSplitSubtorus.1 ν
    ∀ (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X)) (hA : A.HasFiniteLength),
      canonicalRationalAlternatingOperator hG i ν hi hν hiFl hrFl
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        ∑ I : Finset (SimpleRoot i ν), ((-1 : ℤ) ^ I.card) •
          FiniteLengthGrothendieckGroup.ofRepresentation
            ((inductionJacquetFunctor.{u, max (u + 1) v}
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν standardCocharacter hG hi hν I)
              (canonicalStandardUnipotent_isClosed hG i ν hi hν I)).obj A)
            ((canonicalStandardParabolicFiniteLength hG i ν hi hν hiFl hrFl I).1 _
              ((canonicalStandardParabolicFiniteLength hG i ν hi hν hiFl hrFl I).2.2.1 A hA)) := by
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) := Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  dsimp only
  intro A hA
  exact rationalAlternatingOperator_ofRepresentation i ν standardCocharacter hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)
    (relativeRootSystem k G hG T i hi) A hA

end Langlands.Aubert.General.RationalPointFamily
