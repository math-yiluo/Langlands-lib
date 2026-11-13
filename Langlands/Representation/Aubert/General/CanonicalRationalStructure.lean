import Langlands.Representation.Aubert.General.CanonicalRationalOperator
import Langlands.Representation.Aubert.General.RationalLeviFiniteLength
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.StandardLeviInductionFiniteLength
import Langlands.Representation.Aubert.General.StandardLeviJacquetFiniteLength
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.RationalRootSpanCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.GroupScheme.Rational.StandardLeviConjugationProof
import Langlands.Group.RelativeWeylMinimalityProof
import Langlands.Group.RelativeWeylAssociatedSubsetProof

/-! # Canonical standard Levi operators and Weyl data on actual rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)

section StandardLevi

variable [IsAffineHom G.X.hom]

local instance canonicalRationalStructurePointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every actual standard Levi is closed in the canonical point topology. -/
theorem canonicalStandardLevi_isClosed (J : Finset (SimpleRoot i ν)) :
    IsClosed (levi i ν J : Set (RationalPoint k G.X)) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isClosed_levi_of_isNonarchimedeanLocalField i ν J

variable (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Continuity of every actual restricted projection inside a standard Levi. -/
theorem canonicalStandardLeviProjection_continuous
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    Continuous (standardLeviProjection i ν standardLeviIntersection hG hi hν J I) :=
  continuous_standardLeviProjection i ν standardCocharacter standardLeviIntersection
    hG hi hν (continuous_standard_projection i ν standardCocharacter hG hi hν) J I

include hG hi hν in
/-- Every restricted radical inside an actual standard Levi is a limit of
compact subgroups. -/
theorem canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups
    (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)) :=
  standardLeviUnipotent_isLimitOfCompactSubgroups i ν
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) J (canonicalStandardLevi_isClosed i ν J) I

variable
  (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
  (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})

section SuppliedTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

omit [T2Space (RationalPoint k G.X)] in
include hiFl in
/-- Restricted normalized induction inside each actual standard Levi preserves
finite length, from the dynamic induction input alone. -/
theorem canonicalStandardLeviInduction_preservesFiniteLength
    (J : Finset (SimpleRoot i ν)) :
    letI := (canonicalStandardLevi_isClosed i ν J).locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν J I)
        ((canonicalStandardUnipotent_isClosed hG i ν hi hν (leviIndex J I)).preimage
          continuous_subtype_val)) :=
  standardLeviInduction_preservesFiniteLength.{u, v} i ν standardLeviIntersection hG hi hν
    standardCocharacter (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    J (canonicalStandardLevi_isClosed i ν J)

omit [T2Space (RationalPoint k G.X)] in
include hiFl hrFl in
/-- Restricted normalized Jacquet restriction inside each actual standard Levi
preserves finite length, from the two dynamic inputs. -/
theorem canonicalStandardLeviJacquet_preservesFiniteLength
    (J : Finset (SimpleRoot i ν)) :
    letI := (canonicalStandardLevi_isClosed i ν J).locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν J I)
        ((canonicalStandardUnipotent_isClosed hG i ν hi hν (leviIndex J I)).preimage
          continuous_subtype_val)) :=
  standardLeviJacquet_preservesFiniteLength.{u, v} i ν standardLeviIntersection hG hi hν
    standardCocharacter (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)
    J (canonicalStandardLevi_isClosed i ν J)

end SuppliedTopology

include hG hi hν hiFl hrFl in
/-- Aubert's unadjusted operator of the actual standard Levi `M_J` on actual
rational points. All subgroup regularity is supplied by published theorems;
only the two dynamic finite-length inputs remain. -/
def canonicalRationalLeviAlternatingOperator (J : Finset (SimpleRoot i ν)) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) := by
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : Smooth G.X.hom := hG.smooth
  letI : T2Space k := BruhatTits.localField_t2Space k
  letI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  letI : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  letI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  exact rationalLeviAlternatingOperator.{u, v} i ν standardLeviIntersection hG hi hν
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    J (canonicalStandardLevi_isClosed i ν J)
    (canonicalStandardLeviProjection_continuous hG i ν hi hν J)
    (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν J)
    (canonicalStandardLeviInduction_preservesFiniteLength hG i ν hi hν hiFl J)
    (canonicalStandardLeviJacquet_preservesFiniteLength hG i ν hi hν hiFl hrFl J)

/-- Every instance of the published Levi operator on the same actual standard
Levi is the canonical one: all its remaining arguments are propositions. -/
theorem rationalLeviAlternatingOperator_eq_canonical
    [LocallyCompactSpace (RationalPoint k G.X)]
    [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
    (hInter : StandardLeviIntersectionStatement.{u})
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (J : Finset (SimpleRoot i ν))
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
    (hproj : ∀ I : Finset J, Continuous (standardLeviProjection i ν hInter hG hi hν J I))
    (hUc : ∀ I : Finset J, Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
    (hiLFl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))
    (hrLFl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))) :
    rationalLeviAlternatingOperator.{u, v} i ν hInter hG hi hν hU hP J hM
        hproj hUc hiLFl hrLFl =
      canonicalRationalLeviAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl J :=
  rfl

/-- Every instance of the published ambient operator is the canonical ambient
operator of `CanonicalRationalOperator`: all its remaining arguments are
propositions. -/
theorem rationalAlternatingOperator_eq_canonical
    [LocallyCompactSpace (RationalPoint k G.X)]
    [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
    (hStandard : StandardCocharacterStatement.{u})
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (hproj : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
    (hiPFl : ∀ I, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    (hrPFl : ∀ I, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    [Mono i.hom.hom.left] (hRoots : HasRelativeRootSystem i) :
    rationalAlternatingOperator.{u, v} i ν hStandard hG hi hν hU hP hproj hUc
        hiPFl hrPFl hRoots =
      canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl :=
  rfl

end StandardLevi

section WeylData

variable (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- The scheme-normalizer points of a maximal split torus are exactly the
normalizer of its actual point image. -/
theorem canonicalPointNormalizerComparison : HasPointNormalizerComparison i :=
  (rationalWeylComparison k G hG T i hi).1

include hG hi in
/-- The scheme-centralizer points of a maximal split torus are exactly the
full centralizer `Z_G(T₀)` of its actual point image. -/
theorem canonicalPointCentralizerComparison : HasPointCentralizerComparison i :=
  (rationalWeylComparison k G hG T i hi).2

variable [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)

/-- The chosen finite Coxeter data of the actual relative Weyl group
`N_G(T₀)/Z_G(T₀)`, constructed from the published relative root system. -/
def canonicalPointCoxeterData :
    RootSpanPointCoxeterData i ν (canonicalPointNormalizerComparison hG i hi)
      (canonicalPointCentralizerComparison hG i hi) :=
  rootSpanPointCoxeterData i ν (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi) hG hi
    (relativeRootSystem k G hG T i hi) hν

/-- The Coxeter matrix of the canonical data, indexed by actual simple roots. -/
abbrev canonicalCoxeterMatrix : CoxeterMatrix (SimpleRoot i ν) :=
  (canonicalPointCoxeterData hG i hi ν hν).matrix

/-- The canonical Coxeter system on the actual relative Weyl group. -/
abbrev canonicalCoxeterSystem :
    ActualCoxeterSystem (torusPoints i) (canonicalCoxeterMatrix hG i hi ν hν) :=
  (canonicalPointCoxeterData hG i hi ν hν).system

include hG hi hν in
/-- The actual relative Weyl group is finite. -/
theorem canonicalWeyl_finite : Finite (Weyl i) :=
  (canonicalPointCoxeterData hG i hi ν hν).finiteWeyl

include hG hi hν in
/-- The actual simple roots are finite. -/
theorem canonicalSimpleRoot_finite : Finite (SimpleRoot i ν) :=
  (canonicalPointCoxeterData hG i hi ν hν).finiteSimple

/-- A `Fintype` structure on the actual relative Weyl group from its finiteness. -/
abbrev canonicalWeylFintype : Fintype (Weyl i) :=
  haveI := canonicalWeyl_finite hG i hi ν hν
  Fintype.ofFinite _

/-- Root-sign length comparison for the canonical Coxeter system. -/
theorem canonicalRootLengthComparison :
    RootLengthComparison i ν (canonicalPointNormalizerComparison hG i hi)
      (canonicalPointCentralizerComparison hG i hi)
      (canonicalCoxeterSystem hG i hi ν hν) :=
  (canonicalPointCoxeterData hG i hi ν hν).rootLength

/-- Simple reflections fix the cocharacters orthogonal to their root. -/
theorem canonicalSimpleReflectionPairingInvariance :
    SimpleReflectionPairingInvariance i ν (canonicalPointNormalizerComparison hG i hi)
      (canonicalPointCentralizerComparison hG i hi)
      (canonicalCoxeterSystem hG i hi ν hν) :=
  (canonicalPointCoxeterData hG i hi ν hν).simplePairing

/-- The actual Weyl groups of the standard Levis are the standard parabolic
subgroups of the canonical Coxeter system. -/
theorem canonicalLeviWeylIdentification :
    actualLeviWeylIdentification (torusPoints i) (levi i ν)
      (canonicalCoxeterSystem hG i hi ν hν) :=
  (canonicalPointCoxeterData hG i hi ν hν).leviWeyl

/-- Conjugating a positive simple root to a simple root is the same as
conjugating the simple reflections. -/
theorem canonicalPositiveSimpleReflectionComparison :
    PositiveSimpleReflectionComparison i ν (canonicalPointNormalizerComparison hG i hi)
      (canonicalPointCentralizerComparison hG i hi)
      (canonicalCoxeterSystem hG i hi ν hν) :=
  positiveSimpleReflectionComparison_of_rootLength i ν
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalCoxeterSystem hG i hi ν hν) hi.isSplitSubtorus.1
    (relativeRootSystem k G hG T i hi) hν
    (canonicalRootLengthComparison hG i hi ν hν)

/-- The double-coset minimal length criterion for the canonical system. -/
theorem canonicalMinimalityLengthCriterion :
    minimalityLengthCriterion (canonicalCoxeterSystem hG i hi ν hν) :=
  minimalityLengthCriterion_proof _

variable [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]

/-- The associated-subset laws for the canonical system, for any `Fintype`
structures on the actual simple roots and Weyl group. -/
theorem canonicalAssociatedSubsetLaws :
    associatedSubsetLaws (canonicalCoxeterSystem hG i hi ν hν) :=
  associatedSubsetLaws_proof _

/-- Conjugation by any lift of the longest representative carries the actual
Levi of the associated subset onto the actual Levi of `J`. -/
theorem canonicalAssociatedLeviConjugation :
    actualAssociatedLeviConjugation (torusPoints i) (levi i ν)
      (canonicalCoxeterSystem hG i hi ν hν) :=
  associatedLeviConjugation_of_standard i ν hG hi hν standardLeviConjugation
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalCoxeterSystem hG i hi ν hν)
    (canonicalRootLengthComparison hG i hi ν hν)
    (canonicalPositiveSimpleReflectionComparison hG i hi ν hν)
    (canonicalMinimalityLengthCriterion hG i hi ν hν)
    (canonicalAssociatedSubsetLaws hG i hi ν hν)

end WeylData

end Langlands.Aubert.General.RationalPointFamily
