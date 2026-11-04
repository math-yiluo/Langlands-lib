import Langlands.Representation.Aubert.General.RationalStrictFactorUnitarity
import Langlands.Representation.Aubert.General.RationalAssociatedCharacterModulusCases
import Langlands.Representation.Aubert.General.RationalLeviNormKernelUnitarity
import Langlands.Representation.Aubert.General.RationalUnitaryInductionIrreducibility

/-! # Local irreducibility from actual two-Jacquet and modulus inputs -/

noncomputable section

set_option maxHeartbeats 800000

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance instRationalLocalInductionIrreducibility1 : TopologicalSpace (RationalPoint k G.X) := pointTopology

local instance instRationalLocalInductionIrreducibility2 : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance (J : Finset (SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν J)
local instance (J : Finset (SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (rootSet i ν J)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν J)).hom.hom.left
local instance (J : Finset (SimpleRoot i ν)) :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν J))) :=
  rationalPointTopology k (Standard.leviScheme i ν (rootSet i ν J)).X

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  [Mono i.hom.hom.left]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [Fintype (SimpleRoot i ν)] [DecidableEq (SimpleRoot i ν)] [Fintype (Weyl i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
  (hRoots : HasRelativeRootSystem i)
  (hConj : StandardLeviConjugationStatement.{u})
  (I : Finset (SimpleRoot i ν)) (hI : IsMaximalStandard I)
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  (hn : QuotientGroup.mk n = longestRep cs I)
  (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (hsq : RationalStrictJacquetSquareIntegrabilityStatement.{u, v})
  (hHaar : RationalOppositeHaarReciprocityStatement.{u})
  (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
  (hmod : RationalParabolicModulusStatement.{u})
  (hSplit : StandardLeviSplitComponentStatement.{u})
  (hCompact : CenterSplitComponentCompactnessStatement.{u})
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hm : Continuous (isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν I).projection)
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (s : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (hs : IsCentral s)
  (hindex : (Plancherel.RenardCartan.splitValuationImage s).FiniteIndex)
  (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
  (hσ : σ.IsIrreducible) (haσ : σ.IsAdmissible)
  (hcoeff : HasCompactSmoothDualCoefficients
    (restrictSubgroup
      (Plancherel.rationalCommonNormKernel (Standard.leviScheme i ν (rootSet i ν I)))
      ((pullbackFunctor (leviRationalPointHomeomorph i ν I)).obj σ)).representation)
  (hJac : ((jacquetFunctor
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) (hU I)).obj
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ)).IsIrreducible)
  (hJacO : ((jacquetFunctor
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs I)) (hU (associatedSubset cs I))).obj
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ)).IsIrreducible)
  (haJacO : ((jacquetFunctor
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs I)) (hU (associatedSubset cs I))).obj
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ)).IsAdmissible)
  (hdetect : ∀ D : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
    D.IsIrreducible →
    IsSubquotient D ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ) →
    Nontrivial ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj D) ∨
    Nontrivial ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs I)) (hU (associatedSubset cs I))).obj D))
  (hzero : ∀ K : Finset (SimpleRoot i ν),
    K ≠ I → K ≠ associatedSubset cs I → K ≠ Finset.univ →
    Subsingleton ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν K) (hU K)).obj
      ((normalizedInductionFunctor
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)).obj σ)))
  (c : UnitaryCentralCharacter
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ).representation)
  (hchars :
    let C := inductionTwoJacquetScalarCharactersOfSchur
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (associatedSubset cs I)) (hU (associatedSubset cs I))
      σ hσ haσ hJacO haJacO
    C.second = associatedLeviCentralCharacter i ν hG hi hν hConj hN hZ cs
      hLength hSimple hMin hAssoc I n hn C.first)

include hLength hSimple hIdent hMin hAssoc hRoots hI hn hζ hsq hHaar
  hcompact hmod hSplit hCompact hMI hP hm s hs hindex
  hσ haσ hcoeff hJac hJacO haJacO hdetect hzero c hchars

/-- The retained local geometric, scalar-comparison and norm-kernel inputs
force irreducibility of the actual maximal standard induction. -/
theorem isIrreducible_standardInduction_of_twoJacquet_modulus_inputs :
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ).IsIrreducible := by
  classical
  have := hG.smooth
  have : IsAffineHom T.X.hom := hi.isSplitSubtorus.1.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  have : LocallyCompactSpace (parabolic i ν I) := hP.locallyCompactSpace
  have : CompactSpace (Induction.LeftQuotient (parabolic i ν I)) :=
    compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν I
  borelize (RationalPoint k G.X)
  let d := isSemidirectDecomposition_of_standardCocharacterStatement
    i ν hStandard hG hi hν
  let B := (normalizedInductionFunctor (d I) (hU I)).obj σ
  let C := inductionTwoJacquetScalarCharactersOfSchur
    (d I) (hU I) (d (associatedSubset cs I)) (hU (associatedSubset cs I))
    σ hσ haσ hJacO haJacO
  have hfirstopen : IsOpen (C.first.ker : Set (Subgroup.center (levi i ν I))) :=
    inductionTwoJacquetScalarCharactersOfSchur_first_isOpen_ker
      (d I) (hU I) (d (associatedSubset cs I)) (hU (associatedSubset cs I))
      σ hσ haσ hJacO haJacO
  have hsecondopen : IsOpen
      (C.second.ker : Set (Subgroup.center (levi i ν (associatedSubset cs I)))) :=
    inductionTwoJacquetScalarCharactersOfSchur_second_isOpen_ker
      (d I) (hU I) (d (associatedSubset cs I)) (hU (associatedSubset cs I))
      σ hσ haσ hJacO haJacO
  have hfirstambient := InductionTwoJacquetScalarCharacters.first_norm_ambientCenter_eq_one
    (d I) (hU I) (d (associatedSubset cs I)) (hU (associatedSubset cs I))
    σ hJacO C (center_le_standardLevi i ν hZ I) c
  have hsecondambient := InductionTwoJacquetScalarCharacters.second_norm_ambientCenter_eq_one
    (d I) (hU I) (d (associatedSubset cs I)) (hU (associatedSubset cs I))
    σ hJacO C (center_le_standardLevi i ν hZ (associatedSubset cs I)) c
  have haB : B.IsAdmissible :=
    normalizedInductionFunctor_obj_isAdmissible (d I) (hU I) hm σ haσ
  have hunimod := (hmod k G hG T i hi ν hν hStandard I (hU I) hP hm).1
  by_contra hred
  let F := inductionTwoJacquetFactors (d I) (hU I)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν I)
    (d (associatedSubset cs I)) (hU (associatedSubset cs I))
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν (associatedSubset cs I))
    σ hJac hJacO hdetect hσ hred
  rcases associatedLeviCentralCharacters_norm_cases_of_rationalData
    i ν hN hZ cs hStandard hG hi hRoots hν hLength hIdent hConj hSimple hMin hAssoc
    I hI n hn C.first C.second hfirstopen hsecondopen hfirstambient hsecondambient
    hchars with hfirst | hsecond | hunit
  · exact Langlands.Aubert.General.RationalPointFamily.InductionTwoJacquetFactors.not_first_strict_bound
      i ν hG hi hν hStandard hU hN hZ cs hLength hSimple hMin hAssoc hRoots
      I n hn ζ hζ hsq hHaar hunimod σ F C haB c hzero hσ hfirst
  · have hnonzero : Nontrivial ((jacquetFunctor
        (d (associatedSubset cs I)) (hU (associatedSubset cs I))).obj B) :=
      repLength_pos_iff.mp (by
        rw [repLength_eq_one_iff.mpr hJacO]
        exact zero_lt_one)
    exact Langlands.Aubert.General.RationalPointFamily.InductionTwoJacquetFactors.not_second_strict_bound
      i ν hG hi hν hStandard hU hN hZ cs hLength hSimple hMin hAssoc hRoots
      I n hn ζ hζ hsq hHaar hunimod σ F C haB c hzero hnonzero hsecond
  · have htorus : ∀ t : leviCentralTorusPoints i ν I,
        ‖(C.first (leviCentralTorusPointToCenter i ν I t) : ℂ)‖ = 1 :=
      fun t => hunit.1 t.val (leviCentralTorusPointToCenter i ν I t) rfl
    have hunitary : IsUnitarizable σ.representation :=
      ⟨leviNormKernelPositiveForm_of_centralTorus
        i ν I hMI s hs hindex σ hσ hcoeff hSplit hCompact hG hi hν
        C.first hfirstopen htorus C.first_scalar⟩
    exact hred (isIrreducible_standardInduction_of_unitary_irreducible_jacquet
      i ν hcompact hmod hStandard hG hi hν I (hU I) hP hm σ haσ hunitary hJac)

/-- Under the same local inputs, the inclusion of every nonzero invariant
subspace is an equivalence with the whole actual induction. -/
def twoJacquetStandardInductionSubrepresentationEquiv
    (S : Subrepresentation ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ).representation)
    (hS : S ≠ ⊥) :
    S.toRepresentation.Equiv ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ).representation := by
  letI := isIrreducible_standardInduction_of_twoJacquet_modulus_inputs
    i ν hG hi hν hStandard hU hN hZ cs hLength hSimple hIdent hMin hAssoc hRoots
    hConj I hI n hn ζ hζ hsq hHaar hcompact hmod hSplit hCompact hMI hP hm
    s hs hindex σ hσ haσ hcoeff hJac hJacO haJacO hdetect hzero c hchars
  have htop : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hS
  let j : S.toRepresentation.IntertwiningMap ((normalizedInductionFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)).obj σ).representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact j.ofBijective
    ⟨Subtype.val_injective, fun w => ⟨⟨w, by rw [htop]; trivial⟩, rfl⟩⟩

end Langlands.Aubert.General.RationalPointFamily
