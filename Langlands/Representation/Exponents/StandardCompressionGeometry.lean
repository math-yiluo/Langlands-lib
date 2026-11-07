import Langlands.Representation.Exponents.StandardCuspidalInductionCompression
import Langlands.Representation.Plancherel.StandardCuspidalNativeJacquetInputs
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality
import Langlands.Representation.Aubert.General.StandardFamilyStructure
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.GroupScheme.Rational.ParabolicRootPresentationDynamicConstruction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CentralizerRootSystemInheritance
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Geometric inputs for compression on the canonical standard representatives -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open Plancherel Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (I : Finset (SimpleRoot i ν))

/-- Choose a split component and an actual root presentation on the exact
canonical standard parabolic and Levi maps. -/
def standardCompressionRootPresentation
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hPD : ParabolicDynamicStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    Σ A : CommGroupScheme (Spec (CommRingCat.of F)),
      Σ a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I),
        ParabolicRootPresentation (Standard.parabolicHom i ν (rootSet i ν I))
          (Standard.leviToParabolic i ν (rootSet i ν I)) a := by
  apply Classical.choice
  obtain ⟨hp, hl, -, -⟩ :=
    RepresentedParabolic.standard_representatives_geometric i ν hPD hStandard hG hi hν I
  obtain ⟨A, a, ha⟩ :=
    (splitComponentStatement F (Standard.leviScheme i ν (rootSet i ν I))
      hl.isConnectedReductive).1
  exact ⟨⟨A, a, parabolicRootPresentationOfDynamicStructure
    hminimal relativeRootNegation hPD
    (dynamicGeometricUnipotentRadical_of_centralizer dynamicCentralizerReductive)
    hG hp hl ha⟩⟩

section Topology

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

local instance standardCompressionGeometryAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardCompressionGeometryAmbientTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance standardCompressionGeometryLeviClosed :
    IsClosedImmersion (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)
local instance standardCompressionGeometryLeviAffine :
    IsAffine (Standard.leviScheme i ν (rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν I)).hom.hom.left
local instance standardCompressionGeometryLeviTopology :
    TopologicalSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (rootSet i ν I)).X

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A semidirect decomposition of the literal standard groups is also one
of the exact represented standard groups. -/
theorem standardCompression_semidirect
    (h : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I)) :
    IsSemidirectDecomposition
      (ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)))
      (parabolicLeviPointSubgroup (Standard.parabolicHom i ν (rootSet i ν I))
        (Standard.leviToParabolic i ν (rootSet i ν I)))
      (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
        (Standard.unipotentToParabolic i ν (rootSet i ν I))) := by
  rw [standardCompression_parabolicPoints, standardCompression_leviPoints,
    standardCompression_unipotentPoints]
  exact h

/-- The exact represented standard radical is closed. -/
theorem standardCompression_radical_isClosed :
    IsClosed (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.unipotentToParabolic i ν (rootSet i ν I)) : Set (rationalPoints G)) := by
  rw [standardCompression_unipotentPoints]
  exact isClosed_unipotent_of_isNonarchimedeanLocalField i ν I

variable
  (hR : IsSemidirectDecomposition
    (ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)))
    (parabolicLeviPointSubgroup (Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.leviToParabolic i ν (rootSet i ν I)))
    (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
      (Standard.unipotentToParabolic i ν (rootSet i ν I))))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- Every semidirect witness on the represented standard groups has the
continuous canonical standard projection. -/
theorem continuous_standardCompression_projection
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : Continuous hR.projection := by
  revert hR
  rw [standardCompression_parabolicPoints, standardCompression_leviPoints,
    standardCompression_unipotentPoints]
  intro hR
  have heq : hR = isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I := Subsingleton.elim _ _
  subst hR
  exact continuous_standard_projection i ν hStandard hG hi hν I

/-- Dynamic quotient compactness supplies compactness for the exact
represented standard parabolic quotient. -/
theorem compactSpace_standardCompression_leftQuotient
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) :
    CompactSpace (Induction.LeftQuotient
      (ParabolicPoints (Standard.parabolicHom i ν (rootSet i ν I)))) := by
  rw [standardCompression_parabolicPoints]
  exact compactSpace_leftQuotient_parabolic i ν hcompact hStandard hG hi hν I

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [NonarchimedeanGroup (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))]
  [Mono i.hom.hom.left]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)}
  (r : ParabolicRootPresentation (Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.leviToParabolic i ν (rootSet i ν I)) a)
  [Fintype (SimpleRoot (standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν)]
  (hOwn : ∀ J, IsSemidirectDecomposition
    (parabolic (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J)
    (levi (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J)
    (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J))
  (hUL : ∀ J, IsClosed (unipotent (standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν J :
      Set (rationalPoints (Standard.leviScheme i ν (rootSet i ν I)))))
  (hUR : IsClosed (UnipotentPoints (p := Standard.parabolicHom i ν (rootSet i ν I))
    (Standard.unipotentToParabolic i ν (rootSet i ν I)) : Set (rationalPoints G)))

set_option maxHeartbeats 800000 in
/-- The ambient actual root system and named global statements supply the
native Jacquet inputs at each canonical standard Levi. All local geometric
premises of the general native-input constructor are discharged internally. -/
theorem standardCompression_nativeJacquetInputs_of_statements
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hStandard : StandardCocharacterStatement.{u})
    (hcompact : BruhatTits.DynamicParabolicQuotientCompactStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
    (hAdm : RationalPointsIrreducibleAdmissibleStatement.{u, max u uV})
    (hJac : RationalSupercuspidalJacquetFamilyFiniteStatement.{u, max u uV}) :
    RationalCuspidalNativeJacquetInputs.{u, uV} r hR hUR
      (standardLeviTorusFactor i ν (rootSet i ν I)
        (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))) ν hOwn hUL := by
  obtain ⟨hp, hl, hn, -⟩ :=
    RepresentedParabolic.standard_representatives_geometric i ν hPD hStandard hG hi hν I
  have hL := hl.isConnectedReductive
  have := hL.smooth
  let j := standardLeviTorusFactor i ν (rootSet i ν I)
    (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
  have hj : IsMaximalSplitTorus j :=
    hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν I)
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  have := hj.isSplitSubtorus.mono
  have hνL : IsGenericCocharacter j ν :=
    (standardLeviStandardFamilies dynamicLie hStandard F G hG T i hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) _ hL
      (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))).2.1
  have hRootsL : HasRelativeRootSystem j :=
    hRoots.of_standardLeviTorusFactor hStandard hG hi ν hν (rootSet i ν I)
      (rootSet_subset i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I))
  exact rationalCuspidalNativeJacquetInputs_of_statements r j ν hOwn hUL
    hR hUR hPD hconj hL hj hνL hRootsL hG hn
    (continuous_standardCompression_projection i ν I hR hStandard hG hi hν)
    (compactSpace_standardCompression_leftQuotient i ν I hcompact hStandard hG hi hν)
    hAdm hJac

end Topology

end Langlands.Aubert.General.RationalPointFamily
