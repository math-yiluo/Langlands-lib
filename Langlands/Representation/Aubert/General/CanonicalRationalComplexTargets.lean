import Langlands.Representation.Aubert.General.CanonicalRationalStructure
import Langlands.Representation.Aubert.General.CanonicalRationalComplex
import Langlands.Representation.Aubert.General.RationalCorrectedTheorem36
import Langlands.Representation.Aubert.General.RationalTerminalJacquet
import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets

/-! # Canonical-form targets of corrected Theorem 3.6, the erratum comparisons and Corollary 3.9 -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- Corrected Theorem 3.6 (erratum, p.4687) for the canonical actual complex:
for every root order and every standard `I`, every smooth representation in the
actual support category of `L_I` has an actual complex that is exact before its
retained terminal term. All structural inputs are published; there is no
hypothesis. No instance is proved. -/
def CanonicalRationalCorrectedTheorem36Statement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] (I : Finset (SimpleRoot i ν)),
        CorrectedTheorem36Statement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν)
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isUnimodular i ν
            (canonicalStandardUnipotent_isClosed hG i ν hi hν)
            (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
              i ν standardCocharacter hG hi hν))
          (standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
          (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
          (rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
            (canonicalPointCentralizerComparison hG i hi))
          (standardParabolic_univ i ν standardParabolicEndpoints hG hi hν)
          (standardUnipotent_univ i ν standardParabolicEndpoints hG hi hν)
          I (canonicalStandardLevi_isClosed i ν I)
          (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν I)

/-- The fixed-Levi equality before display (**) of the erratum (p.4690) for the
canonical actual families, as a natural isomorphism on the full actual support
category. There is no hypothesis. No instance is proved. -/
def CanonicalRationalFixedLeviComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
        TerminalJacquet.FixedLeviComparisonStatement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν)
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
          (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
          (rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
            (canonicalPointCentralizerComparison hG i hi))
          (canonicalStandardLevi_isClosed i ν)
          (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)
          (standardLeviUnipotent_isUnimodular i ν
            (canonicalStandardUnipotent_isClosed hG i ν hi hν)
            (canonicalStandardLevi_isClosed i ν)
            (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν))

/-- Display (**) of the erratum (p.4690) for the canonical actual families: the
associated-Levi Jacquet comparison on the actual normalizer/full-centralizer
quotient, for the canonical Coxeter system and every lift of its longest
representatives. There is no hypothesis. No instance is proved. -/
def CanonicalRationalAssociatedLeviComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
        TerminalJacquet.AssociatedLeviComparisonStatement.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν)
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isUnimodular i ν
            (canonicalStandardUnipotent_isClosed hG i ν hi hν)
            (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
              i ν standardCocharacter hG hi hν))
          (standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
          (standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
          (rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
            (canonicalPointCentralizerComparison hG i hi))
          (canonicalStandardLevi_isClosed i ν)
          (isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)
          (standardLeviUnipotent_isUnimodular i ν
            (canonicalStandardUnipotent_isClosed hG i ν hi hν)
            (canonicalStandardLevi_isClosed i ν)
            (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν))
          (standardParabolic_univ i ν standardParabolicEndpoints hG hi hν)
          (standardUnipotent_univ i ν standardParabolicEndpoints hG hi hν)
          (torusPoints i) (canonicalCoxeterSystem hG i hi ν hν)
          (canonicalAssociatedLeviConjugation hG i hi ν hν)

/-- Finite length of the canonical actual terminal cokernel `E#` of a
finite-length smooth representation, for every standard `I`. There is no
hypothesis. No instance is proved. -/
def CanonicalRationalSharpFiniteLengthStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpFiniteLengthTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)

/-- Corollaire 3.9 (a) (p.2189), extended to the canonical actual support
category: `D_G([E]) = (-1)^{|I|} [E#]` for every proof of the finite-length
preservation used to build `D_G`, as in the existing target. There is no further
hypothesis. No instance is proved. -/
def CanonicalRationalSharpClassFormulaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpClassFormulaTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hL := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)
        (IsAssociate := rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
          (canonicalPointCentralizerComparison hG i hi))

/-- Retention of the support type by the canonical actual terminal cokernel.
There is no hypothesis. No instance is proved. -/
def CanonicalRationalSharpSupportRetentionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpSupportRetentionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hL := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)
        (IsAssociate := rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
          (canonicalPointCentralizerComparison hG i hi))

/-- Corollaire 3.9 (b) (p.2189) for the canonical actual families: for `E` in
the actual cuspidal series of `L_I`, `E#` is irreducible. There is no
hypothesis. No instance is proved. -/
def CanonicalRationalSharpIrreducibleStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpIrreducibleTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hL := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)

/-- Retention of the cuspidal series by the canonical actual terminal cokernel,
up to an associated standard Levi. There is no hypothesis. No instance is
proved. -/
def CanonicalRationalSharpCuspidalSeriesStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpCuspidalSeriesTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hL := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)
        (IsAssociate := rootAssociation i ν (canonicalPointNormalizerComparison hG i hi)
          (canonicalPointCentralizerComparison hG i hi))

/-- Corollaire 3.9 (c) (p.2189) for the canonical actual families: for `E` in
the actual cuspidal series of `L_I`, `(E#)#` is isomorphic to `E`. There is no
hypothesis. No instance is proved. -/
def CanonicalRationalSharpInvolutionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpInvolutionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hclosed := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hδ := standardUnipotent_isUnimodular i ν
          (canonicalStandardUnipotent_isClosed hG i ν hi hν)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν))
        (hP := standardParabolic_monotone i ν standardParabolicOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν standardParabolicOrder hG hi hν)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hL := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)

/-- Each existing actual rational-point target of Families 3 and 4 implies its
canonical form. This is a proof target; nothing is proved here. -/
def CanonicalRationalComplexTargetBridgesStatement : Prop :=
  (RationalCorrectedTheorem36Statement.{u, v} →
      CanonicalRationalCorrectedTheorem36Statement.{u, v}) ∧
    (RationalFixedLeviComparisonStatement.{u, v} →
      CanonicalRationalFixedLeviComparisonStatement.{u, v}) ∧
    (RationalAssociatedLeviComparisonStatement.{u, v} →
      CanonicalRationalAssociatedLeviComparisonStatement.{u, v}) ∧
    (RationalSharpFiniteLengthStatement.{u, v} →
      CanonicalRationalSharpFiniteLengthStatement.{u, v}) ∧
    (RationalSharpClassFormulaStatement.{u, v} →
      CanonicalRationalSharpClassFormulaStatement.{u, v}) ∧
    (RationalSharpSupportRetentionStatement.{u, v} →
      CanonicalRationalSharpSupportRetentionStatement.{u, v}) ∧
    (RationalSharpIrreducibleStatement.{u, v} →
      CanonicalRationalSharpIrreducibleStatement.{u, v}) ∧
    (RationalSharpCuspidalSeriesStatement.{u, v} →
      CanonicalRationalSharpCuspidalSeriesStatement.{u, v}) ∧
    (RationalSharpInvolutionStatement.{u, v} →
      CanonicalRationalSharpInvolutionStatement.{u, v})

end Langlands.Aubert.General.RationalPointFamily
