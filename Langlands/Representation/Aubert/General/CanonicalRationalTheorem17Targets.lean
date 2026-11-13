import Langlands.Representation.Aubert.General.CanonicalRationalStructure
import Langlands.Representation.Aubert.General.RationalContragredientTarget
import Langlands.Representation.Aubert.General.RationalInductionTarget
import Langlands.Representation.Aubert.General.RationalJacquetTarget
import Langlands.Representation.Aubert.General.RationalInvolutivityTarget
import Langlands.Representation.Aubert.General.RationalCuspidalEigenvalueTarget
import Langlands.Representation.Aubert.General.RationalCorollaryTargets
import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget

/-! # Canonical-form targets of Aubert Theorem 1.7 and Corollary 1.10 on actual rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- Aubert Theorem 1.7(1) for the canonical operator: the smooth contragredient
commutes with the canonical unadjusted operator. The two dynamic finite-length
statements and contragredient finite-length preservation on `G(k)` are the only
hypotheses. No instance is proved. -/
def CanonicalRationalContragredientCommutationStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v})
      (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
        (RationalPoint k G.X)),
      let D := canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl
      let c := contragredientK0.{u, max (u + 1) v} (RationalPoint k G.X)
        (compactOpenCofinal_of_nonarchimedean _) hc
      D.comp c = c.comp D

/-- The induction equation of Aubert Theorem 1.7(2) for the canonical ambient
and standard Levi operators: `D_G ∘ i_{G,M_J} = i_{G,M_J} ∘ D_{M_J}` on exact
finite-length Grothendieck groups, for every subset `J` of actual simple roots.
Only the two dynamic finite-length statements are hypotheses. No instance is
proved. -/
def CanonicalRationalInductionCompatibilityStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      let D := canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl
      ∀ J : Finset (SimpleRoot i ν),
        let hfl := canonicalStandardParabolicFiniteLength.{u, v} hG i ν hi hν hiFl hrFl J
        let ind := inductionK0.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν standardCocharacter hG hi hν J)
          (canonicalStandardUnipotent_isClosed hG i ν hi hν J) hfl.1 hfl.2.1
        let DL := canonicalRationalLeviAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl J
        D.comp ind = ind.comp DL

/-- The Jacquet equation of Aubert Theorem 1.7(2) for the canonical operators:
for every subset `J` of actual simple roots and every lift `n` of the longest
representative of the canonical Coxeter system,
`r_{M_J,G} ∘ D_G = Ad(n)_* ∘ D_{M_{J'}} ∘ r_{M_{J'},G}` with `J'` the
associated subset and the transport supplied by the canonical associated-Levi
conjugation. Every `Fintype` structure on the actual relative Weyl group is
allowed. Only the two dynamic finite-length statements are hypotheses. No
instance is proved. -/
def CanonicalRationalJacquetCompatibilityStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ [Fintype (Weyl i)],
        let cs := canonicalCoxeterSystem hG i hi ν hν
        let D := canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl
        ∀ (J : Finset (SimpleRoot i ν))
          (n : Group.RelativeWeyl.normalizer (torusPoints i))
          (hn : QuotientGroup.mk n = longestRep cs J),
          let J' := associatedSubset cs J
          let hfl := canonicalStandardParabolicFiniteLength.{u, v} hG i ν hi hν hiFl hrFl
          let rJ := jacquetK0.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν standardCocharacter hG hi hν J)
            (canonicalStandardUnipotent_isClosed hG i ν hi hν J) (hfl J).2.2.1 (hfl J).2.2.2
          let rJ' := jacquetK0.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν standardCocharacter hG hi hν J')
            (canonicalStandardUnipotent_isClosed hG i ν hi hν J') (hfl J').2.2.1 (hfl J').2.2.2
          let DL' := canonicalRationalLeviAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl J'
          let transport := conjugationK0.{u, max (u + 1) v}
            (n : RationalPoint k G.X)
            (conjugationMembership_of_map_eq _
              (canonicalAssociatedLeviConjugation hG i hi ν hν J n hn))
          rJ.comp D = transport.comp (DL'.comp rJ')

/-- Aubert Theorem 1.7(3) for the canonical operator: `D_G ∘ D_G = id`. Only the
two dynamic finite-length statements are hypotheses. No instance is proved. -/
def CanonicalRationalInvolutivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      let D := canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl
      D.comp D = LinearMap.id

/-- Aubert Theorem 1.7(4) for the canonical operator: an irreducible
representation all of whose proper standard Jacquet modules vanish is sent to
`(-1)^{|Δ|}` times its class, `Δ` the actual simple roots. Only the two dynamic
finite-length statements are hypotheses. No instance is proved. -/
def CanonicalRationalCuspidalEigenvalueStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
        (hA : A.IsIrreducible),
        (∀ I : Finset (SimpleRoot i ν), I ≠ Finset.univ →
          Limits.IsZero ((jacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν standardCocharacter hG hi hν I)
            (canonicalStandardUnipotent_isClosed hG i ν hi hν I)).obj A)) →
        canonicalRationalAlternatingOperator.{u, v} hG i ν hi hν hiFl hrFl
            (FiniteLengthGrothendieckGroup.ofRepresentation A
              (hasFiniteLength_of_isIrreducible hA)) =
          ((-1 : ℤ) ^ Fintype.card (SimpleRoot i ν)) •
            FiniteLengthGrothendieckGroup.ofRepresentation A
              (hasFiniteLength_of_isIrreducible hA)

/-- Corollary 1.10(a) for the canonical standard rational-point family: the
generic `corollary110a` with the actual standard decompositions, closed
radicals and Levis, and the canonical finite-length package. Only the two
dynamic finite-length statements are hypotheses. No instance is proved. -/
def CanonicalRationalCorollary110aStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      corollary110a.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hU := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hfl := canonicalStandardParabolicFiniteLength hG i ν hi hν hiFl hrFl)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hLevi := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)

/-- Corollary 1.10(b) for the canonical standard rational-point family: the
generic `corollary110b` with the same canonical data as Corollary 1.10(a). Only
the two dynamic finite-length statements are hypotheses. No instance is
proved. -/
def CanonicalRationalCorollary110bStatement : Prop :=
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
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      letI := simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi)
        hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      corollary110b.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (hU := canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (hfl := canonicalStandardParabolicFiniteLength hG i ν hi hν hiFl hrFl)
        (hM := canonicalStandardLevi_isClosed i ν)
        (hLevi := isSemidirectDecomposition_in_levi i ν standardLeviIntersection hG hi hν)

/-- The induced-K0 Weyl conjugacy target of Aubert (1.2) for the canonical
standard rational-point family. Only the two dynamic finite-length statements
are hypotheses. No instance is proved. -/
def CanonicalRationalInducedK0WeylConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : Smooth G.X.hom := hG.smooth
    haveI : T2Space k := BruhatTits.localField_t2Space k
    haveI : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
    haveI : NonarchimedeanGroup (RationalPoint k G.X) :=
      Plancherel.rationalPoints_nonarchimedeanGroup G
    haveI : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
    ∀ (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hiFl : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
      (hrFl : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}),
      inducedK0WeylConjugacy.{u, u, max (u + 1) v}
        (torusPoints i) (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν standardCocharacter hG hi hν)
        (canonicalStandardUnipotent_isClosed hG i ν hi hν)
        (canonicalStandardParabolicFiniteLength hG i ν hi hν hiFl hrFl)

end Langlands.Aubert.General.RationalPointFamily
