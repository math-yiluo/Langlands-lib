import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.SharpConsequenceStatements
import Mathlib.NumberTheory.LocalField.Basic

/-! # Finite-length and irreducible consequences on the actual rational points -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The finite-length obligation for `E#` on the actual standard families: the
actual terminal cokernel of a finite-length smooth representation of the
rational points has finite length. No proof is supplied. -/
def RationalSharpFiniteLengthStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpFiniteLengthTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)

/-- Corollaire 3.9 (a), extended to the actual support category: for a
finite-length `E` in the actual support category of `L_I` whose actual `E#` has
finite length, `D_G([E]) = (-1)^{|I|} [E#]` in the exact finite-length
Grothendieck group of the rational points, for every proof of the finite-length
preservation used to build `D_G`. No proof is supplied. -/
def RationalSharpClassFormulaStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpClassFormulaTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)
        (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Retention of the support type on the actual families: the actual terminal
cokernel of a member of the actual support category of `L_I` lies in the same
support category. No proof is supplied. -/
def RationalSharpSupportRetentionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpSupportRetentionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)
        (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Corollaire 3.9 (b) on the actual families: for `E` in the actual cuspidal
series of `L_I`, the actual terminal cokernel `E#` is irreducible. No proof is
supplied. -/
def RationalSharpIrreducibleStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpIrreducibleTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)
        (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- Retention of the cuspidal series on the actual families: for `E` in the
actual cuspidal series of `L_I`, `E#` lies in the actual cuspidal series of a
standard Levi `L_{I'}` associated to `L_I` by an actual normalizer
representative. No proof is supplied. -/
def RationalSharpCuspidalSeriesStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpCuspidalSeriesTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)
        (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
        (IsAssociate := rootAssociation i ν hN hZ)

/-- Corollaire 3.9 (c) on the actual families: for `E` in the actual cuspidal
series of `L_I`, `(E#)#` is isomorphic to `E`, both cokernels taken at degree
`|S| - |I|`. No proof is supplied. -/
def RationalSharpInvolutionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hOrder : StandardParabolicOrderStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I)),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)],
      SharpInvolutionTarget.{u, u, max (u + 1) v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hclosed := hU)
        (hδ := standardUnipotent_isUnimodular i ν hU hUc)
        (hP := standardParabolic_monotone i ν hOrder hG hi hν)
        (hU := standardUnipotent_antitone i ν hOrder hG hi hν)
        (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

end Langlands.Aubert.General.RationalPointFamily
