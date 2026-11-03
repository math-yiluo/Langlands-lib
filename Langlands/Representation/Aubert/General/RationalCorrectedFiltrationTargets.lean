import Langlands.Representation.Aubert.General.RationalStandardComplex
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Representation.Aubert.General.RationalRootSignTarget
import Langlands.Representation.Aubert.General.CorrectedFiltrationStatements
import Mathlib.NumberTheory.LocalField.Basic

/-! # Graded corrected-filtration targets on the actual rational points -/

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

/-- Erratum, pp. 4688–4689, with the Ban–Jantzen double-coset correction, on
the actual standard families and the actual relative Weyl group
`N_G(T)/Z_G(T)`: for `E` in the actual support category of `L_I`, a nonzero
graded piece of the support filtration of `r_I(E_J)` at the `i`-th
length-ordered Weyl element `w` forces `w L_I w⁻¹ = L_K` for a standard
`K ⊆ J`. The Coxeter structure is tied to the actual roots and standard Levi
Weyl images. No proof is supplied. -/
def RationalCorrectedGradedVanishingStatement : Prop :=
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
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
      letI : DecidableEq (Weyl i) := Classical.decEq _
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        CorrectedFiltration.CorrectedGradedVanishingTarget.{u, u, max (u + 1) v}
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν)
          (hclosed := hU) (hM := hM)
          (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (IsAssociate := rootAssociation i ν hN hZ)
          (T := torusPoints i) (cs := cs)

/-- Erratum, pp. 4688–4690, with the Ban–Jantzen double-coset correction, on
the actual standard families and the actual relative Weyl group: on every
surviving grade, the graded piece of the support filtration of `r_I(E_J)` is
identified with `Ad(w⁻¹)(r_{L_K}(E))` by surjections with kernel the previous
step, under which the actual Jacquet transitions `r_I(φ^J_{J'})` of the
normalized complex become identity maps. The transitions use the order and
unimodularity supplied by the named structural inputs. No proof is supplied. -/
def RationalCorrectedGradedTransitionStatement : Prop :=
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
      ∀ [LinearOrder (SimpleRoot i ν)] [Fintype (Weyl i)],
      letI : DecidableEq (Weyl i) := Classical.decEq _
      ∀ (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM),
        RootLengthComparison i ν hN hZ cs →
        PositiveSimpleReflectionComparison i ν hN hZ cs →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) cs →
        CorrectedFiltration.CorrectedGradedTransitionTarget.{u, u, max (u + 1) v}
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
          (T := torusPoints i) (cs := cs)

end Langlands.Aubert.General.RationalPointFamily
