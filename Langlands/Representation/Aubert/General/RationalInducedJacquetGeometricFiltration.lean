import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs
import Langlands.Representation.Aubert.General.RationalGeometricObjectFiltrationConstruction
import Langlands.Representation.Aubert.General.RationalGeometricEpsilonBalance
import Langlands.Representation.Aubert.General.RationalRootSpanCoxeterComparisons

/-! # The actual geometric filtration of `r_J i_I σ` in the extraction-input form -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)

local instance rationalInducedJacquetGeometricFiltrationPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hRoots : HasRelativeRootSystem i)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  [Fintype (SimpleRoot i ν)]

include hRoots hInter in
/-- For an actual point Coxeter system with the root-length and standard-Levi
Weyl comparisons, every actual `r_J i_I σ` has the geometric filtration required
by the extraction inputs. The filtration is the actual ordered support
filtration; the epsilon cancellation is the proved Haar balance. -/
theorem pointInducedJacquetGeometricFiltration_of_leviWeyl [Fintype (Weyl i)]
    {C : CoxeterMatrix (SimpleRoot i ν)} (cs : ActualCoxeterSystem (torusPoints i) C)
    (hIdent : actualLeviWeylIdentification (torusPoints i) (levi i ν) cs)
    (hLength : RootLengthComparison i ν hN hZ cs) :
    PointInducedJacquetGeometricFiltration.{u, v} i ν hStandard hG hi hν hM hU cs := by
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  intro I J σ
  let hP := isClosed_standard_parabolic i ν hStandard hG hi hν
  let hproj := continuous_standard_projection i ν hStandard hG hi hν
  let D := pointGeometricObjectFiltrationOfEpsilonBalance.{u, v}
    i ν hG hi hν hStandard hN hZ cs hIdent hM hU hInter hLength hSimple J I
    (fun _ _ n _ => geometricEpsilon_mul_eq_one i ν hStandard hG hi hν hN hRoots J I _ _ n
      hU hP hM (hproj J) (hproj I)) σ
  refine ⟨D.tailLength + 1, D.filtration, fun q => ?_⟩
  exact ⟨(D.enumeration q).val, (mem_minimalReps cs J I _).mp (D.enumeration q).property,
    D.lift q, D.lift_class q, D.source q, D.target q,
    ⟨SmoothRep.mkIso (Representation.equivOfIso (D.grade q))⟩⟩

include hRoots hInter in
/-- The displayed rational data supply an actual point Coxeter system with the
root-length comparison together with the actual geometric filtration of every
`r_J i_I σ`, the first of the two extraction inputs. -/
theorem exists_pointInducedJacquetGeometricFiltration :
    ∃ (C : CoxeterMatrix (SimpleRoot i ν))
      (cs : ActualCoxeterSystem (torusPoints i) C),
      RootLengthComparison i ν hN hZ cs ∧
        PointInducedJacquetGeometricFiltration.{u, v} i ν hStandard hG hi hν hM hU cs := by
  obtain ⟨hW, -, C, cs, hLength, -, hIdent⟩ :=
    exists_rootSpanPointCoxeterSystem i ν hN hZ hG hi hRoots hν
  let : Fintype (Weyl i) := Fintype.ofFinite _
  exact ⟨C, cs, hLength, pointInducedJacquetGeometricFiltration_of_leviWeyl.{u, v}
    i ν hN hZ hStandard hInter hRoots hG hi hν hM hU cs hIdent hLength⟩

end Langlands.Aubert.General.RationalPointFamily
