import Langlands.Representation.Aubert.General.RationalCuspidalGeometricExtraction
import Langlands.Representation.Aubert.General.CuspidalJacquetFactorReduction

/-! # The two remaining inputs of actual rational cuspidal factor extraction -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  [TopologicalSpace k]

local instance rationalCuspidalExtractionInputsPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))

/-- For a supplied actual point Coxeter system, every actual induced Jacquet
object `r_J i_I σ` has a finite zero-to-full filtration whose grades are
actual normalized geometric terms at minimal representatives. -/
def PointInducedJacquetGeometricFiltration
    {C : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) C) : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I)),
    ∃ (r : ℕ) (s : ObjectRepFiltration
        ((jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
          (hU J)).obj
          ((normalizedInductionFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
            (hU I)).obj σ)).obj r),
      ∀ q : Fin r,
        ∃ (w : Weyl i) (_hw : IsMinimal cs J I w)
          (n : Group.RelativeWeyl.normalizer (torusPoints i)) (_hn : QuotientGroup.mk n = w)
          (hs : GeometricSourceDecomposition
            (parabolic i ν) (levi i ν) (unipotent i ν) J I n)
          (ht : GeometricTargetDecomposition
            (parabolic i ν) (levi i ν) (unipotent i ν) J I n),
          Nonempty
            (s.smoothGradedObject q ≅
              (geometricTermFunctor.{u, u, max (u + 1) v}
                (parabolic i ν) (levi i ν) (unipotent i ν) hM hU J I n hs ht).obj σ)

/-- Proper actual standard normalized induction inside each standard Levi has
no irreducible `IsLeviCuspidal` subquotient. The inducing datum is arbitrary. -/
def PointLeviStandardInductionCuspidalExclusion : Prop :=
  ∀ (J : Finset (SimpleRoot i ν)) (K : Finset J), K ≠ Finset.univ →
    letI := (hM J).locallyCompactSpace
    ∀ (ρ : SmoothRep.{0, u, max (u + 1) v} ℂ
        ((levi i ν (leviIndex J K)).subgroupOf (levi i ν J)))
      (τ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J)),
      τ.IsIrreducible →
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU J (hM J)
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J) τ →
      ¬ SmoothRep.IsSubquotient τ
        ((normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J K)
          ((hU (leviIndex J K)).preimage continuous_subtype_val)).obj ρ)

/-- At one displayed datum, a geometric filtration for some actual point
Coxeter system with the root-length comparison, together with proper-standard
induction exclusion, proves extraction from the whole induced object. -/
theorem inducedCuspidalJacquetFactorExtraction_of_filtration_exclusion
    (hRoots : HasRelativeRootSystem i)
    (hFilt : ∃ (C : CoxeterMatrix (SimpleRoot i ν))
      (cs : ActualCoxeterSystem (torusPoints i) C),
      RootLengthComparison i ν hN hZ cs ∧
        PointInducedJacquetGeometricFiltration.{u, v}
          i ν hStandard hG hi hν hM hU cs)
    (hExclude : PointLeviStandardInductionCuspidalExclusion.{u, v}
      i ν hInter hG hi hν hM hU) :
    InducedCuspidalJacquetFactorExtractionTarget.{u, u, max (u + 1) v}
      (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
      (h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν)
      (hU := hU) (hM := hM)
      (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
      (IsAssociate := rootAssociation i ν hN hZ) := by
  obtain ⟨C, cs, hLength, hF⟩ := hFilt
  have hSimple := positiveSimpleReflectionComparison_of_rootLength
    i ν hN hZ cs hi.isSplitSubtorus.1 hRoots hν hLength
  have hGeom := pointCuspidalExtractionGeometry_of_rootComparisons.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hStandard hInter hM hU
  have hProper := pointProperTargetGeometricTermExclusion_of_standardInduction.{u, v}
    i ν cs hGeom.1 hInter hG hi hν hM hU hExclude
  intro I J σ τ hσ hcσ hτ hcτ hsub
  obtain ⟨r, s, hgrades⟩ := hF I J σ
  exact pointCuspidalJacquetFactor_of_geometricFiltration.{u, v}
    i ν hN hZ cs hInter hG hi hν hM hU hGeom hProper I J σ τ _ s
    hσ hcσ hτ hcτ hsub hgrades

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RationalPointFamily

open _root_.AlgebraicGeometry
open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The geometric-filtration and proper-standard exclusion inputs, at exactly
the displayed scope of `RationalCuspidalJacquetFactorExtractionStatement`. -/
def RationalCuspidalExtractionInputsStatement : Prop :=
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
      (∃ (C : CoxeterMatrix (SimpleRoot i ν))
          (cs : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ cs ∧
          PointInducedJacquetGeometricFiltration.{u, v}
            i ν hStandard hG hi hν hM hU cs) ∧
        PointLeviStandardInductionCuspidalExclusion.{u, v}
          i ν hInter hG hi hν hM hU

/-- The two remaining inputs prove the exact rational extraction target.
Exactness, the Coxeter comparisons, the normalizer representative and the
root association are discharged from the displayed data. -/
theorem rationalCuspidalJacquetFactorExtraction_of_inputs
    (hInputs : RationalCuspidalExtractionInputsStatement.{u, v}) :
    RationalCuspidalJacquetFactorExtractionStatement.{u, v} := by
  refine rationalCuspidalJacquetFactorExtractionStatement_iff_induced.mpr ?_
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  obtain ⟨hFilt, hExclude⟩ :=
    hInputs k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
  exact inducedCuspidalJacquetFactorExtraction_of_filtration_exclusion
    i ν hN hZ hStandard hInter hG hi hν hM hU hRoots hFilt hExclude

end Langlands.Aubert.General.RationalPointFamily
