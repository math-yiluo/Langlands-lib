import Langlands.Representation.Aubert.General.RationalFiniteLengthDuality
import Langlands.Representation.Aubert.General.RationalContragredientReduction
import Langlands.Representation.Aubert.General.ContragredientTermFactorization

/-! # Actual rational-point duality factorization and term comparison -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance rationalContragredientFactorizationPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hInd : RationalNaturalInductionDualityStatement.{u, v})
  (hJac : RationalNaturalJacquetDualityStatement.{u, v})
  (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
  (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})

/-- The actual standard induction-Jacquet term on a finite-length smooth dual
factors through the smooth dual of induction of its actual opposite Jacquet
module. The closed duality and admissibility inputs remain explicit. -/
def finiteLengthInductionJacquetDualityIso
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (hproj : Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrFl : PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU))
    (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
      (RationalPoint k G.X))
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hA : A.HasFiniteLength) :
    let h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I
    let rO := jacquetFunctor.{u, max (u + 1) v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)
    (inductionJacquetFunctor.{u, max (u + 1) v} h hU).obj A.contragredient ≅
      ((normalizedInductionFunctor h hU).obj (rO.obj A)).contragredient := by
  let B := (jacquetFunctor.{u, max (u + 1) v}
    (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
    (isClosed_oppositeUnipotent_localField i ζ)).obj A
  have hB : B.HasFiniteLength :=
    oppositeJacquet_preservesFiniteLength_of_rationalDuality
      i ν hStandard hG hi hν hJac hadmG hadmM I hU ζ hζ hrFl hc A hA
  exact inductionJacquetDualityFactorizationIso.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) hU A B
    (finiteLengthJacquetDualityIso
      i ν hStandard hG hi hν hJac hadmG I hU ζ hζ A hA)
    (finiteLengthInductionDualityIso
      i ν hStandard hG hi hν hInd hadmM I hU hP hproj B hB)

section Family

variable [Mono i.hom.hom.left]
  (hRoots : HasRelativeRootSystem i)
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) (hU I)))
  (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
    (RationalPoint k G.X))

include hRoots hInd hJac hadmG hadmM

/-- The rational duality and admissibility targets give term comparison once
actual opposite-to-standard conjugation and opposite-induction class equality
are proved. The chosen standard cocharacters may be arbitrary. -/
theorem standardContragredientTermComparison_of_rationalDuality
    (ζ : ∀ I : Finset (SimpleRoot i ν),
      {z : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν I) z})
    (e : Finset (SimpleRoot i ν) ≃ Finset (SimpleRoot i ν))
    (hcard : ∀ I, (e I).card = I.card)
    (g : Finset (SimpleRoot i ν) → RationalPoint k G.X)
    (hQP : ∀ I (x : RationalPoint k G.X),
      x ∈ parabolic i ν (e I) ↔ (g I)⁻¹ * x * g I ∈ oppositeParabolic i (ζ I).val)
    (hMM : ∀ I (x : RationalPoint k G.X),
      x ∈ levi i ν (e I) ↔ (g I)⁻¹ * x * g I ∈ levi i ν I)
    (hVU : ∀ I (x : RationalPoint k G.X),
      x ∈ unipotent i ν (e I) ↔ (g I)⁻¹ * x * g I ∈ oppositeUnipotent i (ζ I).val)
    (hclass : ∀ I (σ : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
      (_hσ : σ.HasFiniteLength)
      (hσO : ((normalizedInductionFunctor.{u, max (u + 1) v}
        (opposite_isSemidirectDecomposition
          i ν hStandard hG hi hν I (ζ I).val (ζ I).property)
        (isClosed_oppositeUnipotent_localField i (ζ I).val)).obj σ).HasFiniteLength)
      (hσP : ((normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)).obj σ).HasFiniteLength),
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor
          (opposite_isSemidirectDecomposition
            i ν hStandard hG hi hν I (ζ I).val (ζ I).property)
          (isClosed_oppositeUnipotent_localField i (ζ I).val)).obj σ) hσO =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)).obj σ) hσP) :
    standardContragredientTermComparison
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hc := by
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact contragredientTermComparison_of_duality.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (compactOpenCofinal_of_nonarchimedean _) hc
    (fun I => oppositeParabolic i (ζ I).val)
    (fun I => oppositeUnipotent i (ζ I).val)
    (fun I => opposite_isSemidirectDecomposition
      i ν hStandard hG hi hν I (ζ I).val (ζ I).property)
    (fun I => isClosed_oppositeUnipotent_localField i (ζ I).val)
    (fun I => oppositeJacquet_preservesFiniteLength_of_rationalDuality
      i ν hStandard hG hi hν hJac hadmG hadmM I (hU I)
      (ζ I).val (ζ I).property (hrFl I) hc)
    e hcard g hQP hMM hVU
    (fun I A hA => finiteLengthJacquetDualityIso
      i ν hStandard hG hi hν hJac hadmG I (hU I) (ζ I).val (ζ I).property A hA)
    (fun I σ hσ => finiteLengthInductionDualityIso
      i ν hStandard hG hi hν hInd hadmM I (hU I) (hP I) (hproj I) σ hσ)
    hclass

end Family

end Langlands.Aubert.General.RationalPointFamily
