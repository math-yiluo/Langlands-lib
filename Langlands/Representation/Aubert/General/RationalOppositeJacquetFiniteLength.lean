import Langlands.Representation.Aubert.General.RationalJacquetDualityStatement
import Langlands.Representation.Aubert.General.DynamicLeviTopology
import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.Smooth.Contragredient.FiniteLengthProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Finite length of actual opposite Jacquet modules from rational duality -/

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

local instance rationalOppositeJacquetPointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

include hStandard hG hi hν

/-- Compact-open cofinality for the literal standard Levi follows from any
standard cocharacter and the actual dynamic-centralizer topology theorem. -/
theorem standardLevi_compactOpenCofinal [IsTopologicalGroup (RationalPoint k G.X)]
    (I : Finset (SimpleRoot i ν)) : CompactOpenCofinal (levi i ν I) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  have hM := (hcompare ζ hζ).2.1
  change CompactOpenCofinal
    ((standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) :
      Subgroup (RationalPoint k G.X))
  rw [hM]
  exact dynamicCentralizer_compactOpenCofinal k G (CommGroupScheme.groupHom ζ ≫ i)

/-- The closed dynamic-Levi admissibility target specializes to the literal
standard Levi; no algebraic model or representation equivalence is assumed. -/
theorem standardLevi_isAdmissible_of_hasFiniteLength
    (hadm : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hA : A.HasFiniteLength) : A.IsAdmissible := by
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ :=
    hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  have hM := (hcompare ζ hζ).2.1
  have htransfer :
      ∀ B : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I),
        B.HasFiniteLength → B.IsAdmissible := by
    change ∀ B : SmoothRep.{0, u, max (u + 1) v} ℂ
      ((standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) :
        Subgroup (RationalPoint k G.X)), B.HasFiniteLength → B.IsAdmissible
    rw [hM]
    exact hadm k G hG (CommGroupScheme.groupHom ζ ≫ i)
  exact htransfer A hA

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- Rational opposite-Jacquet duality transfers standard Jacquet finite length
to the actual opposite Jacquet module. Its admissibility is derived as well. -/
theorem oppositeJacquet_finiteLength_admissible_of_rationalDuality
    (hdual : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrFl : PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU))
    (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
      (RationalPoint k G.X))
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hA : A.HasFiniteLength) :
    let rO := jacquetFunctor.{u, max (u + 1) v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)
    (rO.obj A).HasFiniteLength ∧ (rO.obj A).IsAdmissible := by
  let rP := jacquetFunctor.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν I) hU
  let rO := jacquetFunctor.{u, max (u + 1) v}
    (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
    (isClosed_oppositeUnipotent_localField i ζ)
  change (rO.obj A).HasFiniteLength ∧ (rO.obj A).IsAdmissible
  have hAadm : A.IsAdmissible := hadmG k G hG A hA
  obtain ⟨E, _⟩ := hdual k G hG T i hi ν hν hStandard I hU ζ hζ
  have hdualFl : (rO.obj A).contragredient.HasFiniteLength :=
    hasFiniteLength_of_iso (E A hAadm) (hrFl A.contragredient (hc A hA))
  have hdualAdm : (rO.obj A).contragredient.IsAdmissible :=
    standardLevi_isAdmissible_of_hasFiniteLength
      i ν hStandard hG hi hν hadmM I _ hdualFl
  have hcof : CompactOpenCofinal (levi i ν I) :=
    standardLevi_compactOpenCofinal i ν hStandard hG hi hν I
  have hOadm : (rO.obj A).IsAdmissible :=
    (isAdmissible_contragredient_iff hcof (rO.obj A)).mp hdualAdm
  have hbidualFl : (rO.obj A).contragredient.contragredient.HasFiniteLength :=
    contragredient_hasFiniteLength hcof _ hdualAdm hdualFl
  exact ⟨hasFiniteLength_of_iso (bidualIso hcof _ hOadm).symm hbidualFl, hOadm⟩

/-- The preceding objectwise transfer gives preservation of finite length for
the actual opposite normalized Jacquet functor. -/
theorem oppositeJacquet_preservesFiniteLength_of_rationalDuality
    (hdual : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrFl : PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU))
    (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
      (RationalPoint k G.X)) :
    PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
        (isClosed_oppositeUnipotent_localField i ζ)) :=
  fun A hA =>
    (oppositeJacquet_finiteLength_admissible_of_rationalDuality
      i ν hStandard hG hi hν hdual hadmG hadmM I hU ζ hζ hrFl hc A hA).1

/-- The actual opposite Jacquet object equipped with the derived finite-length
proof, as an object of the existing exact-K0 presentation. -/
def oppositeJacquetFiniteLengthObject
    (hdual : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (hrFl : PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) hU))
    (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
      (RationalPoint k G.X))
    (A : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X)) :
    FiniteLengthObject.{0, u, max (u + 1) v} ℂ (levi i ν I) :=
  ⟨(jacquetFunctor.{u, max (u + 1) v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)).obj A.val,
    oppositeJacquet_preservesFiniteLength_of_rationalDuality
      i ν hStandard hG hi hν hdual hadmG hadmM I hU ζ hζ hrFl hc A.val A.property⟩

end Langlands.Aubert.General.RationalPointFamily
