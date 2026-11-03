import Langlands.Representation.Aubert.General.RationalInductionDualityStatement
import Langlands.Representation.Aubert.General.RationalOppositeJacquetFiniteLength

/-! # Finite-length components of the actual rational-point duality targets -/

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

local instance rationalFiniteLengthDualityPointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

/-- A standard cocharacter chosen from the original standard-cocharacter
statement, with its actual root-subset condition retained in the type. -/
def standardCocharacterForDuality (I : Finset (SimpleRoot i ν)) :
    {ζ : cocharacterLattice T // IsStandardCocharacter i ν (rootSet i ν I) ζ} :=
  ⟨Classical.choose
      (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1,
    Classical.choose_spec
      (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1⟩

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]

/-- Restrict one coherent actual induction-duality family to finite-length
objects, deriving its admissibility input from the closed Levi target. -/
def finiteLengthInductionDualityIso
    (hdual : RationalNaturalInductionDualityStatement.{u, v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (hproj : Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hA : A.HasFiniteLength) :
    let F := normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU
    (F.obj A).contragredient ≅ F.obj A.contragredient :=
  (Classical.choose (hdual k G hG T i hi ν hν hStandard I hU hP hproj)) A
    (standardLevi_isAdmissible_of_hasFiniteLength
      i ν hStandard hG hi hν hadmM I A hA)

/-- The selected finite-length induction components retain the original
contravariant naturality on every actual intertwiner. -/
theorem finiteLengthInductionDualityIso_naturality
    (hdual : RationalNaturalInductionDualityStatement.{u, v})
    (hadmM : DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hP : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
    (hproj : Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (A B : SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν I))
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength) (f : A ⟶ B) :
    let F := normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU
    contragredientHom (F.map f) ≫
        (finiteLengthInductionDualityIso
          i ν hStandard hG hi hν hdual hadmM I hU hP hproj A hA).hom =
      (finiteLengthInductionDualityIso
        i ν hStandard hG hi hν hdual hadmM I hU hP hproj B hB).hom ≫
          F.map (contragredientHom f) :=
  (Classical.choose_spec (hdual k G hG T i hi ν hν hStandard I hU hP hproj))
    A B _ _ f

/-- Restrict one coherent actual opposite-Jacquet-duality family to
finite-length ambient objects, deriving admissibility from its closed target. -/
def finiteLengthJacquetDualityIso
    (hdual : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (A : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hA : A.HasFiniteLength) :
    let rP := jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU
    let rO := jacquetFunctor.{u, max (u + 1) v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)
    rP.obj A.contragredient ≅ (rO.obj A).contragredient :=
  (Classical.choose (hdual k G hG T i hi ν hν hStandard I hU ζ hζ)) A
    (hadmG k G hG A hA)

/-- The selected finite-length Jacquet components retain contravariant
naturality for the actual standard and opposite functor maps. -/
theorem finiteLengthJacquetDualityIso_naturality
    (hdual : RationalNaturalJacquetDualityStatement.{u, v})
    (hadmG : RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v})
    (I : Finset (SimpleRoot i ν))
    (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (ζ : cocharacterLattice T) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
    (A B : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength) (f : A ⟶ B) :
    let rP := jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I) hU
    let rO := jacquetFunctor.{u, max (u + 1) v}
      (opposite_isSemidirectDecomposition i ν hStandard hG hi hν I ζ hζ)
      (isClosed_oppositeUnipotent_localField i ζ)
    rP.map (contragredientHom f) ≫
        (finiteLengthJacquetDualityIso
          i ν hStandard hG hi hν hdual hadmG I hU ζ hζ A hA).hom =
      (finiteLengthJacquetDualityIso
        i ν hStandard hG hi hν hdual hadmG I hU ζ hζ B hB).hom ≫
          contragredientHom (rO.map f) :=
  (Classical.choose_spec (hdual k G hG T i hi ν hν hStandard I hU ζ hζ))
    A B _ _ f

end Langlands.Aubert.General.RationalPointFamily
