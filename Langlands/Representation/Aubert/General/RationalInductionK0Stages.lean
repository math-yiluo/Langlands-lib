import Langlands.Representation.Aubert.General.InductionK0Stages
import Langlands.Representation.Aubert.General.RationalInductionStages

/-! # Actual rational normalized induction stages on exact K0 -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance rationalInductionK0StagesPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hP : ∀ A, IsClosed (parabolic i ν A : Set (RationalPoint k G.X)))
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hiFl : ∀ A, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν A) (hU A)))
  (J : Finset (SimpleRoot i ν))
  (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hLproj : ∀ I : Finset J,
    Continuous (standardLeviProjection i ν hInter hG hi hν J I))
  (hiLFl : letI := hM.locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)))

local notation "dec" => isSemidirectDecomposition_of_standardCocharacterStatement
  i ν hStandard hG hi hν

include hP hproj hiFl in
private theorem ambientInductionPreservation (A : Finset (SimpleRoot i ν)) :
    PreservesFiniteLength (normalizedInductionFunctor.{u, max (u + 1) v}
      (dec A) (hU A)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max (u + 1) v}
      (dec A) (hU A)) :=
  ⟨hiFl A, normalizedInductionFunctor_preservesShortExact
    (compactOpenCofinal_of_nonarchimedean _) (dec A) (hU A) (hP A) (hproj A)⟩

include hP hLproj hiLFl in
private theorem innerInductionPreservation (I : Finset J) :
    letI := hM.locallyCompactSpace
    PreservesFiniteLength (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val)) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val)) := by
  let _ := hM.locallyCompactSpace
  exact ⟨hiLFl I, normalizedInductionFunctor_preservesShortExact
    (compactOpenCofinal_of_nonarchimedean _)
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    ((hU (leviIndex J I)).preimage continuous_subtype_val)
    ((hP (leviIndex J I)).preimage continuous_subtype_val) (hLproj I)⟩

/-- Actual induction from the ambient fine standard Levi to the coarse standard
Levi, through its literal subgroup copy, with short-exactness derived. -/
def standardLeviInductionK0_of_preservation (I : Finset J) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν (leviIndex J I)) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  leviInductionK0.{u, max (u + 1) v} hM
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I))
    (innerInductionPreservation i ν hInter hG hi hν hU hP J hM hLproj hiLFl I)

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]
  (hUc : ∀ A, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν A))
  (hLUc : ∀ I : Finset J, Jacquet.Localization.IsLimitOfCompactSubgroups
    ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))

include hproj hiFl hUc hLUc in
/-- Rational induction stages hold on the full exact K0 without a supplied
stages or Haar-modulus equation. -/
theorem standardInductionK0_stages (I : Finset J) :
    (inductionK0.{u, max (u + 1) v} (dec J) (hU J) (hiFl J)
        (ambientInductionPreservation i ν hG hi hν hStandard hU hP hproj hiFl J).2).comp
      (standardLeviInductionK0_of_preservation.{u, v}
        i ν hInter hG hi hν hU hP J hM hLproj hiLFl I) =
    inductionK0.{u, max (u + 1) v} (dec (leviIndex J I)) (hU (leviIndex J I))
      (hiFl (leviIndex J I))
      (ambientInductionPreservation
        i ν hG hi hν hStandard hU hP hproj hiFl (leviIndex J I)).2 :=
  inductionK0_comp_leviInductionK0.{u, max (u + 1) v}
    (dec (leviIndex J I)) (dec J) hM
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hU J)
    (innerInductionPreservation i ν hInter hG hi hν hU hP J hM hLproj hiLFl I)
    (ambientInductionPreservation
      i ν hG hi hν hStandard hU hP hproj hiFl (leviIndex J I))
    (ambientInductionPreservation i ν hG hi hν hStandard hU hP hproj hiFl J)
    (standardInductionStagesIso
      i ν hInter hG hi hν hStandard hU hproj hUc J I hM (hLUc I))

include hproj hiFl hUc hLUc in
/-- Literal inner-subgroup form of the rational stages equation. -/
theorem standardInductionK0_comp_restricted (I : Finset J) :
    letI := hM.locallyCompactSpace
    (inductionK0.{u, max (u + 1) v} (dec J) (hU J) (hiFl J)
        (ambientInductionPreservation i ν hG hi hν hStandard hU hP hproj hiFl J).2).comp
      (inductionK0.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val) (hiLFl I)
        (innerInductionPreservation i ν hInter hG hi hν hU hP J hM hLproj hiLFl I).2) =
    (inductionK0.{u, max (u + 1) v} (dec (leviIndex J I)) (hU (leviIndex J I))
      (hiFl (leviIndex J I))
      (ambientInductionPreservation
        i ν hG hi hν hStandard hU hP hproj hiFl (leviIndex J I)).2).comp
      (FiniteLengthGrothendieckGroup.pullback
        (subgroupOfContinuousEquiv
          (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))).symm) :=
  inductionK0_comp_restrictedInductionK0.{u, max (u + 1) v}
    (dec (leviIndex J I)) (dec J) hM
    (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    (hU (leviIndex J I)) (hU J)
    (innerInductionPreservation i ν hInter hG hi hν hU hP J hM hLproj hiLFl I)
    (ambientInductionPreservation
      i ν hG hi hν hStandard hU hP hproj hiFl (leviIndex J I))
    (ambientInductionPreservation i ν hG hi hν hStandard hU hP hproj hiFl J)
    (standardInductionStagesIso
      i ν hInter hG hi hν hStandard hU hproj hUc J I hM (hLUc I))

end Langlands.Aubert.General.RationalPointFamily
