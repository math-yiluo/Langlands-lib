import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget

/-! # Comparing the map and actual-class forms of induced Weyl conjugacy -/

noncomputable section

universe uI uG uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open SmoothRep

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {RootIndex : Type uI}
variable (T : Subgroup G) (P M U : Finset RootIndex → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))

/-- Evaluate the map-level identity on each actual finite-length object. -/
theorem inducedClassWeylConjugacy_of_inducedK0WeylConjugacy
    (hK0 : inducedK0WeylConjugacy.{uI, uG, uV} T P M U h hU hfl) :
    inducedClassWeylConjugacy.{uI, uG, uV} T P M U h hU hfl := by
  intro I J n hIJ σ
  have hσn := pullbackFunctor_preservesFiniteLength (conjugationEquiv (n : G) hIJ)
    σ.val σ.property
  calc
    _ = (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1)
        (FiniteLengthGrothendieckGroup.ofRepresentation
          ((conjugationFunctor (n : G) hIJ).obj σ.val) hσn) :=
      (inductionK0_ofRepresentation _ _ _ _ _ hσn).symm
    _ = (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1)
        (conjugationK0 (n : G) hIJ
          (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)) :=
      congrArg _ (conjugationK0_ofRepresentation _ _ _ _ hσn).symm
    _ = (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1)
        (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property) :=
      LinearMap.congr_fun (hK0 I J n hIJ) _
    _ = _ := inductionK0_ofRepresentation _ _ _ _ _ _

/-- Actual finite-length objects generate the exact Grothendieck group. -/
theorem inducedK0WeylConjugacy_of_inducedClassWeylConjugacy
    (hclass : inducedClassWeylConjugacy.{uI, uG, uV} T P M U h hU hfl) :
    inducedK0WeylConjugacy.{uI, uG, uV} T P M U h hU hfl := by
  intro I J n hIJ
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (M I)
  intro σ
  have hσn := pullbackFunctor_preservesFiniteLength (conjugationEquiv (n : G) hIJ)
    σ.val σ.property
  change
    (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1)
      (conjugationK0 (n : G) hIJ
        (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)) =
    (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1)
      (FiniteLengthGrothendieckGroup.ofRepresentation σ.val σ.property)
  calc
    _ = (inductionK0 (h J) (hU J) (hfl J).1 (hfl J).2.1)
        (FiniteLengthGrothendieckGroup.ofRepresentation
          ((conjugationFunctor (n : G) hIJ).obj σ.val) hσn) :=
      congrArg _ (conjugationK0_ofRepresentation _ _ _ _ hσn)
    _ = FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor (h J) (hU J)).obj
          ((conjugationFunctor (n : G) hIJ).obj σ.val)) ((hfl J).1 _ hσn) :=
      inductionK0_ofRepresentation _ _ _ _ _ hσn
    _ = _ := hclass I J n hIJ σ
    _ = _ := (inductionK0_ofRepresentation
      (h I) (hU I) (hfl I).1 (hfl I).2.1 σ.val σ.property).symm

/-- The two formulations impose exactly the same identity. -/
theorem inducedK0WeylConjugacy_iff_inducedClassWeylConjugacy :
    inducedK0WeylConjugacy.{uI, uG, uV} T P M U h hU hfl ↔
      inducedClassWeylConjugacy.{uI, uG, uV} T P M U h hU hfl :=
  ⟨inducedClassWeylConjugacy_of_inducedK0WeylConjugacy T P M U h hU hfl,
    inducedK0WeylConjugacy_of_inducedClassWeylConjugacy T P M U h hU hfl⟩

end Generic

namespace RationalPointFamily

open Langlands.AlgebraicGeometry.PointTopology

/-- Specialization of the generator calculation to the full rational target. -/
theorem rationalInducedClassWeylConjugacy_of_inducedK0WeylConjugacy
    (hK0 : RationalInducedK0WeylConjugacyStatement.{u, v}) :
    RationalInducedClassWeylConjugacyStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU hP hproj hUc hiFl hrFl
  exact inducedClassWeylConjugacy_of_inducedK0WeylConjugacy
    _ _ _ _ _ _ _ (hK0 k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl)

/-- The reverse generator argument also preserves the full rational scope. -/
theorem rationalInducedK0WeylConjugacy_of_inducedClassWeylConjugacy
    (hclass : RationalInducedClassWeylConjugacyStatement.{u, v}) :
    RationalInducedK0WeylConjugacyStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hU hP hproj hUc hiFl hrFl
  exact inducedK0WeylConjugacy_of_inducedClassWeylConjugacy
    _ _ _ _ _ _ _ (hclass k G hG T i hi ν hν hStandard hU hP hproj hUc hiFl hrFl)

/-- The internal comparison proposition; it asserts neither identity alone. -/
def RationalInducedWeylClassComparison : Prop :=
    RationalInducedK0WeylConjugacyStatement.{u, v} ↔
      RationalInducedClassWeylConjugacyStatement.{u, v}

/-- The complete rational-point propositions are equivalent. -/
theorem rationalInducedK0WeylConjugacy_iff_inducedClassWeylConjugacy :
    RationalInducedWeylClassComparison.{u, v} :=
  ⟨rationalInducedClassWeylConjugacy_of_inducedK0WeylConjugacy,
    rationalInducedK0WeylConjugacy_of_inducedClassWeylConjugacy⟩

end RationalPointFamily

end Langlands.Aubert.General
