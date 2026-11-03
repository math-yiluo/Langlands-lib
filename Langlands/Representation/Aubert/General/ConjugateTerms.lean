import Langlands.Representation.Aubert.General.Conjugation

/-! # Conjugate normalized induction-Jacquet terms -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U P' M' U' : Subgroup G}

/-- Conjugating all three subgroups leaves the actual normalized
induction-Jacquet endofunctor naturally isomorphic to the original one. -/
def inductionJacquetConjugationIso (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G)) :
    inductionJacquetFunctor.{uG, uV} h hU ≅ inductionJacquetFunctor h' hU' :=
  Functor.isoWhiskerLeft (jacquetFunctor.{uG, max uG uV} h hU)
      (inductionConjugationIso h h' g hPP' hMM' hUU' hU hU') ≪≫
    (Functor.associator (jacquetFunctor h hU) (conjugationFunctor g hMM')
      (normalizedInductionFunctor h' hU')).symm ≪≫
    Functor.isoWhiskerRight (jacquetConjugationIso h h' g hMM' hUU' hU hU')
      (normalizedInductionFunctor h' hU')

/-- The induced section is translated by `g⁻¹`, and its coinvariant value is
translated by `g`. This is the actual map underlying the natural isomorphism. -/
@[simp]
theorem inductionJacquetConjugationIso_hom_eval
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (f : (inductionJacquetFunctor.{uG, uV} h hU).obj A) (y : G) :
    Induction.eval P' (inducingRepresentation h' hU' ((jacquetFunctor h' hU').obj A))
        (SmoothRep.hom
          ((inductionJacquetConjugationIso h h' g hPP' hMM' hUU' hU hU').hom.app A) f) y =
      coinvariantsTranslate g hUU' A.representation
        (Induction.eval P (inducingRepresentation h hU ((jacquetFunctor h hU).obj A))
          f (g⁻¹ * y)) :=
  rfl

/-- Conjugate actual induction-Jacquet objects have the same exact-K0 class,
for any proofs of finite length of those objects. -/
theorem inductionJacquet_class_eq_of_conjugation
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hA : ((inductionJacquetFunctor.{uG, uV} h hU).obj A).HasFiniteLength)
    (hA' : ((inductionJacquetFunctor.{uG, uV} h' hU').obj A).HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} h hU).obj A) hA =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} h' hU').obj A) hA' :=
  FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((inductionJacquetConjugationIso h h' g hPP' hMM' hUU' hU hU').app A)

/-- The exact-K0 composites of normalized induction and Jacquet restriction
agree for conjugate decompositions. -/
theorem inductionJacquetK0_eq_of_conjugation
    (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (g : G)
    (hPP' : ∀ x : G, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
    (hMM' : ∀ x : G, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
    (hUU' : ∀ x : G, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set G))
    (hfl : ParabolicFiniteLength.{uG, max uG uV} h hU)
    (hfl' : ParabolicFiniteLength.{uG, max uG uV} h' hU') :
    (inductionK0 h hU hfl.1 hfl.2.1).comp (jacquetK0 h hU hfl.2.2.1 hfl.2.2.2) =
      (inductionK0 h' hU' hfl'.1 hfl'.2.1).comp
        (jacquetK0 h' hU' hfl'.2.2.1 hfl'.2.2.2) := by
  rw [inductionK0_comp_jacquetK0 h hU hfl, inductionK0_comp_jacquetK0 h' hU' hfl']
  exact FiniteLengthGrothendieckGroup.map_eq_of_iso
    (inductionJacquetConjugationIso h h' g hPP' hMM' hUU' hU hU') _ _ _ _

end Langlands.Aubert.General
