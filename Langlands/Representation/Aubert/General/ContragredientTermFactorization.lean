import Langlands.Representation.Aubert.General.ContragredientReduction
import Langlands.Representation.Aubert.General.ConjugateTerms
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # From actual duality isomorphisms to contragredient term comparison -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Two actual duality isomorphisms factor the induction-Jacquet term on the
smooth dual through induction of the supplied Levi object. -/
def inductionJacquetDualityFactorizationIso
    {P M U : Subgroup G}
    (hP : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (B : SmoothRep.{0, uG, max uG uV} ℂ M)
    (hJac : (jacquetFunctor hP hU).obj A.contragredient ≅
      B.contragredient)
    (hInd : ((normalizedInductionFunctor hP hU).obj B).contragredient ≅
      (normalizedInductionFunctor hP hU).obj B.contragredient) :
    (inductionJacquetFunctor.{uG, uV} hP hU).obj A.contragredient ≅
      ((normalizedInductionFunctor hP hU).obj B).contragredient :=
  (normalizedInductionFunctor hP hU).mapIso hJac ≪≫ hInd.symm

/-- Applying the exact-K0 smooth-dual map to an induction class equality
completes the objectwise duality factorization. -/
theorem inductionJacquet_class_eq_of_duality
    {P M U : Subgroup G} (hP : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    (hcof : CompactOpenCofinal G)
    (hc : ContragredientPreservesFiniteLength.{uG, max uG uV} G)
    (A C : SmoothRep.{0, uG, max uG uV} ℂ G)
    (B : SmoothRep.{0, uG, max uG uV} ℂ M)
    (hL : ((inductionJacquetFunctor.{uG, uV} hP hU).obj
      A.contragredient).HasFiniteLength)
    (hPB : ((normalizedInductionFunctor hP hU).obj B).HasFiniteLength)
    (hC : C.HasFiniteLength)
    (hJac : (jacquetFunctor hP hU).obj A.contragredient ≅ B.contragredient)
    (hInd : ((normalizedInductionFunctor hP hU).obj B).contragredient ≅
      (normalizedInductionFunctor hP hU).obj B.contragredient)
    (hclass : FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor hP hU).obj B) hPB =
      FiniteLengthGrothendieckGroup.ofRepresentation C hC) :
    FiniteLengthGrothendieckGroup.ofRepresentation
        ((inductionJacquetFunctor.{uG, uV} hP hU).obj A.contragredient) hL =
      FiniteLengthGrothendieckGroup.ofRepresentation C.contragredient (hc C hC) := by
  have hDualClass := congrArg (contragredientK0 G hcof hc) hclass
  rw [contragredientK0_ofRepresentation, contragredientK0_ofRepresentation] at hDualClass
  have hFactor :
      FiniteLengthGrothendieckGroup.ofRepresentation
          ((inductionJacquetFunctor.{uG, uV} hP hU).obj A.contragredient) hL =
        FiniteLengthGrothendieckGroup.ofRepresentation
          (((normalizedInductionFunctor hP hU).obj B).contragredient) (hc _ hPB) :=
    FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
      (inductionJacquetDualityFactorizationIso.{uG, uV} hP hU A B hJac hInd)
  exact hFactor.trans hDualClass

set_option maxHeartbeats 800000 in
/-- Actual duality, opposite-induction class equality, and actual subgroup
conjugation imply the previously published term comparison. Every
representation-theoretic input remains explicit. -/
theorem contragredientTermComparison_of_duality
    {ι : Type uI} [Fintype ι]
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hcof : CompactOpenCofinal G)
    (hc : ContragredientPreservesFiniteLength.{uG, max uG uV} G)
    (Q V : Finset ι → Subgroup G)
    (hQ : ∀ I, IsSemidirectDecomposition (Q I) (M I) (V I))
    (hV : ∀ I, IsClosed (V I : Set G))
    (hrQ : ∀ I, PreservesFiniteLength
      (jacquetFunctor.{uG, max uG uV} (hQ I) (hV I)))
    (e : Finset ι ≃ Finset ι) (hcard : ∀ I, (e I).card = I.card)
    (g : Finset ι → G)
    (hQP : ∀ I (x : G), x ∈ P (e I) ↔ (g I)⁻¹ * x * g I ∈ Q I)
    (hMM : ∀ I (x : G), x ∈ M (e I) ↔ (g I)⁻¹ * x * g I ∈ M I)
    (hVU : ∀ I (x : G), x ∈ U (e I) ↔ (g I)⁻¹ * x * g I ∈ V I)
    (hJac : ∀ I (A : SmoothRep.{0, uG, max uG uV} ℂ G),
      A.HasFiniteLength →
        ((jacquetFunctor (h I) (hU I)).obj A.contragredient ≅
          ((jacquetFunctor (hQ I) (hV I)).obj A).contragredient))
    (hInd : ∀ I (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)),
      σ.HasFiniteLength →
        (((normalizedInductionFunctor (h I) (hU I)).obj σ).contragredient ≅
          (normalizedInductionFunctor (h I) (hU I)).obj σ.contragredient))
    (hclass : ∀ I (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I))
      (_hσ : σ.HasFiniteLength)
      (hσQ : ((normalizedInductionFunctor (hQ I) (hV I)).obj σ).HasFiniteLength)
      (hσP : ((normalizedInductionFunctor (h I) (hU I)).obj σ).HasFiniteLength),
      FiniteLengthGrothendieckGroup.ofRepresentation
          ((normalizedInductionFunctor (hQ I) (hV I)).obj σ) hσQ =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((normalizedInductionFunctor (h I) (hU I)).obj σ) hσP) :
    ContragredientTermComparison P M U h hU hfl hc := by
  refine ⟨e, hcard, ?_⟩
  intro I A hA
  let B := (jacquetFunctor (hQ I) (hV I)).obj A
  have hB : B.HasFiniteLength := hrQ I A hA
  have hPB : ((normalizedInductionFunctor (h I) (hU I)).obj B).HasFiniteLength :=
    (hfl I).1 B hB
  let E := (inductionJacquetConjugationIso.{uG, uV} (hQ I) (h (e I)) (g I)
    (hQP I) (hMM I) (hVU I) (hV I) (hU (e I))).app A
  have hTerm : ((inductionJacquetFunctor.{uG, uV}
      (h (e I)) (hU (e I))).obj A).HasFiniteLength :=
    inductionJacquet_hasFiniteLength P M U h hU hfl (e I) A hA
  have hQB : ((normalizedInductionFunctor (hQ I) (hV I)).obj B).HasFiniteLength :=
    hasFiniteLength_of_iso E.symm hTerm
  have hQToTerm :
      FiniteLengthGrothendieckGroup.ofRepresentation
          ((normalizedInductionFunctor (hQ I) (hV I)).obj B) hQB =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((inductionJacquetFunctor.{uG, uV} (h (e I)) (hU (e I))).obj A) hTerm :=
    FiniteLengthGrothendieckGroup.ofObject_eq_of_iso E
  have hClassToTerm :
      FiniteLengthGrothendieckGroup.ofRepresentation
          ((normalizedInductionFunctor (h I) (hU I)).obj B) hPB =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((inductionJacquetFunctor.{uG, uV} (h (e I)) (hU (e I))).obj A) hTerm :=
    (hclass I B hB hQB hPB).symm.trans hQToTerm
  exact inductionJacquet_class_eq_of_duality.{uG, uV} (h I) (hU I) hcof hc A
    ((inductionJacquetFunctor.{uG, uV} (h (e I)) (hU (e I))).obj A) B
    (inductionJacquet_hasFiniteLength P M U h hU hfl I A.contragredient (hc A hA))
    hPB hTerm (hJac I A hA) (hInd I B hB) hClassToTerm

end Langlands.Aubert.General
