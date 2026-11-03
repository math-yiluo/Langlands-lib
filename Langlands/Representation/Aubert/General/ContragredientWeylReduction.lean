import Langlands.Representation.Aubert.General.ContragredientTermFactorization
import Langlands.Representation.Aubert.General.ConjugateInductionComparison

/-! # Duality term comparison from standard Weyl classes and conjugation -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

section Jacquet

variable {Q L V P M U : Subgroup G}
  (hQ : IsSemidirectDecomposition Q L V) (hP : IsSemidirectDecomposition P M U)
  (g : G)
  (hLM : ∀ x : G, x ∈ M ↔ g⁻¹ * x * g ∈ L)
  (hVU : ∀ x : G, x ∈ U ↔ g⁻¹ * x * g ∈ V)
  (hV : IsClosed (V : Set G)) (hU : IsClosed (U : Set G))
  (hr : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} hP hU))

include hP g hLM hVU hU hr in
/-- Actual Jacquet conjugation reflects finite length through its Levi
group equivalence. No comparison of the parabolic subgroups is needed. -/
theorem conjugateJacquet_preservesFiniteLength :
    PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} hQ hV) := by
  intro A hA
  have hPull :
      ((conjugationFunctor g hLM).obj ((jacquetFunctor hQ hV).obj A)).HasFiniteLength :=
    hasFiniteLength_of_iso
      ((jacquetConjugationIso hQ hP g hLM hVU hV hU).app A).symm (hr A hA)
  exact (FiniteLengthAssembly.finiteLength_comp_surjective_iff
    ((jacquetFunctor hQ hV).obj A).representation
    (conjugationEquiv g hLM).toMonoidHom (conjugationEquiv g hLM).surjective).mpr hPull

/-- The actual conjugate Jacquet object, with its finite-length certificate
derived from Jacquet preservation for the displayed decomposition. -/
def conjugateJacquetFiniteLengthObject
    (A : FiniteLengthObject.{0, uG, max uG uV} ℂ G) :
    FiniteLengthObject.{0, uG, max uG uV} ℂ L :=
  ⟨(jacquetFunctor hQ hV).obj A.val,
    conjugateJacquet_preservesFiniteLength hQ hP g hLM hVU hV hU hr A.val A.property⟩

end Jacquet

set_option maxHeartbeats 800000 in
/-- Standard induced-Weyl class equality and actual subgroup conjugation supply
both the Jacquet-length and induction-class inputs to the duality reduction. -/
theorem contragredientTermComparison_of_duality_of_weylConjugacy
    {ι : Type uI} [Fintype ι]
    (T : Subgroup G) (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
    (hWeyl : inducedClassWeylConjugacy.{uI, uG, uV} T P M U h hU hfl)
    (hcof : CompactOpenCofinal G)
    (hc : ContragredientPreservesFiniteLength.{uG, max uG uV} G)
    (Q V : Finset ι → Subgroup G)
    (hQ : ∀ I, IsSemidirectDecomposition (Q I) (M I) (V I))
    (hV : ∀ I, IsClosed (V I : Set G))
    (e : Finset ι ≃ Finset ι) (hcard : ∀ I, (e I).card = I.card)
    (n : Finset ι → Langlands.Group.RelativeWeyl.normalizer T)
    (hQP : ∀ I (x : G), x ∈ P (e I) ↔ (n I : G)⁻¹ * x * (n I : G) ∈ Q I)
    (hMM : ∀ I (x : G), x ∈ M (e I) ↔ (n I : G)⁻¹ * x * (n I : G) ∈ M I)
    (hVU : ∀ I (x : G), x ∈ U (e I) ↔ (n I : G)⁻¹ * x * (n I : G) ∈ V I)
    (hJac : ∀ I (A : SmoothRep.{0, uG, max uG uV} ℂ G),
      A.HasFiniteLength →
        ((jacquetFunctor (h I) (hU I)).obj A.contragredient ≅
          ((jacquetFunctor (hQ I) (hV I)).obj A).contragredient))
    (hInd : ∀ I (σ : SmoothRep.{0, uG, max uG uV} ℂ (M I)),
      σ.HasFiniteLength →
        (((normalizedInductionFunctor (h I) (hU I)).obj σ).contragredient ≅
          (normalizedInductionFunctor (h I) (hU I)).obj σ.contragredient)) :
    ContragredientTermComparison P M U h hU hfl hc := by
  have hrQ : ∀ I, PreservesFiniteLength
      (jacquetFunctor.{uG, max uG uV} (hQ I) (hV I)) := fun I =>
    conjugateJacquet_preservesFiniteLength (hQ I) (h (e I)) (n I : G)
      (hMM I) (hVU I) (hV I) (hU (e I)) (hfl (e I)).2.2.1
  apply contragredientTermComparison_of_duality.{uI, uG, uV}
    P M U h hU hfl hcof hc Q V hQ hV hrQ e hcard (fun I => (n I : G))
    hQP hMM hVU hJac hInd
  intro I σ hσ hσQ hσP
  exact conjugateInductionClass_eq_of_weylConjugacy.{uI, uG, uV}
    T P M U h hU hfl hWeyl I (e I) (n I) (hQ I)
    (hQP I) (hMM I) (hVU I) (hV I) ⟨σ, hσ⟩ hσQ hσP

end Langlands.Aubert.General
