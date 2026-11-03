import Langlands.Representation.Aubert.General.Conjugation
import Langlands.Representation.Aubert.General.InducedWeylClassComparison
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Induction from a conjugate decomposition and standard Weyl classes -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

section Transport

variable {Q L V P M U : Subgroup G}
  (hQ : IsSemidirectDecomposition Q L V) (hP : IsSemidirectDecomposition P M U)
  (g : G)
  (hQP : ∀ x : G, x ∈ P ↔ g⁻¹ * x * g ∈ Q)
  (hLM : ∀ x : G, x ∈ M ↔ g⁻¹ * x * g ∈ L)
  (hVU : ∀ x : G, x ∈ U ↔ g⁻¹ * x * g ∈ V)
  (hV : IsClosed (V : Set G)) (hU : IsClosed (U : Set G))
  (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} hP hU))
  (hx : PreservesFiniteLengthShortExact
    (normalizedInductionFunctor.{uG, max uG uV} hP hU))

include hP g hQP hLM hVU hU hl in
/-- An actual induction conjugation isomorphism transports finite length. -/
theorem conjugateInduction_preservesFiniteLength :
    PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} hQ hV) :=
  PreservesFiniteLength.of_iso
    ((pullbackFunctor_preservesFiniteLength (conjugationEquiv g hLM)).comp hl)
    (inductionConjugationIso hQ hP g hQP hLM hVU hV hU).symm

include hP g hQP hLM hVU hU hx in
/-- The same natural isomorphism transports preservation of short exact sequences. -/
theorem conjugateInduction_preservesShortExact :
    PreservesFiniteLengthShortExact
      (normalizedInductionFunctor.{uG, max uG uV} hQ hV) :=
  PreservesFiniteLengthShortExact.of_iso
    (PreservesFiniteLengthShortExact.comp
      (pullbackFunctor_preservesFiniteLength (conjugationEquiv g hLM))
      (pullbackFunctor_preservesShortExact (conjugationEquiv g hLM)) hx)
    (inductionConjugationIso hQ hP g hQP hLM hVU hV hU).symm

/-- The actual induction exact-K0 map, with preservation derived from a
conjugate decomposition rather than supplied again as a hypothesis. -/
def conjugateDecompositionInductionK0 :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ L →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  inductionK0 hQ hV
    (conjugateInduction_preservesFiniteLength hQ hP g hQP hLM hVU hV hU hl)
    (conjugateInduction_preservesShortExact hQ hP g hQP hLM hVU hV hU hx)

/-- Conjugation followed by the known induction map is the constructed map. -/
theorem conjugateDecompositionInductionK0_eq :
    conjugateDecompositionInductionK0 hQ hP g hQP hLM hVU hV hU hl hx =
      (inductionK0 hP hU hl hx).comp (conjugationK0.{uG, max uG uV} g hLM) :=
  (inductionK0_comp_conjugationK0 hQ hP g hQP hLM hVU hV hU
    (conjugateInduction_preservesFiniteLength hQ hP g hQP hLM hVU hV hU hl)
    (conjugateInduction_preservesShortExact hQ hP g hQP hLM hVU hV hU hx)
    hl hx).symm

end Transport

section StandardComparison

variable {ι : Type uI}
  (T : Subgroup G) (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hclass : inducedClassWeylConjugacy.{uI, uG, uV} T P M U h hU hfl)
  (I J : Finset ι) (n : Langlands.Group.RelativeWeyl.normalizer T)
  {Q V : Subgroup G} (hQ : IsSemidirectDecomposition Q (M I) V)
  (hQP : ∀ x : G, x ∈ P J ↔ (n : G)⁻¹ * x * (n : G) ∈ Q)
  (hMM : ∀ x : G, x ∈ M J ↔ (n : G)⁻¹ * x * (n : G) ∈ M I)
  (hVU : ∀ x : G, x ∈ U J ↔ (n : G)⁻¹ * x * (n : G) ∈ V)
  (hV : IsClosed (V : Set G))

include T hclass in
/-- Actual conjugation to a standard decomposition plus standard induced-Weyl
class equality identifies the entire induction exact-K0 map. -/
theorem conjugateDecompositionInductionK0_eq_of_weylConjugacy :
    conjugateDecompositionInductionK0 hQ (h J) (n : G) hQP hMM hVU hV (hU J)
        (hfl J).1 (hfl J).2.1 =
      inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1 := by
  rw [conjugateDecompositionInductionK0_eq]
  exact inducedK0WeylConjugacy_of_inducedClassWeylConjugacy
    T P M U h hU hfl hclass I J n hMM

include T hclass hQP hMM hVU in
/-- The two actual induced representations have equal exact-K0 classes.
The output finite-length witnesses may be any proofs. -/
theorem conjugateInductionClass_eq_of_weylConjugacy
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M I))
    (hσQ : ((normalizedInductionFunctor hQ hV).obj σ.val).HasFiniteLength)
    (hσI : ((normalizedInductionFunctor (h I) (hU I)).obj σ.val).HasFiniteLength) :
    FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor hQ hV).obj σ.val) hσQ =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor (h I) (hU I)).obj σ.val) hσI := by
  calc
    _ = FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor (h J) (hU J)).obj
          ((conjugationFunctor (n : G) hMM).obj σ.val))
        ((hfl J).1 _ (pullbackFunctor_preservesFiniteLength
          (conjugationEquiv (n : G) hMM) σ.val σ.property)) :=
      FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
        ((inductionConjugationIso hQ (h J) (n : G) hQP hMM hVU hV (hU J)).app σ.val)
    _ = _ := hclass I J n hMM σ

end StandardComparison

end Langlands.Aubert.General
