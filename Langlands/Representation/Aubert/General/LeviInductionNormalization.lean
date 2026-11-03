import Langlands.Representation.Aubert.General.SubgroupOfModulus

/-! # Actual ambient half-modulus in Levi-in-Levi induction -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {M Q L N : Subgroup G}

/-- The actual ambient positive half-modulus, restricted to the copy of `Q`
inside `M`. Its twist is applied after inflation to that entire subgroup. -/
def ambientInductionCharacterInside (hN : IsClosed (N : Set G)) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) :
    Induction.SmoothCharacter ℂ (Q.subgroupOf M) where
  toMonoidHom := (HaarModulus.closedHalfCharacter N hN Q hQN).comp
    (subgroupOfContinuousEquiv hQM).toMonoidHom
  isOpen_ker := (HaarModulus.isOpen_ker_closedHalfCharacter N hN Q hQN).preimage
    (subgroupOfContinuousEquiv hQM).continuous

@[simp]
theorem ambientInductionCharacterInside_apply (hN : IsClosed (N : Set G))
    (hQM : Q ≤ M) (hQN : Q ≤ Subgroup.normalizer (N : Set G))
    (q : Q.subgroupOf M) :
    (ambientInductionCharacterInside hN hQM hQN).toMonoidHom q =
      HaarModulus.closedHalfCharacter N hN Q hQN (subgroupOfContinuousEquiv hQM q) :=
  rfl

/-- The inside induction character is precisely the pullback of the actual
ambient positive half-modulus, including its smoothness certificate. -/
theorem inductionCharacter_subgroupOf_eq_ambient (hM : IsClosed (M : Set G))
    (hN : IsClosed (N : Set G)) (hNM : N ≤ M) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G))
    (hinside : Q.subgroupOf M ≤ Subgroup.normalizer (N.subgroupOf M : Set M)) :
    letI := hM.locallyCompactSpace
    inductionCharacter (N.subgroupOf M) (Q.subgroupOf M)
        (hN.preimage continuous_subtype_val) hinside =
      ambientInductionCharacterInside hN hQM hQN := by
  let := hM.locallyCompactSpace
  have hext (χ ψ : Induction.SmoothCharacter ℂ (Q.subgroupOf M))
      (heq : χ.toMonoidHom = ψ.toMonoidHom) : χ = ψ := by
    cases χ
    cases ψ
    cases heq
    rfl
  have hc : (inductionCharacter (N.subgroupOf M) (Q.subgroupOf M)
      (hN.preimage continuous_subtype_val) hinside).toMonoidHom =
      (ambientInductionCharacterInside hN hQM hQN).toMonoidHom := by
    apply MonoidHom.ext
    intro q
    exact closedHalfCharacter_subgroupOf hM hN hNM hQM hQN q
  exact hext _ _ hc

/-- Levi-in-Levi induction displayed as pullback, inflation, the actual
ambient half-character twist on `Q.subgroupOf M`, then raw smooth induction. -/
def ambientLeviInductionFunctor (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) :
    SmoothRep.{0, uG, uV} ℂ L ⥤ SmoothRep.{0, uG, max uG uV} ℂ M :=
  let := hM.locallyCompactSpace
  SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM) ⋙
    inflationFunctor h ⋙
      (ambientInductionCharacterInside hN hQM hQN).twistFunctor ⋙
        Induction.smoothInductionFunctor (Q.subgroupOf M)

/-- The normalization comparison is equality of actual functors, with the
canonical positive twist retained after inflation. -/
theorem leviNormalizedInductionFunctor_eq_ambient (hM : IsClosed (M : Set G))
    (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hNM : N ≤ M) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) :
    leviNormalizedInductionFunctor.{uG, uV} hM hLM h hN =
      ambientLeviInductionFunctor hM hLM h hN hQM hQN := by
  let := hM.locallyCompactSpace
  unfold leviNormalizedInductionFunctor ambientLeviInductionFunctor
    normalizedInductionFunctor Induction.normalizedSmoothInductionFunctor
  rw [inductionCharacter_subgroupOf_eq_ambient hM hN hNM hQM hQN h.le_normalizer]

/-- Natural normalization comparison for the actual Levi-in-Levi induction
functor and the ambient half-modulus realization. -/
def leviInductionNormalizationIso (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hNM : N ≤ M) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) :
    leviNormalizedInductionFunctor.{uG, uV} hM hLM h hN ≅
      ambientLeviInductionFunctor hM hLM h hN hQM hQN :=
  eqToIso (leviNormalizedInductionFunctor_eq_ambient hM hLM h hN hNM hQM hQN)

/-- Evaluation on the actual function carrier of Levi-in-Levi induction. -/
abbrev leviNormalizedInductionEval (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (A : SmoothRep.{0, uG, uV} ℂ L)
    (f : (leviNormalizedInductionFunctor hM hLM h hN).obj A) (x : M) : A :=
  letI := hM.locallyCompactSpace
  Induction.eval (Q.subgroupOf M)
    (inducingRepresentation h (hN.preimage continuous_subtype_val)
      ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM)).obj A)) f x

/-- Actual covariance expressed with the ambient positive half-modulus.
The Levi projection is the supplied decomposition's projection inside `M`. -/
theorem leviNormalizedInduction_covariant_ambient (hM : IsClosed (M : Set G))
    (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hNM : N ≤ M) (hQM : Q ≤ M)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G))
    (A : SmoothRep.{0, uG, uV} ℂ L)
    (f : (leviNormalizedInductionFunctor hM hLM h hN).obj A)
    (q : Q.subgroupOf M) (x : M) :
    leviNormalizedInductionEval hM hLM h hN A f ((q : M) * x) =
      (HaarModulus.closedHalfCharacter N hN Q hQN
        (subgroupOfContinuousEquiv hQM q) : ℂ) •
        A.representation (subgroupOfContinuousEquiv hLM (h.projection q))
          (leviNormalizedInductionEval hM hLM h hN A f x) := by
  let := hM.locallyCompactSpace
  have hf := normalizedInductionFunctor_covariant h (hN.preimage continuous_subtype_val)
    ((SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM)).obj A) f q x
  rw [closedHalfCharacter_subgroupOf hM hN hNM hQM hQN q] at hf
  exact hf

/-- The actual target-group action remains right translation. -/
theorem leviNormalizedInduction_right_translation (hM : IsClosed (M : Set G))
    (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) (A : SmoothRep.{0, uG, uV} ℂ L)
    (g : M) (f : (leviNormalizedInductionFunctor hM hLM h hN).obj A) (x : M) :
    leviNormalizedInductionEval hM hLM h hN A
        (((leviNormalizedInductionFunctor hM hLM h hN).obj A).representation g f) x =
      leviNormalizedInductionEval hM hLM h hN A f (x * g) :=
  rfl

/-- Morphisms act by postcomposition on the actual function values. -/
theorem leviNormalizedInduction_map_eval (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) {A B : SmoothRep.{0, uG, uV} ℂ L} (φ : A ⟶ B)
    (f : (leviNormalizedInductionFunctor hM hLM h hN).obj A) (x : M) :
    leviNormalizedInductionEval hM hLM h hN B
        (SmoothRep.hom ((leviNormalizedInductionFunctor hM hLM h hN).map φ) f) x =
      SmoothRep.hom φ (leviNormalizedInductionEval hM hLM h hN A f x) :=
  rfl

end Langlands.Aubert.General
