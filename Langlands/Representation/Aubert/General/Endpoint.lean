import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Induction.SingleBlock

/-! # The actual whole-group term of the Aubert operator -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

open SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

private theorem closedNormalizerCharacter_eq_one_of_eq_bot
    (U : Subgroup G) (hU : IsClosed (U : Set G)) (hbot : U = ⊥)
    (g : Subgroup.normalizer (U : Set G)) :
    HaarModulus.closedNormalizerCharacter U hU g = 1 := by
  let := hU.locallyCompactSpace
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have : Subsingleton U := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj U g = ContinuousMulEquiv.refl U := by
    exact DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U g) = 1
  rw [he]
  simp

private theorem closedHalfCharacter_eq_one_of_eq_bot
    (U : Subgroup G) (hU : IsClosed (U : Set G)) (hbot : U = ⊥)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    HaarModulus.closedHalfCharacter U hU M hMU m = 1 := by
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedNormalizerCharacter U hU ⟨m, hMU m.property⟩ : NNReal) : ℝ) : ℂ) = 1
  rw [closedNormalizerCharacter_eq_one_of_eq_bot U hU hbot]
  simp

private theorem closedInverseHalfCharacter_eq_one_of_eq_bot
    (U : Subgroup G) (hU : IsClosed (U : Set G)) (hbot : U = ⊥)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    HaarModulus.closedInverseHalfCharacter U hU M hMU m = 1 := by
  apply Units.ext
  rw [show (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) =
      (((NNReal.sqrt
        (HaarModulus.closedNormalizerCharacter U hU ⟨m, hMU m.property⟩ : NNReal) : ℝ) : ℂ))⁻¹
    from Jacquet.inverseHalfCharacter_apply _ _]
  rw [closedNormalizerCharacter_eq_one_of_eq_bot U hU hbot]
  simp

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
private theorem endpoint_relations_eq_bot (U : Subgroup G) (hbot : U = ⊥)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    Jacquet.Localization.relations A.representation U 1 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  have hu : (u : G) = 1 := by simpa [hbot] using u.property
  simp [hu]

/-- Coinvariants by a trivial subgroup have their original coefficient module. -/
def endpointCoinvariantsEquiv (U : Subgroup G) (hbot : U = ⊥)
    (A : SmoothRep.{0, uG, uV} ℂ G) :
    Jacquet.Localization.Coinvariants A.representation U 1 ≃ₗ[ℂ] A :=
  (Jacquet.Localization.relations A.representation U 1).quotEquivOfEqBot
    (endpoint_relations_eq_bot U hbot A)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
@[simp] theorem endpointCoinvariantsEquiv_mk (U : Subgroup G) (hbot : U = ⊥)
    (A : SmoothRep.{0, uG, uV} ℂ G) (v : A) :
    endpointCoinvariantsEquiv U hbot A (Jacquet.Localization.mk A.representation U 1 v) = v :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _

/-- At the actual endpoint, both normalizing characters are trivial and the
inducing action is the original action on the trivial-radical quotient. -/
def endpointInducingEquiv {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hM : M = ⊤) (hbot : U = ⊥) (A : SmoothRep.{0, uG, uV} ℂ G) :
    (inducingRepresentation h hU ((jacquetFunctor h hU).obj A)).Equiv
      (A.representation.comp P.subtype) :=
  Representation.Equiv.mk (endpointCoinvariantsEquiv U hbot A) (by
    intro p
    ext q
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 q
    have hp : (h.projection p : G) = (p : G) := by
      have hmem : (p : G) ∈ M := by rw [hM]; trivial
      exact congrArg Subtype.val (h.projection_levi ⟨p, hmem⟩)
    change endpointCoinvariantsEquiv U hbot A
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) •
        ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
          (h.projection p) : ℂˣ) •
          Jacquet.Localization.mk A.representation U 1
            (A.representation (h.projection p) v))) = _
    rw [closedHalfCharacter_eq_one_of_eq_bot U hU hbot,
      closedInverseHalfCharacter_eq_one_of_eq_bot U hU hbot]
    simp only [one_smul, endpointCoinvariantsEquiv_mk]
    exact congrArg (fun g => A.representation g v) hp)

/-- Normalized induction after Jacquet restriction for P=M=G and U=1 is
isomorphic to the original smooth representation, for every smooth object. -/
def endpointInductionJacquetIso {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : P = ⊤) (hM : M = ⊤) (hbot : U = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) :
    (inductionJacquetFunctor h hU).obj A ≅ A :=
  SmoothRep.mkIso ((Induction.smoothInducedEquiv P
    (endpointInducingEquiv h hU hM hbot A)).trans
      (Induction.smoothInducedTopEquiv P hP (A.representation.comp P.subtype)
        A.representation (fun _ => rfl) A.isSmooth))

/-- The actual endpoint term is the identity on the whole exact K0 group. -/
theorem endpoint_inductionK0_comp_jacquetK0 {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : P = ⊤) (hM : M = ⊤) (hbot : U = ⊥)
    (hfl : ParabolicFiniteLength.{uG, max uG uV} h hU) :
    (inductionK0 h hU hfl.1 hfl.2.1).comp
      (jacquetK0 h hU hfl.2.2.1 hfl.2.2.2) = LinearMap.id := by
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ G
  intro A
  change (inductionK0 h hU hfl.1 hfl.2.1)
    ((jacquetK0 h hU hfl.2.2.1 hfl.2.2.2)
      (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
        FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property
  rw [jacquetK0_ofRepresentation, inductionK0_ofRepresentation]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    (endpointInductionJacquetIso h hU hP hM hbot A.val)

end Langlands.Aubert.General
