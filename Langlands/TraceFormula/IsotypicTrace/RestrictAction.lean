import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Restriction of an isometric action to a closed invariant subspace

For an action `π` of a group `A` by bounded operators on a Hilbert space `E` and a complete
invariant subspace `P`, `restrictAction π P hP` is the action on `P`. It preserves inner products
if `π` does; it has no closed invariant subspaces other than `⊥` and `⊤` if `P` has no closed
invariant subspaces of `E` other than `⊥` and `P` (`restrictAction_irreducible`); and the
compression to `P` of the integral of `π` against an integrable function is the integral of the
restricted action (`compression_integratedIsometricAction`).
-/

noncomputable section

open MeasureTheory

namespace Langlands.TraceFormula.IsotypicTrace

universe uA uE

variable {A : Type uA} [Group A]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (π : A →* (E →L[ℂ] E)) (P : Submodule ℂ E) [CompleteSpace P]
  (hP : ∀ a, ∀ x ∈ P, π a x ∈ P)

/-- The action on a complete invariant subspace. -/
def restrictAction : A →* (P →L[ℂ] P) where
  toFun a := ((π a).comp P.subtypeL).codRestrict P (fun x => hP a x x.2)
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    change π (a * b) x = π a (π b x)
    rw [map_mul]
    rfl

omit [CompleteSpace E] [CompleteSpace P] in
@[simp]
theorem restrictAction_apply (a : A) (x : P) : (restrictAction π P hP a x : E) = π a x := rfl

omit [CompleteSpace E] [CompleteSpace P] in
theorem restrictAction_inner (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (a : A) (x y : P) :
    inner ℂ (restrictAction π P hP a x) (restrictAction π P hP a y) = inner ℂ x y := by
  rw [Submodule.coe_inner, Submodule.coe_inner, restrictAction_apply, restrictAction_apply,
    hπinner]

omit [CompleteSpace E] in
/-- Irreducibility passes to the restricted action. -/
theorem restrictAction_irreducible
    (hirr : ∀ Q : Submodule ℂ E, Q ≤ P → IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = P) :
    ∀ Q : Submodule ℂ P, IsClosed (Q : Set P) →
      (∀ a, ∀ x ∈ Q, restrictAction π P hP a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  intro Q hQ hQinv
  have hPclosed : IsClosed (P : Set E) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
  let Q' : Submodule ℂ E := Q.map P.subtype
  have hQ'le : Q' ≤ P := Submodule.map_subtype_le P Q
  have hQ'closed : IsClosed (Q' : Set E) := by
    have : (Q' : Set E) = Subtype.val '' (Q : Set P) := by
      ext x
      simp [Q']
    rw [this]
    exact hPclosed.isClosedEmbedding_subtypeVal.isClosedMap _ hQ
  have hQ'inv : ∀ a, ∀ x ∈ Q', π a x ∈ Q' := by
    rintro a _ ⟨q, hq, rfl⟩
    exact ⟨restrictAction π P hP a q, hQinv a q hq, rfl⟩
  rcases hirr Q' hQ'le hQ'closed hQ'inv with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    have : (q : E) ∈ Q' := ⟨q, hq, rfl⟩
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro q _
    have : (q : E) ∈ Q' := by rw [h]; exact q.2
    obtain ⟨q', hq', hqq'⟩ := this
    rwa [Subtype.ext hqq'] at hq'

variable [MeasurableSpace A] (ν : Measure A)

/-- The compression to `P` of an integrated isometric action is the integrated restricted
action. -/
theorem compression_integratedIsometricAction (hπnorm : ∀ a x, ‖π a x‖ = ‖x‖)
    (hπmeas : ∀ x : E, AEStronglyMeasurable (fun a => π a x) ν)
    (hπPnorm : ∀ a (x : P), ‖restrictAction π P hP a x‖ = ‖x‖)
    (hπPmeas : ∀ x : P, AEStronglyMeasurable (fun a => restrictAction π P hP a x) ν)
    (f : A → ℂ) (hf : Integrable f ν) :
    P.orthogonalProjectionOnto ∘L
        Langlands.Analysis.integratedIsometricAction ν π hπnorm hπmeas f hf ∘L P.subtypeL =
      Langlands.Analysis.integratedIsometricAction ν (restrictAction π P hP) hπPnorm hπPmeas
        f hf := by
  ext1 x
  have hint := Langlands.Analysis.isometricActionIntegrand_integrable ν (restrictAction π P hP)
    hπPnorm hπPmeas f hf x
  have hval : (Langlands.Analysis.integratedIsometricAction ν π hπnorm hπmeas f hf (x : E)) =
      ((Langlands.Analysis.integratedIsometricAction ν (restrictAction π P hP) hπPnorm hπPmeas
        f hf x : P) : E) := by
    rw [Langlands.Analysis.integratedIsometricAction_apply,
      Langlands.Analysis.integratedIsometricAction_apply]
    rw [show ((∫ g, f g • restrictAction π P hP g x ∂ν : P) : E) =
      P.subtypeL (∫ g, f g • restrictAction π P hP g x ∂ν) from rfl,
      ← P.subtypeL.integral_comp_comm hint]
    rfl
  change P.orthogonalProjectionOnto
    (Langlands.Analysis.integratedIsometricAction ν π hπnorm hπmeas f hf (x : E)) = _
  rw [hval]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

section Nested

variable {L : Type uE} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  (S : Submodule ℂ L) [CompleteSpace S] (P : Submodule ℂ S) [CompleteSpace P]

/-- The operator on a subspace `P` of a subspace `S` of `L` induced by an operator on `L`. -/
def nestedRestrict (J : L →L[ℂ] L) : P →L[ℂ] P :=
  P.orthogonalProjectionOnto ∘L (S.orthogonalProjectionOnto ∘L J ∘L S.subtypeL) ∘L P.subtypeL

omit [CompleteSpace L] in
/-- If `J` maps `P` into `P`, the induced operator is `J` on `P`. -/
theorem nestedRestrict_val (J : L →L[ℂ] L) (hJ : ∀ x ∈ P, ∃ y ∈ P, (y : L) = J (x : L))
    (x : P) : (((nestedRestrict S P J x : P) : S) : L) = J ((x : S) : L) := by
  obtain ⟨y, hyP, hy⟩ := hJ (x : S) x.2
  have h1 : S.orthogonalProjectionOnto (J ((x : S) : L)) = y := by
    rw [← hy]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y
  have h2 : nestedRestrict S P J x = ⟨y, hyP⟩ := by
    change P.orthogonalProjectionOnto (S.orthogonalProjectionOnto (J ((x : S) : L))) = _
    rw [h1]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y, hyP⟩
  rw [h2]
  exact hy

omit [CompleteSpace L] in
/-- The compression to `P` of `R ∘ J` is the compression of `R` composed with the operator
induced by `J`, when `J` preserves `P` and `R` preserves `S`. -/
theorem nested_compression_comp (J : L →L[ℂ] L) (hJ : ∀ x ∈ P, ∃ y ∈ P, (y : L) = J (x : L))
    (RL : L →L[ℂ] L) (RS : S →L[ℂ] S) (hRS : ∀ x : S, (RS x : L) = RL x) :
    P.orthogonalProjectionOnto ∘L (S.orthogonalProjectionOnto ∘L (RL ∘L J) ∘L S.subtypeL) ∘L
        P.subtypeL =
      (P.orthogonalProjectionOnto ∘L RS ∘L P.subtypeL) ∘L nestedRestrict S P J := by
  ext1 x
  change P.orthogonalProjectionOnto (S.orthogonalProjectionOnto (RL (J ((x : S) : L)))) =
    P.orthogonalProjectionOnto (RS ((nestedRestrict S P J x : P) : S))
  rw [← nestedRestrict_val S P J hJ x, ← hRS]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

omit [CompleteSpace L] in
/-- Covariance passes to the operator induced on `P`. -/
theorem nestedRestrict_covariant (J : L →L[ℂ] L) (hJ : ∀ x ∈ P, ∃ y ∈ P, (y : L) = J (x : L))
    {A : Type uA} [Group A] (πL : A → L →L[ℂ] L) (πS : A →* (S →L[ℂ] S))
    (hπS : ∀ a (x : S), (πS a x : L) = πL a x) (hP : ∀ a, ∀ x ∈ P, πS a x ∈ P)
    (Θ : A → A) (hcov : ∀ a x, J (πL a x) = πL (Θ a) (J x)) (a : A) (x : P) :
    nestedRestrict S P J (restrictAction πS P hP a x) =
      restrictAction πS P hP (Θ a) (nestedRestrict S P J x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [nestedRestrict_val S P J hJ, restrictAction_apply, restrictAction_apply, hπS, hπS, hcov,
    nestedRestrict_val S P J hJ]

end Nested

end Langlands.TraceFormula.IsotypicTrace
