import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement

/-! # The field hypotheses of Harris's Theorem 1.2 for an auxiliary-valid datum -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField Langlands.GaloisRepresentation

/-- A totally complex intermediate field of a number field is not contained in its
maximal real subfield. -/
theorem not_le_maximalRealSubfield_of_isTotallyComplex {E : Type*} [Field E] [NumberField E]
    (K₀ : IntermediateField ℚ E) [IsTotallyComplex K₀] :
    ¬ K₀.toSubfield ≤ maximalRealSubfield E := by
  intro hle
  have hreal : IsTotallyReal K₀.toSubfield := isTotallyReal_iff_le_maximalRealSubfield.mpr hle
  have hreal' : IsTotallyReal K₀ := hreal
  let w : InfinitePlace K₀ := Classical.choice inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w))
    (IsTotallyReal.isReal w)

/-- In a CM field, the maximal real subfield and any totally complex subfield
generate the whole field. -/
theorem maximalRealSubfield_sup_eq_top_of_isTotallyComplex {E : Type*} [Field E]
    [NumberField E] [IsCMField E] (K₀ : IntermediateField ℚ E) [IsTotallyComplex K₀] :
    (maximalRealSubfield E).toIntermediateField (fun a => by simp) ⊔ K₀ = ⊤ := by
  set E₀ : IntermediateField ℚ E := (maximalRealSubfield E).toIntermediateField (fun a => by simp)
  set S := maximalRealSubfield E
  have hS : S ≤ (E₀ ⊔ K₀).toSubfield := fun x hx => (le_sup_left : E₀ ≤ E₀ ⊔ K₀) hx
  have hprime : (Module.finrank S E).Prime := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]
    exact Nat.prime_two
  rcases (IntermediateField.isSimpleOrder_of_finrank_prime S E hprime).eq_bot_or_eq_top
      (Subfield.extendScalars hS) with h | h
  · exfalso
    apply not_le_maximalRealSubfield_of_isTotallyComplex K₀
    intro x hx
    have hx' : x ∈ Subfield.extendScalars hS :=
      (Subfield.mem_extendScalars hS).mpr ((le_sup_right : K₀ ≤ E₀ ⊔ K₀) hx)
    rw [h, IntermediateField.mem_bot] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact y.2
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.extendScalars hS := h ▸ IntermediateField.mem_top
    exact (Subfield.mem_extendScalars hS).mp hx

/-- The auxiliary-valid datum of Harris's Proposition 4.8 supplies the CM
compositum and the split imaginary quadratic field required by Theorem 1.2. -/
theorem proposition48AuxiliaryTheorem12Field :
    Proposition48AuxiliaryTheorem12FieldStatement.{uF} := by
  intro Q hQ
  obtain ⟨-, hsplit, -, -, hpv, -⟩ := hQ
  have hK₀deg : Module.finrank ℚ Q.K₀ = 2 := hsplit.1
  have hK₀cx : IsTotallyComplex Q.K₀ := hsplit.2.1
  let E₀ : IntermediateField ℚ Q.E :=
    (maximalRealSubfield Q.E).toIntermediateField (fun a => by simp)
  have hE₀ : E₀.toSubfield = maximalRealSubfield Q.E := rfl
  have hreal : IsTotallyReal E₀ := by
    change IsTotallyReal E₀.toSubfield
    rw [hE₀]
    infer_instance
  refine ⟨E₀, hE₀, hreal, hK₀deg, hK₀cx, ?_, ?_⟩
  · exact maximalRealSubfield_sup_eq_top_of_isTotallyComplex Q.K₀
  · rw [residueCharacteristic_eq_of_natCast_mem Q.prime.out hpv]
    exact hsplit

end Langlands.Global.Harris
