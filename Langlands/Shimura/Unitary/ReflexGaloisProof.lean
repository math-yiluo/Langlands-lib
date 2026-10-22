import Langlands.Shimura.Unitary.ReflexGaloisStatement
import Langlands.FieldTheory.AlgClosedAutomorphismExtensionProof
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

namespace Langlands.Shimura

open IntermediateField

private theorem exists_translation (L : IntermediateField ℚ ℂ) (x : ℂ)
    (hx : Transcendental L x) :
    ∃ e : L⟮x⟯ ≃ₐ[L] L⟮x⟯,
      (e (AdjoinSimple.gen L x) : ℂ) = x + 1 := by
  have hy : Transcendental L (x + 1) := by
    intro hy
    apply hx
    have h := hy.isIntegral.sub (isIntegral_one : IsIntegral L (1 : ℂ))
    simpa only [add_sub_cancel_right] using h.isAlgebraic
  have heq : L⟮x + 1⟯ = L⟮x⟯ := by
    simpa using adjoin_simple_add_algebraMap x (1 : L)
  let e := ((RatFunc.algEquivOfTranscendental x hx).symm.trans
    (RatFunc.algEquivOfTranscendental (x + 1) hy)).trans (equivOfEq heq)
  refine ⟨e, ?_⟩
  change ((RatFunc.algEquivOfTranscendental (x + 1) hy)
    ((RatFunc.algEquivOfTranscendental x hx).symm (AdjoinSimple.gen L x)) : ℂ) = x + 1
  simp

private theorem extend_intermediate_aut
    (hExt : ∀ (K : Type) [Field K] [Algebra K ℂ] (e : K ≃+* K),
      ∃ σ : ℂ ≃+* ℂ, ∀ a : K, σ (algebraMap K ℂ a) = algebraMap K ℂ (e a))
    (L : IntermediateField ℚ ℂ) (A : IntermediateField L ℂ) (e : A ≃ₐ[L] A) :
    ∃ σ : ℂ ≃ₐ[L] ℂ, ∀ a : A, σ (a : ℂ) = (e a : ℂ) := by
  obtain ⟨σ, hσ⟩ := hExt A e.toRingEquiv
  have hbase (z : L) : σ (algebraMap L ℂ z) = algebraMap L ℂ z := by
    have hz := hσ (algebraMap L A z)
    change σ (algebraMap A ℂ (algebraMap L A z)) =
      algebraMap A ℂ (e (algebraMap L A z)) at hz
    rw [e.commutes] at hz
    simpa only [IsScalarTower.algebraMap_apply L A ℂ] using hz
  exact ⟨{ σ with commutes' := hbase }, hσ⟩

private theorem algebraic_mem_of_fixed
    (hExt : ∀ (K : Type) [Field K] [Algebra K ℂ] (e : K ≃+* K),
      ∃ σ : ℂ ≃+* ℂ, ∀ a : K, σ (algebraMap K ℂ a) = algebraMap K ℂ (e a))
    (L : IntermediateField ℚ ℂ) (x : ℂ) (hx : IsAlgebraic L x)
    (hfixed : ∀ σ : ℂ ≃ₐ[L] ℂ, σ x = x) : x ∈ L := by
  let A := algebraicClosure L ℂ
  let a : A := ⟨x, mem_algebraicClosure_iff.mpr hx⟩
  have ha : a ∈ (⊥ : IntermediateField L A) := by
    apply (InfiniteGalois.mem_bot_iff_fixed a).mpr
    intro e
    obtain ⟨σ, hσ⟩ := extend_intermediate_aut hExt L A e
    apply Subtype.ext
    exact (hσ a).symm.trans (hfixed σ)
  obtain ⟨z, hz⟩ := mem_bot.mp ha
  have hz' : (z : ℂ) = x := congrArg (fun z : A => (z : ℂ)) hz
  exact hz' ▸ z.property

private theorem complexFixedField_of_extension
    (hExtension : Langlands.FieldTheory.AlgClosedAutomorphismExtensionStatement.{0, 0}) :
    ComplexFixedFieldStatement := by
  have hExt : ∀ (K : Type) [Field K] [Algebra K ℂ] (e : K ≃+* K),
      ∃ σ : ℂ ≃+* ℂ, ∀ a : K, σ (algebraMap K ℂ a) = algebraMap K ℂ (e a) :=
    fun K _ _ e => hExtension K ℂ e
  intro L
  apply le_antisymm
  · intro x hx
    have hfixed (σ : ℂ ≃ₐ[L] ℂ) : σ x = x := by
      have h := (mem_fixedField_iff _ _).mp hx
      exact h ((fixingSubgroupEquiv L).symm σ).1 ((fixingSubgroupEquiv L).symm σ).2
    by_cases ha : IsAlgebraic L x
    · exact algebraic_mem_of_fixed hExt L x ha hfixed
    · obtain ⟨e, he⟩ := exists_translation L x ha
      obtain ⟨σ, hσ⟩ := extend_intermediate_aut hExt L L⟮x⟯ e
      have hmove : σ x = x + 1 := (hσ (AdjoinSimple.gen L x)).trans he
      have hbad : x = x + 1 := (hfixed σ).symm.trans hmove
      exact False.elim (one_ne_zero (add_left_cancel (hbad.symm.trans (add_zero x).symm)))
  · exact (le_iff_le L.fixingSubgroup L).mpr le_rfl

/-- Every subfield of the complex numbers is the fixed field of its fixing group. -/
theorem complexFixedField : ComplexFixedFieldStatement :=
  complexFixedField_of_extension Langlands.FieldTheory.algClosedAutomorphismExtension

end Langlands.Shimura
