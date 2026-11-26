import Langlands.Global.Arithmetic.CMHalfWeightLocalNormControl
import Mathlib.Algebra.Polynomial.Splits

/-! # Splitting of a generating polynomial at finite and real places -/

noncomputable section

namespace Langlands.Global

open _root_.Algebra NumberField _root_.Polynomial Langlands.Global.AdelicFunctoriality
open scoped FiniteExtension

universe u v w x

section Algebraic

variable {E : Type u} {F : Type v} {R : Type w} {L : Type x}
  [Field E] [Field F] [Algebra E F] [Field R] [Field L]
  {b : F} {f : E[X]} {φ : F →+* L} {ι : E →+* R} {j : R →+* L}

private theorem range_le_of_splits (hcomp : φ.comp (algebraMap E F) = j.comp ι)
    (hgen : ∀ x : F, ∃ g : E[X], aeval b g = x) (hb : aeval b f = 0)
    (hf : f ≠ 0) (hs : (f.map ι).Splits) : φ.range ≤ j.range := by
  have hroot : ((f.map ι).map j).IsRoot (φ b) := by
    rw [Polynomial.IsRoot, Polynomial.map_map, eval_map, ← hcomp, ← hom_eval₂,
      ← aeval_def, hb, map_zero]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot (map_ne_zero hf) hroot
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, hg⟩ := hgen x
  refine ⟨g.eval₂ ι a, ?_⟩
  rw [hom_eval₂, ha, ← hcomp, ← hom_eval₂, ← aeval_def, hg]

end Algebraic

section Places

variable {E : Type u} {F : Type v} [Field E] [Field F] [Algebra E F]
  [NumberField E] [NumberField F] {b : F} {f : E[X]}
  (hgen : ∀ x : F, ∃ g : E[X], aeval b g = x) (hb : aeval b f = 0) (hf : f ≠ 0)

include hgen hb hf in
private theorem completionMap_surjective_of_splitGenerator
    (p : FinitePlace E) (q : FinitePlacesAbove F p)
    (hs : (f.map (algebraMap E (FiniteCompletion E p))).Splits) :
    Function.Surjective (FiniteExtension.completionMap p q.val) := by
  let R := FiniteCompletion E p
  let L := FiniteCompletion F q.val
  let φ := algebraMap F L
  let j := FiniteExtension.completionMap p q.val
  have hcomp : φ.comp (algebraMap E F) = j.comp (algebraMap E R) :=
    RingHom.ext fun e => (FiniteExtension.completionMap_coe p q.val e).symm
  have h := range_le_of_splits hcomp hgen hb hf hs
  let : NontriviallyNormedField R := Valued.toNontriviallyNormedField R (WithZero (Multiplicative ℤ))
  have hj : IsClosed (Set.range j) := (LinearMap.isClosedEmbedding_of_injective
    (f := Algebra.linearMap R L) (LinearMap.ker_eq_bot.mpr j.injective)).isClosed_range
  have hd : DenseRange φ := q.val.denseRange_algebraMap F
  intro y
  exact closure_minimal (show Set.range φ ⊆ Set.range j from h) hj (hd y)

/-- The actual completion embedding is an isomorphism when a generating
polynomial splits over the base completion. -/
def completionEquivOfSplitGenerator (p : FinitePlace E) (q : FinitePlacesAbove F p)
    (hs : (f.map (algebraMap E (FiniteCompletion E p))).Splits) :
    FiniteCompletion E p ≃ₐ[FiniteCompletion E p] FiniteCompletion F q.val :=
  AlgEquiv.ofBijective (Algebra.ofId (FiniteCompletion E p) (FiniteCompletion F q.val))
    ⟨(FiniteExtension.completionMap p q.val).injective,
      completionMap_surjective_of_splitGenerator hgen hb hf p q hs⟩

omit [NumberField E] [NumberField F] in
include hgen hb hf in
/-- A generator whose polynomial splits over every real embedding of the
original totally real field generates a totally real field. -/
theorem totallyReal_of_splitGenerator [IsTotallyReal E]
    (hs : ∀ τ : E →+* ℝ, (f.map τ).Splits) : IsTotallyReal F := by
  refine ⟨fun q => InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr ?_)⟩
  let φ := q.embedding
  let ψ := φ.comp (algebraMap E F)
  let hψ := IsTotallyReal.complexEmbedding_isReal ψ
  let ι := hψ.embedding
  have hcomp : φ.comp (algebraMap E F) = Complex.ofRealHom.comp ι :=
    RingHom.ext fun e => (ComplexEmbedding.IsReal.coe_embedding_apply hψ e).symm
  have h := range_le_of_splits hcomp hgen hb hf (hs ι)
  ext x
  obtain ⟨y, hy⟩ := h (show φ x ∈ φ.range from ⟨x, rfl⟩)
  change (starRingEnd ℂ) (φ x) = φ x
  rw [← hy]
  exact Complex.conj_ofReal y

end Places

end Langlands.Global
