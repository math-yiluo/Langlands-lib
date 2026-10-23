import Langlands.Representation.Classification.LanglandsData

/-!
# Ordering exponent-preserving matches of regular Langlands data

An equivalence matching the real exponents of two regular tempered data
automatically respects their block orders.
-/

namespace Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

open CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ}
  (d e : T.TemperedLanglandsDatum.{uV, uF} n)

/-- Promote an exponent-preserving block equivalence to an order isomorphism.
Its underlying equivalence is exactly the supplied one. -/
def orderIsoOfExponentEquiv (a : Fin d.shape.length ≃ Fin e.shape.length)
    (ha : ∀ i, d.exponent i = e.exponent (a i)) :
    Fin d.shape.length ≃o Fin e.shape.length where
  toEquiv := a
  map_rel_iff' := by
    intro i j
    calc
      a i ≤ a j ↔ e.exponent (a j) ≤ e.exponent (a i) :=
        e.strictAnti.le_iff_ge.symm
      _ ↔ d.exponent j ≤ d.exponent i := by rw [ha i, ha j]
      _ ↔ i ≤ j := d.strictAnti.le_iff_ge

@[simp]
theorem orderIsoOfExponentEquiv_toEquiv
    (a : Fin d.shape.length ≃ Fin e.shape.length)
    (ha : ∀ i, d.exponent i = e.exponent (a i)) :
    (d.orderIsoOfExponentEquiv e a ha).toEquiv = a := rfl

/-- Strict exponents determine any matching of block indices uniquely. -/
theorem exponentEquiv_unique
    (a b : Fin d.shape.length ≃ Fin e.shape.length)
    (ha : ∀ i, d.exponent i = e.exponent (a i))
    (hb : ∀ i, d.exponent i = e.exponent (b i)) : a = b := by
  apply Equiv.ext
  intro i
  exact e.strictAnti.injective ((ha i).symm.trans (hb i))

/-- An actual rank, exponent and block-isomorphism match supplies the ordered
match requested by regular Langlands-data uniqueness. This lemma assumes the
match; it does not derive it from an irreducible quotient. -/
theorem orderedBlockMatching
    (a : Fin d.shape.length ≃ Fin e.shape.length)
    (h : ∀ i, d.shape.size i = e.shape.size (a i))
    (hc : ∀ i, d.exponent i = e.exponent (a i) ∧
      Nonempty ((h i ▸ d.blocks i) ≅ e.blocks (a i))) :
    ∃ (b : Fin d.shape.length ≃o Fin e.shape.length)
      (k : ∀ i, d.shape.size i = e.shape.size (b i)),
      ∀ i, d.exponent i = e.exponent (b i) ∧
        Nonempty ((k i ▸ d.blocks i) ≅ e.blocks (b i)) := by
  exact ⟨d.orderIsoOfExponentEquiv e a (fun i => (hc i).1), h, hc⟩

end Langlands.PadicField.TopologicalData.TemperedLanglandsDatum
