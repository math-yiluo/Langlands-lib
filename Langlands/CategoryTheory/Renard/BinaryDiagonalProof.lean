import Langlands.CategoryTheory.Renard.BinaryDiagonalStatements
import Langlands.CategoryTheory.Renard.UniversalArrowProof

/-!
# Binary diagonal universal-arrow comparisons

Proofs of the four closed comparisons for Renard A.III.1, example 1,
with the actual supplied paired arrows and binary (co)fans.
-/

open CategoryTheory CategoryTheory.Limits

universe vC uC

namespace Langlands.Renard.BinaryDiagonal

/-- The diagonal's left universal property is simultaneous unique factorization. -/
theorem productFactorizationStatement : ProductFactorizationStatement.{vC, uC} := by
  intro C _ X Y P p q
  rw [← UniversalArrow.leftCharacterization_proof C (C × C)
    (Functor.diag C) (X, Y) P (CategoryTheory.Prod.mkHom p q)]
  constructor
  · intro h Z f g
    obtain ⟨l, hl, hu⟩ := h Z (CategoryTheory.Prod.mkHom f g)
    refine ⟨l, ⟨congrArg (fun k => k.1) hl, congrArg (fun k => k.2) hl⟩, ?_⟩
    intro m hm
    exact hu m (CategoryTheory.Prod.hom_ext hm.1 hm.2)
  · intro h Z fg
    obtain ⟨l, hl, hu⟩ := h Z fg.1 fg.2
    refine ⟨l, CategoryTheory.Prod.hom_ext hl.1 hl.2, ?_⟩
    intro m hm
    exact hu m ⟨congrArg (fun k => k.1) hm, congrArg (fun k => k.2) hm⟩

/-- The same supplied diagonal arrow is universal exactly when its binary fan is limiting. -/
theorem productLimitStatement : ProductLimitStatement.{vC, uC} := by
  classical
  intro C _ X Y P p q
  rw [productFactorizationStatement C X Y P p q]
  constructor
  · intro hU
    exact ⟨BinaryFan.IsLimit.mk (BinaryFan.mk p q)
      (fun {Z} f g => (hU Z f g).choose)
      (fun {Z} f g => (hU Z f g).choose_spec.1.1)
      (fun {Z} f g => (hU Z f g).choose_spec.1.2)
      (fun {Z} f g m hm₁ hm₂ => (hU Z f g).choose_spec.2 m ⟨hm₁, hm₂⟩)⟩
  · rintro ⟨ht⟩ Z f g
    let l := BinaryFan.IsLimit.lift' ht f g
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact BinaryFan.IsLimit.hom_ext ht
      (hm.1.trans l.2.1.symm) (hm.2.trans l.2.2.symm)

/-- The diagonal's right universal property is simultaneous unique factorization. -/
theorem coproductFactorizationStatement : CoproductFactorizationStatement.{vC, uC} := by
  intro C _ X Y Q i j
  rw [← UniversalArrow.rightCharacterization_proof C (C × C)
    (Functor.diag C) (X, Y) Q (CategoryTheory.Prod.mkHom i j)]
  constructor
  · intro h Z f g
    obtain ⟨l, hl, hu⟩ := h Z (CategoryTheory.Prod.mkHom f g)
    refine ⟨l, ⟨congrArg (fun k => k.1) hl, congrArg (fun k => k.2) hl⟩, ?_⟩
    intro m hm
    exact hu m (CategoryTheory.Prod.hom_ext hm.1 hm.2)
  · intro h Z fg
    obtain ⟨l, hl, hu⟩ := h Z fg.1 fg.2
    refine ⟨l, CategoryTheory.Prod.hom_ext hl.1 hl.2, ?_⟩
    intro m hm
    exact hu m ⟨congrArg (fun k => k.1) hm, congrArg (fun k => k.2) hm⟩

/-- The supplied right diagonal arrow is universal exactly when its cofan is colimiting. -/
theorem coproductColimitStatement : CoproductColimitStatement.{vC, uC} := by
  classical
  intro C _ X Y Q i j
  rw [coproductFactorizationStatement C X Y Q i j]
  constructor
  · intro hU
    exact ⟨BinaryCofan.IsColimit.mk (BinaryCofan.mk i j)
      (fun {Z} f g => (hU Z f g).choose)
      (fun {Z} f g => (hU Z f g).choose_spec.1.1)
      (fun {Z} f g => (hU Z f g).choose_spec.1.2)
      (fun {Z} f g m hm₁ hm₂ => (hU Z f g).choose_spec.2 m ⟨hm₁, hm₂⟩)⟩
  · rintro ⟨ht⟩ Z f g
    let l := BinaryCofan.IsColimit.desc' ht f g
    refine ⟨l.1, l.2, ?_⟩
    intro m hm
    exact BinaryCofan.IsColimit.hom_ext ht
      (hm.1.trans l.2.1.symm) (hm.2.trans l.2.2.symm)

/-- Renard's binary product and coproduct comparisons for the actual diagonal. -/
theorem binaryDiagonalStatements : BinaryDiagonalStatements.{vC, uC} :=
  ⟨productFactorizationStatement, productLimitStatement,
    coproductFactorizationStatement, coproductColimitStatement⟩

end Langlands.Renard.BinaryDiagonal
