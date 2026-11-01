import Langlands.CategoryTheory.Renard.UniversalArrowStatements

/-!
# Universal-arrow characterizations and compatible comparison

Proofs of the closed statements for Renard A.III.1, using the actual
structured-arrow and costructured-arrow categories.
-/

open CategoryTheory

universe vA vB uA uB

namespace Langlands.Renard.UniversalArrow

/-- The right factorization property constructs, and follows from, initiality. -/
theorem rightCharacterization_proof :
    RightCharacterizationStatement.{vA, vB, uA, uB} := by
  classical
  intro A _ B _ F Y X i
  constructor
  · intro h
    let g := fun Z f => (h Z f).choose
    refine ⟨Limits.IsInitial.ofUniqueHom
      (fun c => StructuredArrow.homMk (g c.right c.hom)
        (h c.right c.hom).choose_spec.1) ?_⟩
    intro c m
    apply StructuredArrow.hom_ext
    exact (h c.right c.hom).choose_spec.2 m.right (StructuredArrow.w m)
  · rintro ⟨h⟩ Z f
    exact StructuredArrow.IsUniversal.existsUnique h (StructuredArrow.mk f)

/-- The left factorization property constructs, and follows from, terminality. -/
theorem leftCharacterization_proof :
    LeftCharacterizationStatement.{vA, vB, uA, uB} := by
  classical
  intro A _ B _ F Y X j
  constructor
  · intro h
    let g := fun Z f => (h Z f).choose
    refine ⟨Limits.IsTerminal.ofUniqueHom
      (fun c => CostructuredArrow.homMk (g c.left c.hom)
        (h c.left c.hom).choose_spec.1) ?_⟩
    intro c m
    apply CostructuredArrow.hom_ext
    exact (h c.left c.hom).choose_spec.2 m.left (CostructuredArrow.w m)
  · rintro ⟨h⟩ Z f
    exact CostructuredArrow.IsUniversal.existsUnique h (CostructuredArrow.mk f)

/-- The two compatible right factor maps are inverse and determine the comparison. -/
theorem rightComparison_proof :
    RightComparisonStatement.{vA, vB, uA, uB} := by
  intro A _ B _ F Y X X' i i' hi hi'
  obtain ⟨f, hf, uf⟩ := hi X' i'
  obtain ⟨g, hg, _⟩ := hi' X i
  have hfg : f ≫ g = 𝟙 X := by
    obtain ⟨k, _, hk⟩ := hi X i
    apply (hk _ ?_).trans (hk _ ?_).symm
    · rw [F.map_comp, ← Category.assoc, hf, hg]
    · simp
  have hgf : g ≫ f = 𝟙 X' := by
    obtain ⟨k, _, hk⟩ := hi' X' i'
    apply (hk _ ?_).trans (hk _ ?_).symm
    · rw [F.map_comp, ← Category.assoc, hg, hf]
    · simp
  let e : X ≅ X' := ⟨f, g, hfg, hgf⟩
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  exact uf e'.hom he'

/-- The two compatible left factor maps are inverse and determine the comparison. -/
theorem leftComparison_proof :
    LeftComparisonStatement.{vA, vB, uA, uB} := by
  intro A _ B _ F Y X X' j j' hj hj'
  obtain ⟨f, hf, uf⟩ := hj' X j
  obtain ⟨g, hg, _⟩ := hj X' j'
  have hfg : f ≫ g = 𝟙 X := by
    obtain ⟨k, _, hk⟩ := hj X j
    apply (hk _ ?_).trans (hk _ ?_).symm
    · rw [F.map_comp, Category.assoc, hg, hf]
    · simp
  have hgf : g ≫ f = 𝟙 X' := by
    obtain ⟨k, _, hk⟩ := hj' X' j'
    apply (hk _ ?_).trans (hk _ ?_).symm
    · rw [F.map_comp, Category.assoc, hf, hg]
    · simp
  let e : X ≅ X' := ⟨f, g, hfg, hgf⟩
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  exact uf e'.hom he'

/-- Renard A.III.1: both characterizations and both compatible comparisons. -/
theorem universalArrowStatements_proof :
    UniversalArrowStatements.{vA, vB, uA, uB} :=
  ⟨rightCharacterization_proof, leftCharacterization_proof,
    rightComparison_proof, leftComparison_proof⟩

end Langlands.Renard.UniversalArrow
