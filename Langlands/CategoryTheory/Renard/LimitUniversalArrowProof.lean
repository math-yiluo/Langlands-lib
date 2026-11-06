import Langlands.CategoryTheory.Renard.LimitUniversalArrowStatements
import Langlands.CategoryTheory.Renard.UniversalArrowProof

/-!
# Proof of the limit and colimit universal-arrow comparisons

The factorization forms are proved directly from the actual limit and colimit
witnesses. The structured-arrow forms then follow from the published left and
right universal-arrow characterizations of Renard A.III.1.
-/

open CategoryTheory CategoryTheory.Limits

universe vJ vC uJ uC

namespace Langlands.Renard.LimitUniversalArrow

open Langlands.CategoryTheory.Renard

theorem limitFactorization : LimitFactorizationStatement.{vJ, vC, uJ, uC} := by
  intro J _ C _ D X η
  constructor
  · rintro ⟨h⟩ Y f
    refine ⟨h.lift (Cone.mk Y f), ?_, ?_⟩
    · ext j
      exact h.fac (Cone.mk Y f) j
    · intro g hg
      refine h.uniq (Cone.mk Y f) g fun j => ?_
      exact congrArg (fun φ => NatTrans.app φ j) hg
  · intro h
    refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
    obtain ⟨g, hg, hu⟩ := h s.pt s.π
    refine ⟨g, fun j => congrArg (fun φ => NatTrans.app φ j) hg, fun g' hg' => hu g' ?_⟩
    ext j
    exact hg' j

theorem colimitFactorization : ColimitFactorizationStatement.{vJ, vC, uJ, uC} := by
  intro J _ C _ D X η
  constructor
  · rintro ⟨h⟩ Y f
    refine ⟨h.desc (Cocone.mk Y f), ?_, ?_⟩
    · ext j
      exact h.fac (Cocone.mk Y f) j
    · intro g hg
      refine h.uniq (Cocone.mk Y f) g fun j => ?_
      exact congrArg (fun φ => NatTrans.app φ j) hg
  · intro h
    refine ⟨IsColimit.ofExistsUnique fun s => ?_⟩
    obtain ⟨g, hg, hu⟩ := h s.pt s.ι
    refine ⟨g, fun j => congrArg (fun φ => NatTrans.app φ j) hg, fun g' hg' => hu g' ?_⟩
    ext j
    exact hg' j

theorem limitUniversal : LimitUniversalStatement.{vJ, vC, uJ, uC} := by
  intro J _ C _ D X η
  exact (limitFactorization J C D X η).trans
    (UniversalArrow.leftCharacterization_proof C (J ⥤ C) (diagonal J C) D X η)

theorem colimitUniversal : ColimitUniversalStatement.{vJ, vC, uJ, uC} := by
  intro J _ C _ D X η
  exact (colimitFactorization J C D X η).trans
    (UniversalArrow.rightCharacterization_proof C (J ⥤ C) (diagonal J C) D X η)

/-- The four limit and colimit universal-arrow comparisons. -/
theorem limitUniversalArrowStatements :
    LimitUniversalArrowStatements.{vJ, vC, uJ, uC} :=
  ⟨limitUniversal, limitFactorization, colimitUniversal, colimitFactorization⟩

end Langlands.Renard.LimitUniversalArrow
