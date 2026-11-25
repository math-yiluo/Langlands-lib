/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionSeparability

/-! Finite coefficient descent of lisse rational sheaves.

## References

* Deligne, Weil II (1.1.1) b)-d), pp. 146-147
* Stacks Project, Algebra, finite separable case
-/

@[expose] public section
set_option autoImplicit false
universe d
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (K : Type (d + 1)) [Field K] [Algebra ℚ_[l] K] [IsAlgClosure ℚ_[l] K]

private theorem lisseRational_retract_of_integral_multiple
    (E : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F G : LisseRationalSheaf l E Y) (a : Padic.coefficientExtensionIntegers l E)
    (ha : a ≠ 0) (i : F.integral ⟶ G.integral) (r : G.integral ⟶ F.integral)
    (h : i ≫ r = a • 𝟙 F.integral) : Nonempty (Retract F G) := by
  refine ⟨{ i := TensorProduct.tmul _ (a : E)⁻¹ i
            r := TensorProduct.tmul _ 1 r
            retract := ?_ }⟩
  change (lisseRationalComposition l E Y).comp F G F
    (TensorProduct.tmul _ (a : E)⁻¹ i) (TensorProduct.tmul _ 1 r) =
      TensorProduct.tmul _ 1 (𝟙 F.integral)
  rw [(lisseRationalComposition l E Y).comp_tmul, mul_one, h,
    ← TensorProduct.smul_tmul]
  change TensorProduct.tmul _ ((a : E) * (a : E)⁻¹) (𝟙 F.integral) = _
  rw [mul_inv_cancel₀ (show (a : E) ≠ 0 from fun h0 ↦ ha (Subtype.ext h0))]

set_option linter.unusedSectionVars false in
/-- Every finite-coefficient rational sheaf is a retract of an extension from the
least coefficient field.
-/
theorem lisseCoefficientRestriction_retracts
    (E₀ : Padic.FiniteCoefficientFields l K) :
    let P := (lisseCoefficientDiagramData l Y K).diagram
    let T := (P.map (homOfLE
      (show Padic.finiteCoefficientBase l K ≤ E₀ from
        show (⊥ : IntermediateField ℚ_[l] K) ≤ E₀.val from bot_le)).toLoc).toFunctor
    ∀ X : P.obj ⟨E₀⟩,
      ∃ A : P.obj ⟨Padic.finiteCoefficientBase l K⟩, Nonempty (Retract X (T.obj A)) := by
  unfold lisseCoefficientDiagramData
  change ∀ X : LisseRationalSheaf l E₀.val Y,
    ∃ A : LisseRationalSheaf l (Padic.finiteCoefficientBase l K).val Y,
      Nonempty (Retract X
        ((lisseRationalScalarExtension l (Padic.finiteCoefficientBase l K).val Y
          E₀.val (IntermediateField.inclusion bot_le)).obj A))
  intro X
  let ι := IntermediateField.inclusion
    (show (Padic.finiteCoefficientBase l K).val ≤ E₀.val from bot_le)
  have hX := lisseIntegralRestrictionRaw_isLisse l Y
    (Padic.finiteCoefficientBase l K).val E₀.val ι X.integral
  refine ⟨⟨⟨lisseIntegralRestrictionRaw l Y
    (Padic.finiteCoefficientBase l K).val E₀.val ι X.integral, hX⟩⟩, ?_⟩
  obtain ⟨a, ha, i, r, hir⟩ := lisseIntegralRestriction_bounded_retract l Y
    (Padic.finiteCoefficientBase l K).val E₀.val ι X.integral hX
  exact lisseRational_retract_of_integral_multiple l Y E₀.val X
    ((lisseRationalScalarExtension l (Padic.finiteCoefficientBase l K).val Y
      E₀.val ι).obj ⟨⟨lisseIntegralRestrictionRaw l Y
        (Padic.finiteCoefficientBase l K).val E₀.val ι X.integral, hX⟩⟩)
    a ha i r hir

end AlgebraicGeometry.Scheme
