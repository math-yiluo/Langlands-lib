/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionIntegralModel
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionSeparableTensor
import WeilConjectures.AlgebraicGeometry.Lisse.Coefficient.LisseCoefficientRestrictionTensorMaps

/-! Separability section for finite coefficient extension.

## References

* Deligne, Weil II (1.1.1) c)-d), pp. 146-147
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe d
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{d})
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  (E L : Type (d + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- An integral multiple of the separability section gives compatible integral maps. -/
theorem lisseIntegralRestriction_bounded_retract
    (F : LisseIntegralSheaf l L Y)
    (hF : IsLisseIntegralDiagram l E Y
      (lisseIntegralRestrictionRaw l Y E L ι F)) :
    let G : LisseIntegralSheaf l E Y :=
      ⟨lisseIntegralRestrictionRaw l Y E L ι F, hF⟩
    let H := (lisseIntegralScalarExtension l E Y L ι).obj G
    ∃ a : Padic.coefficientExtensionIntegers l L, a ≠ 0 ∧
      ∃ (i : F ⟶ H) (r : H ⟶ F), i ≫ r = a • 𝟙 F := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let : Algebra R S := (lisseIntegerInclusion l E L ι).toAlgebra
  obtain ⟨t, ht, hc⟩ := lisseIntegerInclusion_separability_tensor l E L ι
  obtain ⟨i, r, hir⟩ := lisseIntegralRestriction_tensor_maps l Y E L ι F hF t hc
  exact ⟨Algebra.TensorProduct.lmul' R t, ht, i, r, hir⟩

end AlgebraicGeometry.Scheme
