/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTriangulation
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarAmbientShift
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Exactness and shift descent for rational scalar extension

Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.

## References

* Milne, Section 19
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section ScalarShift
variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) (T : Scheme.{u})
variable [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The integral restriction retains the actual ambient functor through its inclusion. -/
@[irreducible] def pbcIntegralScalarInclusionIso :
    pbcEmbeddingIntegralTensor l E F i T dim.out inv.out ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l F)) ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcEmbeddingAmbientTensor l E F i T := Iso.refl _

/-- The actual tensor Hom formula agrees with tensoring integral arrows by one. -/
theorem pbcScalarLocalization_naturality
    {K L : PbcIntegralCategory l E T dim.out inv.out} (f : K ⟶ L) :
    (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).map f) ≫ 𝟙 _ =
      𝟙 _ ≫ (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f) := by
  have h := (pbcRationalScalarHom_exists l E F i T dim.out inv.out K L).exists.choose_spec
    (1 : Localization.Away (pbcUniformizer l E)) f
  simp only [Category.comp_id, Category.id_comp]
  change _ = pbcRationalScalarHom l E F i T dim.out inv.out K L _
  dsimp only [pbcRationalScalarHom]
  simpa only [one_smul, map_one] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
attribute [local irreducible] pbcRationalScalarHom

end ScalarShift
end AlgebraicGeometry.Scheme
