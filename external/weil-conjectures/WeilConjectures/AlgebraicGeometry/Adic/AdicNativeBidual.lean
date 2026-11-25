/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-! # The native adic bidual evaluation map -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.ProEtale

/-- Native bidual evaluation is the transpose of the identity of the dual.
Source: Stacks 03EO, the tensor-Hom adjunction
(blueprint: lem-sf-adic-native-bidual). -/
noncomputable def adicNativeBidual {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) :
    M ⟶ (AdicSheaf.ihom ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X))).obj
      (AdicSheaf.unit l X) :=
  Mod.transpose (𝟙 ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)))

/-- The native bidual map is the transpose of braided evaluation.
Source: Stacks 03EO (blueprint: lem-sf-adic-native-bidual).
Proof: uncurry the transpose of the identity. The transpose-uncurry identity gives
braided evaluation, and the identity morphism disappears from its first factor. -/
theorem adicNativeBidual_transpose {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) :
    (adicNativeBidual M).hom ▷ ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X ≫
        Mod.evaluation ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) (AdicSheaf.unit l X) =
      (β_ M.X ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X).hom ≫
        Mod.evaluation M (AdicSheaf.unit l X) := by
  simpa only [adicNativeBidual, Mod.uncurryHom, Mod.id_hom', id_whiskerRight,
    Category.id_comp] using
    Mod.uncurryHom_transpose (𝟙 ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)))

end AlgebraicGeometry.ProEtale
