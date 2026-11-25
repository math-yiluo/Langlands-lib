/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Local split determinant comparisons
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Converting a natural family of linear maps to equal linear equivalences preserves naturality. -/
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ)
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W))
    (dNatural : ∀ (W : X.Opens), W ≤ V →
      (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W))
    (hn : ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (dNatural W hW y) =
        dNatural Z (hZW.trans hW)
          ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
            (homOfLE hZW).op y))
    (hd : ∀ W hW y, d W hW y = dNatural W hW y) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
            (homOfLE hZW).op y) := by
  intro W Z hW hZW y
  simpa only [hd] using hn W Z hW hZW y

end AlgebraicGeometry.Scheme.Modules

