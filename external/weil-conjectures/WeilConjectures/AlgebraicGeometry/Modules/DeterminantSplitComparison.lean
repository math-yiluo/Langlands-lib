/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import WeilConjectures.LinearAlgebra.ExteriorTopDirectSum
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal

/-!
# Construction of the determinant comparison on a split open
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Construct the comparison independently of any proposed determinant morphism.
-/
theorem determinant_split_comparison_exists {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g)
    (l : ∀ (W : X.Opens), W ≤ U → S.X₃.val.obj (op W) → S.X₂.val.obj (op W))
    (hl : ∀ W hW b, S.g.val.app (op W) (l W hW b) = b) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∃ (d : ∀ (W : X.Opens), W ≤ V →
        (exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.obj (op W)
          ≃ₗ[X.presheaf.obj (op W)] (exteriorPower S.X₂ r₂).val.obj (op W)),
      (∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
        (b : Fin r₃ → S.X₃.val.obj (op W)),
        d W hW (tmulSection (wedge (M := S.X₁) (r := r₁) (U := W) a)
          (wedge (M := S.X₃) (r := r₃) (U := W) b)) =
        wedge (M := S.X₂) (r := r₂) (U := W)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
            (fun j ↦ l W (hW.trans hVU) (b j)) (Fin.cast hr i))) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
        (exteriorPower S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW)
            ((exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃).val.map
              (homOfLE hZW).op y)) := by
  classical
  obtain ⟨d₀, ⟨hd₀, hn⟩, _⟩ :=
    determinant_split_linear_maps_exists S r₁ r₂ r₃ hr U e hf hg l hl
  intro x hx
  obtain ⟨V, hVU, hxV, hbij⟩ :=
    determinant_split_linear_maps_locally_bijective S r₁ r₂ r₃ hr U e hf hg l hl d₀ hd₀ x hx
  let d := fun W hW ↦ LinearEquiv.ofBijective (d₀ W (hW.trans hVU)) (hbij W hW)
  refine ⟨V, hVU, hxV, d, ?_, ?_⟩
  · intro W hW a b
    exact hd₀ W (hW.trans hVU) a b
  · apply determinant_split_comparison_restriction S r₁ r₂ r₃ V d
      (fun W hW ↦ d₀ W (hW.trans hVU))
    · intro W Z hW hZW y
      exact hn W Z (hW.trans hVU) hZW y
    · intro W hW y
      rfl

end AlgebraicGeometry.Scheme.Modules
