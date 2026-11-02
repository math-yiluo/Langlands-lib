import Langlands.CategoryTheory.RenardThreeByThreeStatement
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Proof of Renard's three-by-three bottom-row construction

Proof of `Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement`
(Renard 2026, A.VI.2(8), printed page 262 / PDF page 268). The two missing
bottom arrows are induced by the cokernel universal properties of the first
two columns. Short exactness of the bottom row comes from Mathlib's snake
lemma applied to the morphism of rows `τ : S₁ ⟶ S₂`.
-/

universe u v

open CategoryTheory Limits

namespace Langlands.CategoryTheory

/-- Renard A.VI.2(8): in an abelian category, two short exact rows joined by
three short exact columns admit a compatible short exact row on the three
given bottom objects. -/
theorem renardThreeByThreeBottomRowStatement_proof
    (C : Type u) [Category.{v} C] [Abelian C] :
    RenardThreeByThreeBottomRowStatement C := by
  intro S₁ S₂ τ Z₁ Z₂ Z₃ p₁ p₂ p₃ w₁ w₂ w₃ hS₁ hS₂ hc₁ hc₂ hc₃
  -- The missing arrows, from the cokernel properties of the first two columns.
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc₁.gIsCokernel (S₂.f ≫ p₂) (by
    dsimp
    rw [← Category.assoc, τ.comm₁₂, Category.assoc, w₂, comp_zero])
  obtain ⟨b, hb⟩ := CokernelCofork.IsColimit.desc' hc₂.gIsCokernel (S₂.g ≫ p₃) (by
    dsimp
    rw [← Category.assoc, τ.comm₂₃, Category.assoc, w₃, comp_zero])
  change Z₁ ⟶ Z₂ at a
  change Z₂ ⟶ Z₃ at b
  replace ha : p₁ ≫ a = S₂.f ≫ p₂ := ha
  replace hb : p₂ ≫ b = S₂.g ≫ p₃ := hb
  have : Epi p₁ := hc₁.epi_g
  have w : a ≫ b = 0 := by
    rw [← cancel_epi p₁, reassoc_of% ha, hb, S₂.zero_assoc, zero_comp, comp_zero]
  -- The vertical maps `pᵢ` form a morphism from `S₂` to the bottom row.
  let v₂₃ : S₂ ⟶ ShortComplex.mk a b w :=
    { τ₁ := p₁
      τ₂ := p₂
      τ₃ := p₃
      comm₁₂ := ha
      comm₂₃ := hb }
  have w₁₃ : τ ≫ v₂₃ = 0 := by
    ext
    · exact w₁
    · exact w₂
    · exact w₃
  -- Mathlib's snake input: the kernel of `τ`, the two given rows and the bottom row.
  let SI : ShortComplex.SnakeInput C :=
    { L₀ := kernel τ
      L₁ := S₁
      L₂ := S₂
      L₃ := ShortComplex.mk a b w
      v₀₁ := kernel.ι τ
      v₁₂ := τ
      v₂₃ := v₂₃
      w₀₂ := kernel.condition τ
      w₁₃ := w₁₃
      h₀ := kernelIsKernel τ
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm hc₁.gIsCokernel
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm hc₂.gIsCokernel
        · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm hc₃.gIsCokernel
      L₁_exact := hS₁.exact
      epi_L₁_g := hS₁.epi_g
      L₂_exact := hS₂.exact
      mono_L₂_f := hS₂.mono_f }
  -- The kernel of the third column is zero, so the connecting map vanishes.
  have : Mono τ.τ₃ := hc₃.mono_f
  have hZ : IsZero SI.L₀.X₃ := by
    have := SI.mono_v₀₁_τ₃
    refine IsZero.of_mono_eq_zero SI.v₀₁.τ₃ ?_
    rw [← cancel_mono τ.τ₃, zero_comp]
    exact SI.w₀₂_τ₃
  have : Epi S₂.g := hS₂.epi_g
  refine ⟨a, b, w, ha, hb, ?_⟩
  exact
    { exact := SI.L₃_exact
      mono_f := SI.L₂'_exact.mono_g (hZ.eq_of_src _ _)
      epi_g := SI.epi_L₃_g }

end Langlands.CategoryTheory
