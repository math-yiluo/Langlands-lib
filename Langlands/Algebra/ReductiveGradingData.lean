import Langlands.Algebra.ReductiveCartanData
import Langlands.Algebra.ParabolicCenterProjectionWeights

/-! # Cartan and grading data for a reductive Lie algebra with an integral grading element -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.ParabolicCenterProjection

open LieAlgebra

/-- Data attached to a complex Lie algebra `g` and an element `H`: an abelian subspace
`cartan ∋ H` with a basis of `g` of common eigenvectors of `ad cartan` (linear weights `wt`), whose
weight-zero vectors lie in `cartan`; a nondegenerate symmetric invariant form, nondegenerate on the
centre; and an element `reg ∈ cartan` at which the real parts of the weights vanish exactly for the
zero weights and are positive on the basis vectors of positive integral `H`-eigenvalue. -/
structure GradingData (g : Type v) [LieRing g] [LieAlgebra ℂ g] (H : g) where
  /-- The abelian subspace. -/
  cartan : Submodule ℂ g
  /-- The index type of the weight basis. -/
  ι : Type v
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- The basis of common eigenvectors. -/
  basis : Module.Basis ι ℂ g
  /-- The weights. -/
  wt : ι → cartan →ₗ[ℂ] ℂ
  /-- The invariant form. -/
  form : LinearMap.BilinForm ℂ g
  H_mem : H ∈ cartan
  lie_eq_zero : ∀ x ∈ cartan, ∀ y ∈ cartan, ⁅x, y⁆ = 0
  lie_basis : ∀ i (h : cartan), ⁅(h : g), basis i⁆ = wt i h • basis i
  mem_of_wt_eq_zero : ∀ i, wt i = 0 → basis i ∈ cartan
  nondegenerate : form.Nondegenerate
  isSymm : form.IsSymm
  invariant : ∀ x y z, form ⁅x, y⁆ z = form x ⁅y, z⁆
  center_nondegenerate : ∀ c ∈ center ℂ g, (∀ c' ∈ center ℂ g, form c c' = 0) → c = 0
  /-- The regular element. -/
  reg : cartan
  re_wt_reg_eq_zero_iff : ∀ i, (wt i reg).re = 0 ↔ wt i = 0
  re_wt_reg_pos : ∀ i (n : ℕ), wt i ⟨H, H_mem⟩ = ((n + 1 : ℕ) : ℂ) → 0 < (wt i reg).re

attribute [instance] GradingData.fintype GradingData.decEq

variable {g : Type v} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]

/-- A reductive complex Lie algebra with an integral grading element has grading data. -/
theorem nonempty_gradingData (hred : radical ℂ g = center ℂ g) (H : g)
    (hspan : Submodule.span ℂ {Y : g | ∃ k : ℤ, ⁅H, Y⁆ = (k : ℂ) • Y} = ⊤) :
    Nonempty (GradingData g H) := by
  obtain ⟨𝔥, I, _, b, wt, B, hH, hab, heig, hzero, hnd, hsymm, hinv, hcen⟩ :=
    ReductiveCartanData.exists_cartanData hred H hspan
  classical
  obtain ⟨H'', hreg, hpos⟩ := exists_regular heig H hH hspan
  exact ⟨⟨𝔥, I, b, wt, B, hH, hab, heig, hzero, hnd, hsymm, hinv, hcen, H'', hreg, hpos⟩⟩

end Langlands.Algebra.ParabolicCenterProjection
