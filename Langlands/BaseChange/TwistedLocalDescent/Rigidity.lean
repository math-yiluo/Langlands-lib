import Langlands.BaseChange.TwistedLocalDescent.Windows
import Langlands.BaseChange.TwistedLocalDescent.BlockIntertwiner

/-! # Twisted conjugators between parabolic elements over a window

Let `σ^l = 1`. If two parabolic elements have Levi parts in the twisted conjugacy saturation of a
window `Ω` such that, for all `x, x' ∈ Ω` and distinct blocks `i ≠ i'`, the norms of the blocks
`x_i` and `x'_{i'}` have coprime characteristic polynomials, then every twisted conjugator
between them lies in the parabolic. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear

universe u v

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] (σ : E ≃ₐ[F] E) (l : ℕ) {n : ℕ} (B : BlockShape n)

theorem normCharpoly_of_mem_saturation (hσ : σ ^ l = 1) {Ω : Set (B.Levi E)} {x : B.Levi E}
    (hx : x ∈ twistedConjugacySaturation (leviAut σ B).toMonoidHom Ω) :
    ∃ x₀ ∈ Ω, ∀ i, normCharpoly σ l B x i = normCharpoly σ l B x₀ i := by
  obtain ⟨y, x₀, hx₀, rfl⟩ := Set.mem_iUnion.mp hx
  refine ⟨x₀, hx₀, fun i => ?_⟩
  exact normCharpoly_twistedConj σ l B hσ y x₀ i

omit [TopologicalSpace E] [IsTopologicalRing E] in
theorem block_cyclicNorm_parabolic (p : B.parabolic E) (i : Fin B.length) :
    block B (parabolicCyclicNorm σ B l p : GeneralLinear n E).val i i =
      (cyclicNorm σ l (B.leviProjection E p i)).val := by
  rw [← leviProjection_parabolicCyclicNorm]
  ext a b
  rfl

/-- **Rigidity.** For `σ^l = 1`, a twisted conjugator between two parabolic elements whose Levi
parts lie in the saturation of `Ω` is parabolic, when the norm characteristic polynomials of
distinct blocks at any two points of `Ω` are coprime. -/
theorem mem_parabolic_of_twistedConj (hσ : σ ^ l = 1) (Ω : Set (B.Levi E))
    (hcop : ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ i i', i ≠ i' →
      IsCoprime (normCharpoly σ l B x' i') (normCharpoly σ l B x i))
    {p p' : B.parabolic E}
    (hp : B.leviProjection E p ∈ twistedConjugacySaturation (leviAut σ B).toMonoidHom Ω)
    (hp' : B.leviProjection E p' ∈ twistedConjugacySaturation (leviAut σ B).toMonoidHom Ω)
    (h : GeneralLinear n E)
    (hh : h * (p : GeneralLinear n E) * (entrywiseAut σ n h)⁻¹ = p') : h ∈ B.parabolic E := by
  rw [← isBlockUpper_iff_mem_parabolic]
  have hN : h * (parabolicCyclicNorm σ B l p : GeneralLinear n E) =
      (parabolicCyclicNorm σ B l p' : GeneralLinear n E) * h := by
    change h * cyclicNorm σ l (p : GeneralLinear n E) = cyclicNorm σ l (p' : GeneralLinear n E) * h
    rw [← hh]
    have := cyclicNorm_twistedConj σ l h⁻¹ (p : GeneralLinear n E)
    rw [inv_inv, map_inv, hσ, entrywiseAut_one_apply] at this
    rw [this]
    group
  have hNval := congrArg Units.val hN
  simp only [Units.val_mul] at hNval
  apply isBlockUpper_of_mul_eq B ((isBlockUpper_iff_mem_parabolic B _).mpr
    (parabolicCyclicNorm σ B l p).property)
    ((isBlockUpper_iff_mem_parabolic B _).mpr (parabolicCyclicNorm σ B l p').property) hNval
  intro i k hik
  rw [block_cyclicNorm_parabolic, block_cyclicNorm_parabolic]
  obtain ⟨x₀, hx₀, hx⟩ := normCharpoly_of_mem_saturation σ l B hσ hp
  obtain ⟨x₀', hx₀', hx'⟩ := normCharpoly_of_mem_saturation σ l B hσ hp'
  have := hcop x₀ hx₀ x₀' hx₀' i k hik
  rw [← hx, ← hx'] at this
  exact this

end Langlands.BaseChange.TwistedLocalDescent
