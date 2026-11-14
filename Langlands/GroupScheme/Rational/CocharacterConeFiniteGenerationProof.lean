import Langlands.GroupScheme.Rational.CocharacterConeFiniteGenerationStatement
import Mathlib.Order.WellQuasiOrder

/-! # Finite generation via subtractive natural evaluation vectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

theorem cocharacterConeFiniteGeneration :
    CocharacterConeFiniteGenerationStatement.{u} := by
  intro k _ T R hR
  classical
  let : Fintype R := hR.fintype
  let e : cocharacterLattice T →ₗ[ℤ] (R → ℤ) :=
    LinearMap.pi fun α => latticePairing T α.1
  have hker : RealTorusSpace.rootAnnihilatorInt T R = e.ker := by
    ext ν
    simp only [RealTorusSpace.mem_rootAnnihilatorInt, LinearMap.mem_ker,
      funext_iff, e, LinearMap.pi_apply, Pi.zero_apply]
    constructor
    · intro h α
      exact h α.1 α.2
    · intro h α hα
      exact h ⟨α, hα⟩
  let qeval := (RealTorusSpace.rootAnnihilatorInt T R).liftQ e hker.le
  have hqinj : Function.Injective qeval :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ e hker)
  let c : (R → ℕ) →+ (R → ℤ) :=
    { toFun := fun x α => (x α : ℤ)
      map_zero' := rfl
      map_add' := by intro x y; ext α; exact Nat.cast_add _ _ }
  let P : AddSubmonoid (R → ℕ) := e.range.toAddSubmonoid.comap c
  have hPfg : P.FG := AddSubmonoid.fg_of_subtractive (by
    intro x hx y hxy
    change c y ∈ e.range
    have hx' : c x ∈ e.range := hx
    have hxy' : c (x + y) ∈ e.range := hxy
    simpa only [map_add, add_sub_cancel_left] using e.range.sub_mem hxy' hx')
  have himage :
      (CocharacterCone.quotient T R).map qeval.toAddMonoidHom = P.map c := by
    ext z
    constructor
    · rintro ⟨q, ⟨ν, hν, rfl⟩, rfl⟩
      let x : R → ℕ := fun α => (latticePairing T α.1 ν).toNat
      have hx : c x = e ν := by
        ext α
        exact Int.toNat_of_nonneg (hν α.1 α.2)
      refine ⟨x, ?_, hx⟩
      change c x ∈ e.range
      exact hx ▸ e.mem_range_self ν
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨ν, hν⟩ := hx
      have hn : ν ∈ CocharacterCone.nonnegative T R := by
        intro α hα
        have he : latticePairing T α ν = (x ⟨α, hα⟩ : ℤ) :=
          congrFun hν ⟨α, hα⟩
        rw [he]
        exact Int.natCast_nonneg _
      exact ⟨(RealTorusSpace.rootAnnihilatorInt T R).mkQ ν,
        ⟨ν, hn, rfl⟩, hν⟩
  apply AddSubmonoid.FG.map_injective qeval.toAddMonoidHom hqinj
  rw [himage]
  exact hPfg.map c

end Langlands.GroupScheme
