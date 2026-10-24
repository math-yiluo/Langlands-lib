import Langlands.Representation.RankinSelberg.RootSchwartzStatement

namespace Langlands.RankinSelberg

open HarmonicAnalysis Set

universe uF

/-- Assemble the three test factors into a Schwartz function on the full
field coordinate space. -/
theorem rootSchwartzAssembly (F : Type uF) [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [T2Space F] (n : ℕ) :
    RootSchwartzAssemblyStatement F n := by
  classical
  intro φ φ' Φ k
  obtain ⟨j, hj⟩ : ∃ j, lastRow k j ≠ 0 := by
    by_contra! h
    exact Matrix.GeneralLinearGroup.det_ne_zero k
      (Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) h)
  let f : (Fin (n + 1) → F) → ℂ := fun x =>
    φ (fun i : Fin n => x i.castSucc) *
      φ' (fun i : Fin n => x i.castSucc) * Φ (x (Fin.last n) • lastRow k)
  have hprefix : Continuous (fun x : Fin (n + 1) → F =>
      fun i : Fin n => x i.castSucc) :=
    continuous_pi fun i => continuous_apply i.castSucc
  have hrow : Continuous (fun x : Fin (n + 1) → F =>
      x (Fin.last n) • lastRow k) := by
    apply continuous_pi
    intro i
    exact (continuous_apply (Fin.last n)).mul continuous_const
  have hlc : IsLocallyConstant f :=
    ((φ.locallyConstant.comp_continuous hprefix).comp₂
      (φ'.locallyConstant.comp_continuous hprefix) (· * ·)).comp₂
        (Φ.locallyConstant.comp_continuous hrow) (· * ·)
  let assemble : (Fin n → F) × (Fin (n + 1) → F) → (Fin (n + 1) → F) :=
    fun yz => Fin.snoc yz.1 (yz.2 j / lastRow k j)
  have hcont : Continuous assemble := by
    apply Continuous.finSnoc (A := fun _ : Fin (n + 1) => F)
    · exact continuous_fst
    · exact ((continuous_apply j).comp continuous_snd).div_const _
  have hcompact : IsCompact (assemble ''
      (tsupport (φ : (Fin n → F) → ℂ) ×ˢ tsupport (Φ : (Fin (n + 1) → F) → ℂ))) :=
    (φ.hasCompactSupport.prod Φ.hasCompactSupport).image hcont
  have hsupp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact hcompact
    intro x hx
    have hx' : φ (fun i : Fin n => x i.castSucc) ≠ 0 ∧
        Φ (x (Fin.last n) • lastRow k) ≠ 0 := by
      have hf : f x ≠ 0 := hx
      exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hf).1).1,
        (mul_ne_zero_iff.mp hf).2⟩
    refine ⟨((fun i : Fin n => x i.castSucc), x (Fin.last n) • lastRow k),
      ⟨subset_tsupport _ hx'.1, subset_tsupport _ hx'.2⟩, ?_⟩
    change Fin.snoc (fun i : Fin n => x i.castSucc)
      ((x (Fin.last n) * lastRow k j) / lastRow k j) = x
    rw [mul_div_cancel_right₀ _ hj]
    exact Fin.snoc_init_self x
  exact ⟨⟨f, hlc, hsupp⟩, fun _ => rfl⟩

end Langlands.RankinSelberg
