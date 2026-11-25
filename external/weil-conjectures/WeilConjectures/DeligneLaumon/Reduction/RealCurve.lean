/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.RealPurity

/-!
# Real lisse Weil sheaves on curves are mixed

On a smooth geometrically connected curve `C₀` over `k₀`, a real lisse Weil sheaf has a finite
filtration by lisse Weil subsheaves with irreducible lisse quotients
(`AlgebraicGeometry.WeilSheaf.IsLisse.exists_filtration_isIrreducibleLisse`); each quotient is an
irreducible constituent, hence punctually pure
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel`), so the sheaf is
mixed. This is the curve case of `theorem-real-constructible-sheaves-are-mixed--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The members of a finite chain of monomorphisms `H 0 ⟶ H 1 ⟶ ⋯ ⟶ H n ≅ G` map into `G` by
monomorphisms. -/
theorem exists_mono_of_chain {n : ℕ} {H : Fin (n + 1) → WeilSheaf k₀ l X}
    (φ : ∀ i : Fin n, H i.castSucc ⟶ H i.succ) (hφ : ∀ i, Mono (φ i)) {G : WeilSheaf k₀ l X}
    (e : H (Fin.last n) ≅ G) : ∀ i : Fin (n + 1), ∃ ψ : H i ⟶ G, Mono ψ := by
  intro i
  induction i using Fin.reverseInduction with
  | last => exact ⟨e.hom, inferInstance⟩
  | cast i ih =>
    obtain ⟨ψ, hψ⟩ := ih
    exact ⟨φ i ≫ ψ, mono_comp _ _⟩

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Real lisse sheaves on curves are mixed.** Let `C₀` be a smooth geometrically connected curve
over `k₀` and `𝒢` an `ι`-real lisse Weil sheaf on `C₀`. Then `𝒢` is `ι`-mixed: the successive
quotients of a filtration with irreducible lisse quotients are irreducible constituents of `𝒢`,
punctually pure by `theorem-purity-real-sheaves-curves--1` (blueprint:
`theorem-real-constructible-sheaves-are-mixed--1`, the curve case). -/
theorem IsReal.isMixed_of_isLisse [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] {ι : PadicAlgCl l →+* ℂ}
    {𝒢 : WeilSheaf k₀ l X} (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) : 𝒢.IsMixed ι := by
  obtain ⟨n, H, φ, h0, ⟨e⟩, hmono, hlisse, hirr⟩ := h𝒢.exists_filtration_isIrreducibleLisse
  have hpure (i : Fin n) : ∃ w : ℝ, (cokernel (φ i)).IsPunctuallyPureOfWeight ι w := by
    obtain ⟨ψ, hψ⟩ := exists_mono_of_chain φ hmono e i.succ
    have := hmono i
    exact hreal.exists_isPunctuallyPureOfWeight_cokernel h𝒢 (φ i) ψ (hlisse _) (hlisse _) (hirr i)
  choose w hw using hpure
  refine ⟨∑ i, |w i|, n, H, φ, h0, ⟨e⟩, hmono, fun i ↦ ⟨w i, ?_, hw i⟩⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (w j)) (Finset.mem_univ i))

end AlgebraicGeometry.WeilSheaf
