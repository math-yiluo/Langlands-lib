import Langlands.Global.AdelicHeightPowerPolynomialBound
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Polynomial bounds for Iwasawa height increments on bounded parameter sets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) {N : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hN : 0 < N) (hrho : IsClosedSubgroup rho)

include hN hrho in
/-- The polynomial bound for right translation of Iwasawa height powers can use
one exponent and one constant over a bounded set of complex coordinates. -/
theorem IsIwasawaCompact.exists_uniform_heightPower_mul_le {n : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) {W : Set (Fin n → ℂ)}
    (hW : Bornology.IsBounded W) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ s ∈ W, ∀ x g : AdelicGroupPoints F G,
      ‖hK.heightPower (e s) (x * g)‖ ≤ C * adelicHeight F G rho g ^ D *
        ‖hK.heightPower (e s) x‖ := by
  classical
  let V := Fin n → ℂ
  let I := Fin (Module.finrank ℝ V)
  let b : Module.Basis I ℝ V := Module.finBasis ℝ V
  let coord : V →ₗ[ℝ] (I → ℝ) := b.equivFun.toLinearMap
  obtain ⟨M, hM⟩ := (hW.isCompact_closure.image
    coord.continuous_of_finiteDimensional.norm).bddAbove
  let B : ℝ := max 0 M
  have hcoord (s : V) (hs : s ∈ W) (i : I) : |b.repr s i| ≤ B := by
    change ‖coord s i‖ ≤ B
    exact (norm_le_pi_norm (coord s) i).trans
      ((hM ⟨s, subset_closure hs, rfl⟩).trans (le_max_right _ _))
  let vertex (v : I → Bool) : V := ∑ i, (if v i then B else -B) • b i
  choose c d hc hd hbound using fun v : I → Bool =>
    hK.iwasawaHeightPowerPolynomialBound rho hN hrho (e (vertex v))
  let C := 1 + ∑ v, c v
  let D := ∑ v, d v
  have hcC (v : I → Bool) : c v ≤ C :=
    (Finset.single_le_sum (fun t _ => (hc t).le) (Finset.mem_univ v)).trans (by
      dsimp [C]
      linarith)
  refine ⟨C, D, add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun v _ => (hc v).le),
    Finset.sum_nonneg (fun v _ => hd v), ?_⟩
  intro s hs x g
  let L : V →ₗ[ℝ] ℝ := Complex.reCLM.toLinearMap.comp
    ((((complexParameterPairing F P).flip (hK.height (x * g))).comp e -
      ((complexParameterPairing F P).flip (hK.height x)).comp e).restrictScalars ℝ)
  let v (i : I) : Bool := decide (0 ≤ L (b i))
  have hv : L s ≤ L (vertex v) := by
    conv_lhs => rw [← b.sum_repr s]
    simp only [vertex, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : 0 ≤ L (b i)
    · simpa [v, h] using mul_le_mul_of_nonneg_right ((abs_le.mp (hcoord s hs i)).2) h
    · simpa [v, h] using mul_le_mul_of_nonpos_right ((abs_le.mp (hcoord s hs i)).1)
        (le_of_not_ge h)
  have hpower (z : V) : ‖hK.heightPower (e z) (x * g)‖ =
      Real.exp (L z) * ‖hK.heightPower (e z) x‖ := by
    let y := complexParameterPairing F P (e z) (hK.height (x * g))
    let w := complexParameterPairing F P (e z) (hK.height x)
    simp only [IsIwasawaCompact.heightPower, Complex.norm_exp, ← Real.exp_add]
    change Real.exp y.re = Real.exp ((y - w).re + w.re)
    rw [Complex.sub_re, sub_add_cancel]
  have hpos (z : V) : 0 < ‖hK.heightPower (e z) x‖ := by
    rw [IsIwasawaCompact.heightPower, Complex.norm_exp]
    exact Real.exp_pos _
  have hF : Real.exp (L (vertex v)) ≤ c v * adelicHeight F G rho g ^ d v := by
    apply le_of_mul_le_mul_right _ (hpos (vertex v))
    rw [← hpower]
    exact hbound v x g
  have hdD : d v ≤ D := Finset.single_le_sum (fun t _ => hd t) (Finset.mem_univ v)
  rw [hpower]
  refine mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hv).trans (hF.trans ?_))
    (norm_nonneg _)
  exact mul_le_mul (hcC v)
    (Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hN g) hdD)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_adelicHeight F G rho hN g)) _)
    ((hc v).le.trans (hcC v))

end Langlands.Global.AdelicGroupPoints
