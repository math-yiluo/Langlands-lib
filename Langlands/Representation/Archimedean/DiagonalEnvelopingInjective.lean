import Langlands.Representation.Archimedean.DiagonalEnvelopingProjection
import Langlands.Representation.Archimedean.LowerVermaCentral

/-! # Injectivity of the diagonal projection for complex matrix products -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

open Langlands.Algebra.UniversalEnveloping MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

local notation "L" => GLProd ℂ n
local notation "U" => UniversalEnvelopingAlgebra ℂ (GLProd ℂ n)
local notation "B" => weightOrderedPBWBasis (glBasis ℂ n) (deg n)

private theorem pbw_eq_orderedMonomial (α : Coord n →₀ ℕ) :
    B α = orderedMonomial ℂ L (glBasis ℂ n) (sortedCoords n) α :=
  weightOrderedPBWBasis_apply (glBasis ℂ n) (deg n) α

private theorem central_coordinate_weight_zero (z : Subalgebra.center ℂ U) {α : Coord n →₀ ℕ}
    (hα : (B).repr z.val α ≠ 0) : wdeg n α = 0 := by
  have hcoord : (B).coord α ∘ₗ gradDer n = (wdeg n α : ℂ) • (B).coord α := by
    refine (B).ext fun β => ?_
    rw [LinearMap.comp_apply, pbw_eq_orderedMonomial n β, gradDer_orderedMonomial, map_smul,
      ← pbw_eq_orderedMonomial]
    by_cases he : α = β
    · subst β
      rfl
    · simp [Module.Basis.coord_apply, Module.Basis.repr_self, he]
  have hz : gradDer n z.val = 0 := by
    rw [gradDer_apply, sub_eq_zero]
    exact Subalgebra.mem_center_iff.mp z.property _
  have h := LinearMap.congr_fun hcoord z.val
  rw [LinearMap.comp_apply, hz, map_zero, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul] at h
  exact Int.cast_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hα)

private theorem mem_expand_sortedCoords {α : Coord n →₀ ℕ} {a : Coord n} :
    a ∈ expand (sortedCoords n) α ↔ α a ≠ 0 := by
  rw [← List.count_pos_iff, count_expand (sortedCoords_nodup n) (mem_sortedCoords n), Nat.pos_iff_ne_zero]

private theorem exists_lower_letter (z : Subalgebra.center ℂ U)
    (hz : diagonalCenterPolynomial n z = 0) {α : Coord n →₀ ℕ}
    (hα : (B).repr z.val α ≠ 0) : ∃ a : Coord n, α a ≠ 0 ∧ a.2.2 < a.2.1 := by
  have hzI := sub_diagonalCenterPolynomial_mem n z
  rw [hz, map_zero, sub_zero] at hzI
  have hH (a : Coord n) : ⁅hdiag n, glBasis ℂ n a⁆ = (deg n a : ℂ) • glBasis ℂ n a := by
    rw [glBasis_apply, lie_hdiag_unit]
  let P := positiveWeightLieSubalgebra (glBasis ℂ n) (deg n) (hdiag n) hH
  have hzB := positiveWeightRightIdeal_le_positivePBWSpan (glBasis ℂ n) (deg n) P.incl
    (positiveWeightLieBasis _ _ _ _) (positiveWeightLieSubalgebra_incl_basis _ _ _ _) hzI
  have hpos : ∃ a : Coord n, 0 < deg n a ∧ α a ≠ 0 := by
    by_contra h
    push Not at h
    exact hα (positivePBWSpan_coord_zero (glBasis ℂ n) (deg n) h hzB)
  obtain ⟨a, ha, haα⟩ := hpos
  by_contra h
  push Not at h
  let w := expand (sortedCoords n) α
  have hnn (d : ℤ) (hd : d ∈ w.map (deg n)) : 0 ≤ d := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    have hb' := h b ((mem_expand_sortedCoords n).1 hb)
    change 0 ≤ ((b.2.2 : ℕ) : ℤ) - ((b.2.1 : ℕ) : ℤ)
    exact sub_nonneg.mpr (Int.ofNat_le.mpr hb')
  have ham : deg n a ∈ w.map (deg n) :=
    List.mem_map.mpr ⟨a, (mem_expand_sortedCoords n).2 haα, rfl⟩
  obtain ⟨x, y, he, -⟩ := List.eq_append_cons_of_mem ham
  have hs := central_coordinate_weight_zero n z hα
  change (w.map (deg n)).sum = 0 at hs
  rw [he, List.sum_append, List.sum_cons] at hs
  have hx : 0 ≤ x.sum := List.sum_nonneg fun d hd => hnn d (by
    rw [he]
    exact List.mem_append_left _ hd)
  have hy : 0 ≤ y.sum := List.sum_nonneg fun d hd => hnn d (by
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hd))
  omega

private theorem symbol_center_invariant (z : Subalgebra.center ℂ U) (x : L) {N : ℕ}
    (hz : z.val ∈ degreeFiltration ℂ L N) : coadDer ℂ n x ((glSymbol ℂ n).symbol N z.val) = 0 := by
  have h := (glSymbol ℂ n).symbol_commutator x (coadDer ℂ n x).toLinearMap
    (coadDer_isLeibniz ℂ n x) (coadDer_ξ ℂ n x) hz
  rw [sub_eq_zero.mpr (Subalgebra.mem_center_iff.mp z.property _), map_zero] at h
  exact h.symm

private theorem eq_zero_of_invariant_upper (σ : MvPolynomial (Coord n) ℂ)
    (hinv : ∀ i p q, coadDer ℂ n (unit ℂ n i p q) σ = 0)
    (hup : ∀ Y : L, (∀ i (p q : Fin (n i)), q < p → Y i p q = 0) → eval (tuplePoint n Y) σ = 0) :
    σ = 0 := by
  let W : Submodule ℂ (MvPolynomial (Coord n) ℂ) := ℂ ∙ σ
  have hW : ∀ i (p q : Fin (n i)), p ≠ q → ∀ f ∈ W,
      coadDer ℂ n (unit ℂ n i p q) f ∈ W := by
    intro i p q _ f hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [Derivation.map_smul, hinv, smul_zero]
    exact W.zero_mem
  apply MvPolynomial.funext
  intro y
  let Y : L := fun i => Matrix.of fun p q => y ⟨i, p, q⟩
  choose P Q hPQ htri using (fun i => VermaCentral.exists_triangular (n i) (Y i))
  let T : L := fun i => Q i * Y i * P i
  have hT : T ∈ zeroSet n W := by
    intro f hf
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [smul_eq_C_mul, eval_mul, hup T htri, mul_zero]
  have hP (i : ι) : IsUnit (P i).det := Matrix.isUnit_det_of_right_inverse (hPQ i)
  have h := conj_mem_zeroSet hW P hP hT
  have he : (fun i => P i * T i * (P i)⁻¹) = Y := by
    funext i
    dsimp only [T]
    rw [Matrix.inv_eq_right_inv (hPQ i), mul_assoc (Q i) (Y i) (P i),
      ← mul_assoc (P i) (Q i) (Y i * P i), hPQ, one_mul, mul_assoc, hPQ, mul_one]
  rw [he] at h
  have hσ := h σ (Submodule.mem_span_singleton_self σ)
  change eval y σ = 0 at hσ
  rw [map_zero]
  exact hσ

/-- The projection to diagonal polynomials is injective on the centre of a complex matrix product. -/
theorem diagonalCenterPolynomial_injective : Function.Injective (diagonalCenterPolynomial n) := by
  refine (injective_iff_map_eq_zero (diagonalCenterPolynomial n)).2 fun z hz => ?_
  by_contra hz₀
  have hu : z.val ≠ 0 := fun h => hz₀ (Subtype.ext h)
  let r := (B).repr z.val
  have hne : r.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h =>
    hu ((B).repr.injective (h.trans (map_zero (B).repr).symm))
  let N := r.support.sup Finsupp.degree
  obtain ⟨α, hα, hαN⟩ := Finset.exists_mem_eq_sup _ hne Finsupp.degree
  have hsum : z.val = ∑ β ∈ r.support, r β • B β := by
    conv_lhs => rw [← (B).linearCombination_repr z.val]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hmem : z.val ∈ degreeFiltration ℂ L N := by
    rw [hsum]
    refine Submodule.sum_mem _ fun β hβ => Submodule.smul_mem _ _ ?_
    rw [pbw_eq_orderedMonomial]
    exact degreeFiltration_mono ℂ _ (Finset.le_sup hβ)
      (orderedMonomial_mem_degreeFiltration ℂ L (glBasis ℂ n) (sortedCoords_nodup n)
        (mem_sortedCoords n) β)
  let σ := (glSymbol ℂ n).symbol N z.val
  have hσsum : σ = ∑ β ∈ r.support, r β • (if β.degree = N then monomial β (1 : ℂ) else 0) := by
    change (glSymbol ℂ n).symbol N z.val = _
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_smul, pbw_eq_orderedMonomial]
    rw [symbol_orderedMonomial ℂ L (glBasis ℂ n) (glSymbol ℂ n)
      (AssocSymbol.symbolData_ξ_basis (glBasis ℂ n)) (sortedCoords_nodup n) (mem_sortedCoords n)
      (Finset.le_sup hβ)]
  have hcoeff : σ.coeff α = r α := by
    rw [hσsum, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_smul, ite_eq_left (show α.degree = N from hαN.symm), MvPolynomial.coeff_monomial,
        ite_eq_left rfl, smul_eq_mul, mul_one]
    · intro β _ hβα
      rw [MvPolynomial.coeff_smul]
      split_ifs
      · rw [MvPolynomial.coeff_monomial, ite_eq_right hβα, smul_zero]
      · simp
    · exact fun h => (h hα).elim
  have hzero : σ = 0 := by
    apply eq_zero_of_invariant_upper n σ (fun i p q => symbol_center_invariant n z _ hmem)
    intro Y hY
    rw [hσsum, map_sum]
    refine Finset.sum_eq_zero fun β hβ => ?_
    obtain ⟨a, ha, hlt⟩ := exists_lower_letter n z hz (Finsupp.mem_support_iff.mp hβ)
    rw [smul_eq_C_mul, eval_mul, eval_C]
    split_ifs
    · rw [eval_monomial, Finsupp.prod,
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr ha) (by
          change Y a.1 a.2.1 a.2.2 ^ β a = 0
          rw [hY a.1 _ _ hlt, zero_pow ha]), mul_zero, mul_zero]
    · rw [map_zero, mul_zero]
  exact (Finsupp.mem_support_iff.mp hα) (by simpa [hzero] using hcoeff.symm)

/-- Identify the centre with the subalgebra of its diagonal polynomials. -/
def diagonalCenterPolynomialEquiv :
    Subalgebra.center ℂ U ≃ₐ[ℂ] (diagonalCenterPolynomial n).range :=
  AlgEquiv.ofInjective (diagonalCenterPolynomial n) (diagonalCenterPolynomial_injective n)

end Langlands.Archimedean.Kostant
