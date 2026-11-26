import Langlands.Global.Arithmetic.PolynomialRootNeighborhood
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Galois.Infinite

/-! # Coefficient neighborhoods preserving polynomial factorization types -/

noncomputable section

open Polynomial

namespace Langlands.Global.FieldRealization

universe u v

variable {F : Type u} [NormedField F]

/-- Monic polynomials of the same degree in this coefficient neighborhood
split over the base field and have distinct roots. -/
def SplitCoefficientNeighborhood (f : F[X]) :=
  {ε : ℝ // 0 < ε ∧ ∀ (g : F[X]), g.Monic → g.natDegree = f.natDegree →
    (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → g.Splits ∧ g.Separable}

private theorem exists_splitCoefficientNeighborhood {L : Type v} [NormedField L]
    [NormedAlgebra F L] [IsAlgClosed L] [IsGalois F L]
    (hIso : ∀ (σ : L ≃ₐ[F] L) (x : L), ‖σ x‖ = ‖x‖)
    (f : F[X]) (hf : f.Monic) (hn : 0 < f.natDegree) (hSplit : f.Splits) (hSep : f.Separable) :
    Nonempty (SplitCoefficientNeighborhood f) := by
  classical
  let S := f.rootSet F
  let i : S → L := fun a => algebraMap F L a.val
  have hi : Function.Injective i := fun _ _ h => Subtype.ext ((algebraMap F L).injective h)
  let separations : Finset ℝ :=
    (Finset.univ : Finset (S × S)).image (fun p => if p.1 = p.2 then 1 else ‖i p.1 - i p.2‖ / 2)
  let bounds := insert 1 separations
  have hb : bounds.Nonempty := by simp [bounds]
  let r := bounds.inf' hb id
  have hr : 0 < r := by
    dsimp only [r]
    rw [Finset.lt_inf'_iff]
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · norm_num
    · obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hz
      split_ifs with h
      · norm_num
      · exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hi.ne h))) (by norm_num)
  have hrsep {a b : S} (hab : a ≠ b) : 2 * r ≤ ‖i a - i b‖ := by
    have hz : ‖i a - i b‖ / 2 ∈ bounds := by
      refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, ?_⟩)
      simp [hab]
    have h : r ≤ ‖i a - i b‖ / 2 := Finset.inf'_le id hz
    linarith
  let sizes := insert 1 ((Finset.univ : Finset S).image (fun a => max ‖i a‖ 1))
  have hsz : sizes.Nonempty := by simp [sizes]
  let B := sizes.sup' hsz id
  have hB : 0 < B :=
    zero_lt_one.trans_le (Finset.le_sup' id (Finset.mem_insert_self (a := 1) _))
  have hiB (a : S) : max ‖i a‖ 1 ≤ B := by
    have ha : max ‖i a‖ 1 ∈ sizes :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun a => max ‖i a‖ 1) (Finset.mem_univ a))
    exact Finset.le_sup' id ha
  let ε := (r / B) ^ f.natDegree / (f.natDegree + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hrad : (((f.natDegree : ℝ) + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ = r / B := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (by positivity) hn.ne']
  refine ⟨ε, hε, fun g hg hdeg hcoeff => ?_⟩
  have hgs : (g.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have hnear (a : S) : ∃ b : g.rootSet L, ‖i a - b.val‖ < r := by
    have ha : aeval (i a) f = 0 := by
      change aeval ((Algebra.ofId F L) a.val) f = 0
      rw [aeval_algHom_apply, hf.mem_rootSet.mp a.property, map_zero]
    obtain ⟨b, hbr, hdist⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε ha hf hg hdeg
      hcoeff hgs
    refine ⟨⟨b, by simpa [Polynomial.rootSet_def] using hbr⟩, hdist.trans_le ?_⟩
    rw [hrad]
    exact (mul_le_mul_of_nonneg_left (hiB a) (div_nonneg hr.le hB.le)).trans_eq
      (div_mul_cancel₀ r hB.ne')
  choose β hβ using hnear
  have hseparated {a b : S} {y : L} (ha : ‖i a - y‖ < r) (hb : ‖i b - y‖ < r) : a = b := by
    by_contra hab
    have h := (hrsep hab).trans (norm_sub_le_norm_sub_add_norm_sub (i a) y (i b))
    rw [norm_sub_rev y (i b)] at h
    linarith
  have hβinj : Function.Injective β := fun a b hab =>
    hseparated (hβ a) (by rw [hab]; exact hβ b)
  have hS : Fintype.card S = f.natDegree := by
    apply card_rootSet_eq_natDegree hSep
    simpa using hSplit
  have hcard : Fintype.card (g.rootSet L) = g.natDegree := by
    have hle : Fintype.card (g.rootSet L) ≤ g.natDegree := by
      simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans g.card_roots_map_le_natDegree
    have hge := Fintype.card_le_of_injective β hβinj
    rw [hS, ← hdeg] at hge
    exact le_antisymm hle hge
  have hβsurj : Function.Surjective β :=
    ((Fintype.bijective_iff_injective_and_card β).mpr
      ⟨hβinj, hS.trans (hdeg.symm.trans hcard.symm)⟩).2
  refine ⟨hgs.of_splits_algebraMap (fun x hx => ?_),
    (card_rootSet_eq_natDegree_iff_of_splits hg.ne_zero hgs).mp hcard⟩
  change x ∈ Set.range (algebraMap F L)
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  obtain ⟨a, ha⟩ := hβsurj ⟨x, hx⟩
  change β a = _ at ha
  have hx' : (β a).val = x := congrArg Subtype.val ha
  intro σ
  have hσ : σ x ∈ g.rootSet L := by
    apply hg.mem_rootSet.mpr
    change aeval (σ.toAlgHom x) g = 0
    rw [aeval_algHom_apply σ.toAlgHom, hg.mem_rootSet.mp hx, map_zero]
  obtain ⟨b, hb⟩ := hβsurj ⟨σ x, hσ⟩
  have hσx : (β b).val = σ x := congrArg Subtype.val hb
  have hσa : ‖i a - σ x‖ < r := by
    calc
      _ = ‖σ (i a - x)‖ := by rw [map_sub, show σ (i a) = i a from σ.commutes a.val]
      _ = ‖i a - x‖ := hIso σ _
      _ < r := hx' ▸ hβ a
  have hσb : ‖i b - σ x‖ < r := hσx ▸ hβ b
  have hab := hseparated hσa hσb
  exact hσx.symm.trans ((congrArg (fun a => (β a).val) hab.symm).trans hx')

section Nonarchimedean

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F] [CharZero F]

/-- A completely split separable polynomial stays split under small coefficient
perturbations over a complete nonarchimedean field of characteristic zero. -/
def splitCoefficientNeighborhood_nonarchimedean (f : F[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) (hSplit : f.Splits) (hSep : f.Separable) :
    SplitCoefficientNeighborhood f := by
  let L := AlgebraicClosure F
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField F L
  let : NormedAlgebra F L := spectralNorm.normedAlgebra F L
  exact Classical.choice (exists_splitCoefficientNeighborhood (L := L) (fun σ x => by
    change spectralNorm F L (σ x) = spectralNorm F L x
    exact (spectralNorm_eq_of_equiv σ x).symm)
    f hf hn hSplit hSep)

end Nonarchimedean

/-- Monic polynomials of the same degree in this coefficient neighborhood are irreducible. -/
def IrreducibleCoefficientNeighborhood (f : F[X]) :=
  {ε : ℝ // 0 < ε ∧ ∀ (g : F[X]), g.Monic → g.natDegree = f.natDegree →
    (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → Irreducible g}

/-- Irreducibility of a monic polynomial is stable under small coefficient
perturbations over a complete nonarchimedean field of characteristic zero. -/
def irreducibleCoefficientNeighborhood_nonarchimedean {F : Type u} [NontriviallyNormedField F]
    [CompleteSpace F] [IsUltrametricDist F] [CharZero F] (f : F[X]) (hf : f.Monic)
    (hIrr : Irreducible f) : IrreducibleCoefficientNeighborhood f := by
  let L := AlgebraicClosure F
  let : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField F L
  let : NormedAlgebra F L := spectralNorm.normedAlgebra F L
  have hex : Nonempty (IrreducibleCoefficientNeighborhood f) := by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (k := L) f
      (natDegree_pos_iff_degree_pos.mp hIrr.natDegree_pos).ne'
    have hfx : minpoly F x = f := (minpoly.eq_of_irreducible_of_monic hIrr hx hf).symm
    have hxsep : IsSeparable F x := by
      change (minpoly F x).Separable
      rw [hfx]
      exact hIrr.separable
    refine ⟨⟨coefficientRadius F x, coefficientRadius_pos x, fun g hg hdeg hcoeff => ?_⟩⟩
    obtain ⟨y, hy, hfield⟩ := exists_root_adjoin_eq_of_coeff_lt x hxsep (IsAlgClosed.splits _)
      g hg (hfx.symm ▸ hdeg) (hfx.symm ▸ hcoeff) (IsAlgClosed.splits _)
    have hyi : IsIntegral F y := ⟨g, hg, hy⟩
    have hdeg' := congrArg (fun P : IntermediateField F L => Module.finrank F P) hfield
    rw [IntermediateField.adjoin.finrank hxsep.isIntegral, IntermediateField.adjoin.finrank hyi,
      hfx] at hdeg'
    have hg' : g = minpoly F y := eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hyi) hg (minpoly.dvd F y hy) (hdeg.trans hdeg').le
    rw [hg']
    exact minpoly.irreducible hyi
  exact Classical.choice hex

/-- A completely split separable real polynomial stays split under small
coefficient perturbations. -/
def splitCoefficientNeighborhood_real (f : ℝ[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) (hSplit : f.Splits) (hSep : f.Separable) :
    SplitCoefficientNeighborhood f := by
  let : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
  have hIso (σ : ℂ ≃ₐ[ℝ] ℂ) (z : ℂ) : ‖σ z‖ = ‖z‖ := by
    have hcard : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]
    have hc : Complex.conjAe ≠ (1 : ℂ ≃ₐ[ℝ] ℂ) := by
      intro h
      have h' := congrArg (fun e : ℂ ≃ₐ[ℝ] ℂ => (e Complex.I).im) h
      norm_num at h'
    obtain ⟨s, -, hs⟩ := (Nat.card_eq_two_iff' (1 : ℂ ≃ₐ[ℝ] ℂ)).mp hcard
    by_cases hσ : σ = 1
    · rw [hσ]
      rfl
    · rw [(hs σ hσ).trans (hs Complex.conjAe hc).symm]
      exact Complex.norm_conj z
  exact Classical.choice (exists_splitCoefficientNeighborhood (L := ℂ) hIso f hf hn hSplit hSep)

end Langlands.Global.FieldRealization
