import Langlands.Analysis.PolynomialRootClustering
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Linarith

/-! # Local spectral clusters of complex matrices -/

noncomputable section

open Filter
open scoped Topology

set_option autoImplicit false

namespace Langlands

variable {n : ℕ}

/-- The characteristic-polynomial coefficients of a square matrix below the leading term. -/
def matrixCharpolyLowerCoefficients {K : Type*} [CommRing K] (A : Matrix (Fin n) (Fin n) K) :
    Fin n → K := polynomialLowerCoefficients n A.charpoly

theorem continuous_matrixCharpolyLowerCoefficients {K : Type*} [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (matrixCharpolyLowerCoefficients (K := K) (n := n)) := by
  refine continuous_pi fun i => ?_
  have h : (fun A : Matrix (Fin n) (Fin n) K => matrixCharpolyLowerCoefficients A i) =
      fun A => MvPolynomial.eval (fun ij : Fin n × Fin n => A ij.1 ij.2)
        (MvPolynomial.map (Int.castRingHom K) ((Matrix.charpoly.univ ℤ (Fin n)).coeff i)) := by
    funext A
    rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom]
    rfl
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

open Classical in
/-- The set of distinct roots of a complex matrix's characteristic polynomial. -/
def matrixSpectralRoots (A : Mat) : Finset ℂ := A.charpoly.roots.toFinset

@[simp]
theorem mem_matrixSpectralRoots {A : Mat} {z : ℂ} :
    z ∈ matrixSpectralRoots A ↔ z ∈ A.charpoly.roots :=
  Multiset.mem_toFinset

open Classical in
/-- The roots in a disk, with their characteristic-polynomial multiplicities. -/
def matrixSpectralCluster (B : Mat) (z : ℂ) (r : ℝ) : Multiset ℂ :=
  B.charpoly.roots.filter (fun w => dist w z < r)

/-- With a fixed ordering of the roots at the base matrix, all nearby matrices admit root tuples
with each index as close as prescribed to the corresponding base root. -/
theorem eventually_exists_matrixRootTuple (A : Mat) (a : Fin n → ℂ)
    (ha : A.charpoly = monicRootPolynomial a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B in 𝓝 A, ∃ b : Fin n → ℂ,
      B.charpoly = monicRootPolynomial b ∧ ∀ i, dist (b i) (a i) < ε := by
  have hA : matrixCharpolyLowerCoefficients A = monicRootsToCoeffs a := by
    simp only [matrixCharpolyLowerCoefficients, ha, monicRootsToCoeffs]
  have hcont := (continuous_matrixCharpolyLowerCoefficients (K := ℂ)).continuousAt (x := A)
  rw [ContinuousAt, hA] at hcont
  have hmatching := hcont.eventually (eventually_monicRootsToCoeffs_match a hε)
  filter_upwards [hmatching] with B hB
  obtain ⟨b, hb⟩ := exists_eq_monicRootPolynomial (n := n) B.charpoly_monic
    (IsAlgClosed.splits B.charpoly) (by simp)
  have hBc : monicRootsToCoeffs b = matrixCharpolyLowerCoefficients B := by
    simp only [matrixCharpolyLowerCoefficients, hb, monicRootsToCoeffs]
  obtain ⟨σ, hσ⟩ := hB b hBc
  refine ⟨b ∘ σ.symm, ?_, fun i => ?_⟩
  · rw [hb, monicRootPolynomial, monicRootPolynomial]
    exact (σ.symm.prod_comp (fun j => Polynomial.X - Polynomial.C (b j))).symm
  · have hc := (dist_le_pi_dist _ _ (σ.symm i)).trans_lt hσ
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc

private theorem exists_separated_spectral_radius (s : Finset ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ ε ∧
      ∀ x y : s, x ≠ y → 2 * r < dist (x : ℂ) (y : ℂ) := by
  have h (p : s × s) : ∀ᶠ r : ℝ in 𝓝 0,
      p.1 ≠ p.2 → 2 * r < dist (p.1 : ℂ) (p.2 : ℂ) := by
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun _ hne => (hne hp).elim
    filter_upwards [(isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds
      (show 2 * (0 : ℝ) < dist (p.1 : ℂ) (p.2 : ℂ) by
        rw [mul_zero, dist_pos]
        exact fun h => hp (Subtype.ext h))] with r hr _
    exact hr
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr h)
  let r := min ε (δ / 2)
  have hr : 0 < r := lt_min hε (half_pos hδ)
  have hrδ : dist r 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    exact (min_le_right _ _).trans_lt (half_lt_self hδ)
  exact ⟨r, hr, min_le_left _ _, fun x y hxy => hball hrδ (x, y) hxy⟩

private theorem spectralCenters_eq_of_dist_lt {s : Finset ℂ} {r : ℝ}
    (hsep : ∀ x y : s, x ≠ y → 2 * r < dist (x : ℂ) (y : ℂ))
    {x y : s} {w : ℂ} (hx : dist w (x : ℂ) < r) (hy : dist w (y : ℂ) < r) : x = y := by
  by_contra hne
  have ht := dist_triangle_left (x : ℂ) (y : ℂ) w
  linarith [hsep x y hne]

/-- Small disjoint disks about the distinct roots of a base matrix capture all nearby roots.
Each disk contains the same total multiplicity as its center has at the base matrix. -/
theorem exists_eventually_matrixSpectralClusters (A : Mat) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ ε ∧
      (∀ x y : matrixSpectralRoots A, x ≠ y → 2 * r < dist (x : ℂ) (y : ℂ)) ∧
      ∀ᶠ B in 𝓝 A,
        (∀ b : matrixSpectralRoots B,
          ∃! x : matrixSpectralRoots A, dist (b : ℂ) (x : ℂ) < r) ∧
        ∀ x : matrixSpectralRoots A,
          (matrixSpectralCluster B x r).card = A.charpoly.roots.count (x : ℂ) := by
  classical
  obtain ⟨r, hr, hre, hsep⟩ := exists_separated_spectral_radius (matrixSpectralRoots A) hε
  obtain ⟨a, ha⟩ := exists_eq_monicRootPolynomial (n := n) A.charpoly_monic
    (IsAlgClosed.splits A.charpoly) (by simp)
  have hA : A.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map a := by
    rw [ha, roots_monicRootPolynomial]
  have haMem (i : Fin n) : a i ∈ matrixSpectralRoots A := by
    simp only [matrixSpectralRoots, Multiset.mem_toFinset, hA, Multiset.mem_map]
    exact ⟨i, Finset.mem_univ i, rfl⟩
  refine ⟨r, hr, hre, hsep, ?_⟩
  filter_upwards [eventually_exists_matrixRootTuple A a ha hr] with B hB
  obtain ⟨b, hb, hd⟩ := hB
  have hB : B.charpoly.roots = (Finset.univ : Finset (Fin n)).val.map b := by
    rw [hb, roots_monicRootPolynomial]
  constructor
  · intro w
    have hw := w.property
    simp only [matrixSpectralRoots, Multiset.mem_toFinset, hB, Multiset.mem_map] at hw
    obtain ⟨i, -, hi⟩ := hw
    let x : matrixSpectralRoots A := ⟨a i, haMem i⟩
    have hx : dist (w : ℂ) (x : ℂ) < r := by simpa only [x, ← hi] using hd i
    exact ⟨x, hx, fun y hy => spectralCenters_eq_of_dist_lt hsep hy hx⟩
  · intro x
    rw [matrixSpectralCluster, Multiset.count_eq_card_filter_eq, hB, hA,
      Multiset.filter_map, Multiset.filter_map, Multiset.card_map, Multiset.card_map]
    apply congrArg Multiset.card
    apply Multiset.filter_congr
    intro i _
    change dist (b i) (x : ℂ) < r ↔ (x : ℂ) = a i
    constructor
    · intro hi
      exact congrArg Subtype.val (spectralCenters_eq_of_dist_lt hsep hi
        (show dist (b i) ((⟨a i, haMem i⟩ : matrixSpectralRoots A) : ℂ) < r from hd i))
    · intro hi
      rw [hi]
      exact hd i

/-- Distinct root count can only increase near a base matrix. If the count stays fixed, the
roots match by a nearby bijection preserving each algebraic multiplicity. -/
theorem eventually_matrixSpectralRoots_equiv (A : Mat) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B in 𝓝 A, (matrixSpectralRoots A).card ≤ (matrixSpectralRoots B).card ∧
      ((matrixSpectralRoots B).card = (matrixSpectralRoots A).card →
        ∃ e : matrixSpectralRoots A ≃ matrixSpectralRoots B,
          ∀ x : matrixSpectralRoots A, dist (e x : ℂ) (x : ℂ) < ε ∧
            B.charpoly.roots.count (e x : ℂ) = A.charpoly.roots.count (x : ℂ)) := by
  classical
  obtain ⟨r, _, hre, hsep, hnear⟩ := exists_eventually_matrixSpectralClusters A hε
  filter_upwards [hnear] with B hB
  obtain ⟨hcover, hcount⟩ := hB
  let f (w : matrixSpectralRoots B) : matrixSpectralRoots A := (hcover w).exists.choose
  have hf (w : matrixSpectralRoots B) : dist (w : ℂ) (f w : ℂ) < r :=
    (hcover w).exists.choose_spec
  have hsurj : Function.Surjective f := by
    intro x
    have hpos : 0 < (matrixSpectralCluster B x r).card := by
      rw [hcount]
      exact Multiset.count_pos.mpr (mem_matrixSpectralRoots.mp x.property)
    obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    obtain ⟨hw₀, hw₁⟩ := Multiset.mem_filter.mp hw
    let z : matrixSpectralRoots B := ⟨w, mem_matrixSpectralRoots.mpr hw₀⟩
    exact ⟨z, spectralCenters_eq_of_dist_lt hsep (hf z) hw₁⟩
  refine ⟨by simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective f hsurj, ?_⟩
  intro hcard
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, by simpa only [Fintype.card_coe]⟩
  let e := (Equiv.ofBijective f hbij).symm
  have he (x : matrixSpectralRoots A) : f (e x) = x :=
    e.symm_apply_apply x
  have hclose (x : matrixSpectralRoots A) : dist (e x : ℂ) (x : ℂ) < r := by
    simpa only [he] using hf (e x)
  refine ⟨e, fun x => ⟨(hclose x).trans_le hre, ?_⟩⟩
  rw [← hcount x, matrixSpectralCluster, Multiset.count_eq_card_filter_eq]
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro w hw
  constructor
  · intro hw'
    rw [← hw']
    exact hclose x
  · intro hw'
    let z : matrixSpectralRoots B := ⟨w, mem_matrixSpectralRoots.mpr hw⟩
    have hz : f z = x := spectralCenters_eq_of_dist_lt hsep (hf z) hw'
    exact congrArg Subtype.val (hbij.injective ((he x).trans hz.symm))

end Langlands
