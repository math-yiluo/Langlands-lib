import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Multiset.Fintype
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Properness of the map from roots to monic coefficient vectors -/

noncomputable section

open Polynomial Filter
open scoped Topology NNReal

set_option autoImplicit false

namespace Langlands

section Ring

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The monic polynomial whose linear factors are indexed by the input tuple. -/
def monicRootPolynomial (a : Fin n → K) : K[X] := ∏ i, (X - C (a i))

/-- The coefficients strictly below degree `n`, in ascending order. -/
def polynomialLowerCoefficients (n : ℕ) (p : K[X]) : Fin n → K := fun i => p.coeff i

/-- The coefficient vector of the product of the monic factors `X - a i`. -/
def monicRootsToCoeffs (a : Fin n → K) : Fin n → K :=
  polynomialLowerCoefficients n (monicRootPolynomial a)

theorem monic_monicRootPolynomial (a : Fin n → K) : (monicRootPolynomial a).Monic :=
  monic_prod_X_sub_C a Finset.univ

@[simp]
theorem natDegree_monicRootPolynomial [Nontrivial K] (a : Fin n → K) :
    (monicRootPolynomial a).natDegree = n := by
  rw [monicRootPolynomial, natDegree_prod_of_monic Finset.univ (fun i => X - C (a i))
    (fun i _ => monic_X_sub_C (a i))]
  simp

theorem polynomial_eq_of_lowerCoefficients_eq {p q : K[X]} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = n) (hqd : q.natDegree = n)
    (h : polynomialLowerCoefficients n p = polynomialLowerCoefficients n q) : p = q := by
  ext k
  rcases lt_trichotomy k n with hk | hk | hk
  · exact congrFun h ⟨k, hk⟩
  · rw [hk]
    calc
      p.coeff n = p.leadingCoeff := by rw [← hpd, coeff_natDegree]
      _ = q.leadingCoeff := hp.leadingCoeff.trans hq.leadingCoeff.symm
      _ = q.coeff n := by rw [← hqd, coeff_natDegree]
  · rw [coeff_eq_zero_of_natDegree_lt (hpd ▸ hk), coeff_eq_zero_of_natDegree_lt (hqd ▸ hk)]

theorem roots_monicRootPolynomial [IsDomain K] (a : Fin n → K) :
    (monicRootPolynomial a).roots = (Finset.univ : Finset (Fin n)).val.map a := by
  change ((Finset.univ.val.map (fun i : Fin n => X - C (a i))).prod).roots = _
  rw [show (fun i : Fin n => X - C (a i)) = (fun z => X - C z) ∘ a from rfl,
    ← Multiset.map_map, roots_multiset_prod_X_sub_C]

/-- Enumerating the roots of a split monic polynomial gives a tuple of the prescribed degree. -/
theorem exists_eq_monicRootPolynomial [IsDomain K] {p : K[X]} (hp : p.Monic) (hs : p.Splits)
    (hpd : p.natDegree = n) : ∃ a : Fin n → K, p = monicRootPolynomial a := by
  classical
  have hcard : Fintype.card p.roots = n := by
    rw [Multiset.card_coe, ← hs.natDegree_eq_card_roots, hpd]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : K), ?_⟩
  rw [monicRootPolynomial, e.prod_comp (fun x : p.roots => X - C (x : K))]
  have hprod : (∏ x : p.roots, (X - C (x : K))) =
      (p.roots.map fun x => X - C x).prod :=
    congrArg Multiset.prod (Multiset.map_univ p.roots (fun x : K => X - C x))
  exact (hs.eq_prod_roots_of_monic hp).trans hprod.symm

end Ring

section Continuous

variable {E I K : Type*} [TopologicalSpace E] [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/-- Coefficients of a finite polynomial product vary continuously if the factor coefficients do. -/
theorem continuous_polynomialCoeff_prod (s : Finset I) (p : I → E → K[X])
    (hp : ∀ i ∈ s, ∀ j, Continuous (fun x => (p i x).coeff j)) (k : ℕ) :
    Continuous (fun x => (∏ i ∈ s, p i x).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa only [Finset.prod_empty] using continuous_const
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, coeff_mul]
    exact continuous_finsetSum _ (fun j _ =>
      (hp i (Finset.mem_insert_self i s) j.1).mul
        (ih (fun a ha => hp a (Finset.mem_insert_of_mem ha)) j.2))

theorem continuous_monicRootsToCoeffs (n : ℕ) : Continuous (monicRootsToCoeffs (K := K) (n := n)) := by
  apply continuous_pi
  intro i
  change Continuous (fun a : Fin n → K => (∏ j : Fin n, (X - C (a j))).coeff (i : ℕ))
  apply continuous_polynomialCoeff_prod Finset.univ (fun (j : Fin n) (a : Fin n → K) =>
    X - C (a j))
  intro j _ k
  simp only [coeff_sub, coeff_C]
  split_ifs
  · exact continuous_const.sub (continuous_apply j)
  · exact continuous_const

end Continuous

section Proper

variable {K : Type*} [NormedField K] {n : ℕ}

private theorem norm_le_monicRootsToCoeffs_add_one (a : Fin n → K) :
    ‖a‖ ≤ ‖monicRootsToCoeffs a‖ + 1 := by
  let p := monicRootPolynomial a
  have hp := monic_monicRootPolynomial a
  have hsup : (Finset.range n).sup (fun j => ‖p.coeff j‖₊) ≤ ‖monicRootsToCoeffs a‖₊ := by
    apply Finset.sup_le
    intro j hj
    exact nnnorm_le_pi_nnnorm (monicRootsToCoeffs a) ⟨j, Finset.mem_range.mp hj⟩
  have hb : p.cauchyBound ≤ ‖monicRootsToCoeffs a‖₊ + 1 := by
    change (monicRootPolynomial a).cauchyBound ≤ _
    rw [cauchyBound, natDegree_monicRootPolynomial, hp.leadingCoeff, nnnorm_one, div_one]
    exact add_le_add hsup le_rfl
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
  have hroot : p.IsRoot (a i) := by
    apply (mem_roots hp.ne_zero).mp
    rw [roots_monicRootPolynomial, Multiset.mem_map]
    exact ⟨i, Finset.mem_univ i, rfl⟩
  have hi := (hroot.norm_lt_cauchyBound hp.ne_zero).le.trans hb
  exact_mod_cast hi

/-- Over a proper normed field the map from root tuples to monic coefficient vectors is proper. -/
theorem isProperMap_monicRootsToCoeffs [ProperSpace K] (n : ℕ) :
    IsProperMap (monicRootsToCoeffs (K := K) (n := n)) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_monicRootsToCoeffs n, ?_⟩
  intro s hs
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  apply Metric.isCompact_of_isClosed_isBounded (hs.isClosed.preimage (continuous_monicRootsToCoeffs n))
  exact isBounded_iff_forall_norm_le.mpr ⟨R + 1, fun a ha =>
    (norm_le_monicRootsToCoeffs_add_one a).trans (add_le_add (hR _ ha) le_rfl)⟩

private theorem exists_perm_of_coeffs_eq {a b : Fin n → K}
    (h : monicRootsToCoeffs b = monicRootsToCoeffs a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, b i = a (σ i) := by
  classical
  have hp := polynomial_eq_of_lowerCoefficients_eq
    (monic_monicRootPolynomial b) (monic_monicRootPolynomial a)
    (natDegree_monicRootPolynomial b) (natDegree_monicRootPolynomial a) h
  have hr := congrArg Polynomial.roots hp
  simp only [roots_monicRootPolynomial] at hr
  have hcard (f : Fin n → K) (z : K) :
      Fintype.card {i : Fin n // f i = z} = ((Finset.univ : Finset (Fin n)).val.map f).count z := by
    rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val]
    exact congrArg Finset.card (Finset.filter_congr (fun i _ => eq_comm))
  let e (z : K) : {i : Fin n // b i = z} ≃ {i : Fin n // a i = z} :=
    Fintype.equivOfCardEq (by rw [hcard, hcard, hr])
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

/-- Every root tuple for sufficiently close coefficient vectors is close to a permutation of
the original root tuple, even at repeated roots. -/
theorem eventually_monicRootsToCoeffs_match [ProperSpace K] (a : Fin n → K) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ c in 𝓝 (monicRootsToCoeffs a), ∀ b : Fin n → K, monicRootsToCoeffs b = c →
      ∃ σ : Equiv.Perm (Fin n), dist b (a ∘ σ) < ε := by
  let U : Set (Fin n → K) := ⋃ σ : Equiv.Perm (Fin n), Metric.ball (a ∘ σ) ε
  have hU : IsOpen U := isOpen_iUnion (fun _ => Metric.isOpen_ball)
  have H := (isProperMap_monicRootsToCoeffs (K := K) n).isClosedMap.eventually_nhds_fiber
    (p := fun b => b ∈ U) (monicRootsToCoeffs a) (by
      intro b hb
      obtain ⟨σ, hσ⟩ := exists_perm_of_coeffs_eq (by simpa only [Set.mem_preimage,
        Set.mem_singleton_iff] using hb)
      apply hU.mem_nhds
      exact Set.mem_iUnion.mpr ⟨σ, by rw [show b = a ∘ σ from funext hσ]; exact Metric.mem_ball_self hε⟩)
  filter_upwards [H] with c hc b hb
  have hbU : b ∈ U := hc b (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hb)
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hbU
  exact ⟨σ, hσ⟩

end Proper

end Langlands
