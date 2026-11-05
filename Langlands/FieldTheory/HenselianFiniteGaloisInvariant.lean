import Langlands.FieldTheory.HenselianSmallConjugateDescent

/-! # Henselian invariance in finite Galois extensions -/

noncomputable section

open scoped NNReal BigOperators

namespace Langlands.FieldTheory

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The subgroup preserving an actual real valuation. -/
def realValuationDecompositionGroup (w : Valuation Ω ℝ≥0) : Subgroup Gal(Ω/K) where
  carrier := {σ | ∀ x, w (σ x) = w x}
  one_mem' _ := rfl
  mul_mem' {σ τ} hσ hτ x := by
    change w (σ (τ x)) = w x
    rw [hσ, hτ]
  inv_mem' {σ} hσ x := by
    change w (σ.symm x) = w x
    have h := hσ (σ.symm x)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm

/-- Every normalized prolongation of a nontrivial Henselian real valuation
is invariant under a finite Galois group. -/
theorem realValuation_invariant_of_finiteGalois [FiniteDimensional K Ω] [IsGalois K Ω]
    (ν : Valuation K ℝ≥0) (hν : ν.IsNontrivial)
    [HenselianLocalRing ν.valuationSubring]
    (w : Valuation Ω ℝ≥0) (hw : w.comap (algebraMap K Ω) = ν) :
    ∀ (σ : Gal(Ω/K)) (x : Ω), w (σ x) = w x := by
  classical
  let D := realValuationDecompositionGroup (K := K) w
  let : Fintype Gal(Ω/K) := Fintype.ofFinite _
  let : Fintype D := Fintype.ofFinite _
  let I := Set.range (fun σ : Gal(Ω/K) => w.comap σ.toRingHom)
  let : Fintype I := (Set.finite_range (fun σ : Gal(Ω/K) => w.comap σ.toRingHom)).fintype
  let i₀ : I := ⟨w, ⟨1, by apply Valuation.ext; intro x; rfl⟩⟩
  have hres : ∀ i : I, i.val.comap (algebraMap K Ω) = ν := by
    rintro ⟨wi, σ, rfl⟩
    apply Valuation.ext
    intro x
    change w (σ (algebraMap K Ω x)) = ν x
    rw [σ.commutes]
    exact congrArg (fun v : Valuation K ℝ≥0 => v x) hw
  obtain ⟨a, ha, hsep⟩ := exists_normalizedRealProlongation_separator
    ν hν (fun i : I => i.val) Subtype.val_injective hres i₀
  change w a < 1 at ha
  have houtside : ∀ σ : Gal(Ω/K), σ ∉ D → w (σ a) = 1 := by
    intro σ hσ
    let iσ : I := ⟨w.comap σ.toRingHom, ⟨σ, rfl⟩⟩
    have hne : iσ ≠ i₀ := by
      intro he
      have hval := congrArg (fun i : I => i.val) he
      apply hσ
      intro x
      exact congrArg (fun v : Valuation Ω ℝ≥0 => v x) hval
    have hs := hsep iσ hne
    change w (σ (a - 1)) < 1 at hs
    simp only [map_sub, map_one] at hs
    have h := w.map_one_add_of_lt hs
    have he : 1 + (σ a - 1) = σ a := by ring
    rwa [he] at h
  let b : Ω := ∏ d : D, (d : Gal(Ω/K)) a
  have hbsmall : w b < 1 := by
    change w (∏ d : D, (d : Gal(Ω/K)) a) < 1
    rw [map_prod]
    have he : ∀ d : D, w ((d : Gal(Ω/K)) a) = w a := fun d => d.property a
    simp_rw [he]
    rw [Finset.prod_const, Finset.card_univ]
    exact pow_lt_one₀ zero_le ha Fintype.card_ne_zero
  have hbfix : ∀ d : D, (d : Gal(Ω/K)) b = b := by
    intro d
    change (d : Gal(Ω/K)) (∏ e : D, (e : Gal(Ω/K)) a) =
      ∏ e : D, (e : Gal(Ω/K)) a
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft d) _ _ (fun _ => rfl)
  have hbunit : ∀ σ : Gal(Ω/K), σ ∉ D → w (σ b) = 1 := by
    intro σ hσ
    change w (σ (∏ d : D, (d : Gal(Ω/K)) a)) = 1
    rw [map_prod, map_prod]
    apply Finset.prod_eq_one
    intro d _
    have hsd : σ * (d : Gal(Ω/K)) ∉ D := by
      intro h
      apply hσ
      have hm := D.mul_mem h (D.inv_mem d.property)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hm
    exact houtside (σ * (d : Gal(Ω/K))) hsd
  have hother : ∀ r ∈ (minpoly K b).aroots Ω, r ≠ b → w r = 1 := by
    intro r hr hrb
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic (R := K) b) (Polynomial.mem_aroots.mp hr).2
    have hσD : σ ∉ D := by
      intro hd
      apply hrb
      rw [← hσ]
      exact hbfix ⟨σ, hd⟩
    rw [← hσ]
    exact hbunit σ hσD
  obtain ⟨c, hc⟩ := mem_range_of_small_and_other_conjugates_units ν w hw b hbsmall hother
  intro σ x
  have hmem : σ ∈ D := by
    by_contra hσ
    have hunit := hbunit σ hσ
    have hfix : σ b = b := by rw [← hc, σ.commutes]
    rw [hfix] at hunit
    exact hbsmall.ne hunit
  exact hmem x

end Langlands.FieldTheory
