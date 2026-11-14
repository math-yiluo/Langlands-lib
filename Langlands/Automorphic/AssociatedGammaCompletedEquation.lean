import Langlands.Global.Factors.RelativeWeilEngine
import Langlands.Representation.RankinSelberg.RationalContinuation
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.DiscreteSubset

/-!
# From a completed global equation to the comparison-engine format

A completed equation `Λ(s) = (∏_(v ∈ S) e_v(s)) ε_∞(s) Λ∨(1 - s)`, where `Λ` is the
archimedean product times an absolutely convergent Euler product on a right half-plane,
gives the admissibility, Euler-product and functional-equation inputs of the finite
comparison engine at the exceptional set `univ.disjSum B` for every finite `B ⊇ S`
outside which the epsilon factors are `1`.

Only the finitely many factors in `B` must be nonzero on a right half-plane. The
partial L-function has nonzero germ because each local factor vanishes only on a
countable set, the finite places are countable, and a product of nonzero factors with
summable distance to `1` is nonzero.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Langlands.Global.FunctionalEquationComparison

namespace CompletedEquationAdapter

open RelativeWeilEngine

/-- A product of nonzero complex factors with summable distance to `1` is nonzero. -/
theorem hasProd_ne_zero_of_summable {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a)
    (hf : ∀ i, f i ≠ 0) (hs : Summable fun i => ‖f i - 1‖) : a ≠ 0 := by
  have e : ∀ i, 1 + (f i - 1) = f i := fun i => by ring
  have h1 : ∏' i, (1 + (f i - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun i => by rw [e]; exact hf i) hs
  simp only [e] at h1
  rwa [h.tprod_eq] at h1

/-- A function with nonzero germ everywhere vanishes only on a countable set: the zero set
is discrete, and `ℂ` is second countable. -/
theorem NonzeroMeromorphic.countable_zeros {f : ℂ → ℂ} (hf : NonzeroMeromorphic f) :
    {s : ℂ | f s = 0}.Countable := by
  have hd : DiscreteTopology {s : ℂ | f s = 0} := by
    rw [discreteTopology_subtype_iff]
    intro x _
    exact Filter.inf_principal_eq_bot.mpr (hf.eventually_ne_zero x)
  exact (HereditarilyLindelofSpace.isLindelof _).countable hd

/-- The quotient of the completed function by its archimedean factor has a nonzero
germ: the archimedean factor is nonzero on a right half-plane, the local factors vanish
only on countable sets, and off their union the convergent Euler product is nonzero. -/
theorem nonzeroMeromorphic_div_archimedean {Q : Type*} [Countable Q] (l : Q → ℂ → ℂ)
    (hzero : ∀ v, {s : ℂ | l v s = 0}.Countable) (Λ L : ℂ → ℂ) (hΛ : Meromorphic Λ)
    (hL : NonzeroMeromorphic L) (σ : ℝ) (hLne : ∀ s : ℂ, σ < s.re → L s ≠ 0)
    (hprod : ∀ s : ℂ, σ < s.re → Summable (fun v => ‖l v s - 1‖) ∧
      ∃ p : ℂ, HasProd (fun v => l v s) p ∧ Λ s = L s * p) :
    NonzeroMeromorphic (fun s => Λ s * (L s)⁻¹) := by
  have hmero : Meromorphic (fun s => Λ s * (L s)⁻¹) := fun z => (hΛ z).mul (hL.1 z).inv
  refine ⟨hmero, fun z => ?_⟩
  set x : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hx : σ < x.re := by simp [x]
  have hxtop : meromorphicOrderAt (fun s => Λ s * (L s)⁻¹) x ≠ ⊤ := by
    intro htop
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | σ < s.re} ∈ 𝓝[≠] x := nhdsWithin_le_nhds (hopen.mem_nhds hx)
    obtain ⟨U, hU, hUprop⟩ := (eventually_nhdsWithin_iff.mp (htop.and hmem)).exists_mem
    set Z : Set ℂ := (⋃ v, {s : ℂ | l v s = 0}) ∪ {x}
    have hZ : Z.Countable := (Set.countable_iUnion hzero).union (Set.countable_singleton x)
    obtain ⟨s, hsZ, hsU⟩ := (hZ.dense_compl ℂ).exists_mem_open isOpen_interior
      ⟨x, mem_interior_iff_mem_nhds.mpr hU⟩
    have hsx : s ≠ x := fun h => hsZ (Or.inr h)
    have hlne : ∀ v, l v s ≠ 0 := fun v h => hsZ (Or.inl (Set.mem_iUnion.mpr ⟨v, h⟩))
    obtain ⟨hzero_s, hσs⟩ := hUprop s (interior_subset hsU) hsx
    obtain ⟨hsum, p, hp, hΛp⟩ := hprod s hσs
    have hpne : p ≠ 0 := hasProd_ne_zero_of_summable hp hlne hsum
    apply hpne
    have hLs := hLne s hσs
    rw [hΛp, mul_comm (L s) p, mul_assoc, mul_inv_cancel₀ hLs, mul_one] at hzero_s
    exact hzero_s
  exact (Meromorphic.meromorphicOn hmero (s := Set.univ)).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ x) (Set.mem_univ z) hxtop

/-- Conversion of a completed global equation to the format of the finite comparison
engine, for a finite exceptional set `B ⊇ S` of finite places outside `S` of which the
epsilon factors are `1`. The partial L-functions are the completed functions divided by
the archimedean factors and the local factors in `B`. -/
theorem functionalEquation_of_completedEquation
    {I Q : Type*} [Fintype I] [Countable Q] [DecidableEq (I ⊕ Q)]
    (arch : I → LocalFactors) (l d e : Q → ℂ → ℂ) (Linf Ldinf εinf : ℂ → ℂ)
    (harch : ∀ w, NonzeroMeromorphic (arch w).lFactor ∧
      NonzeroMeromorphic (arch w).dualLFactor ∧ NonzeroMeromorphic (arch w).epsilonFactor)
    (hA : ∀ s, ∏ w, (arch w).lFactor s = Linf s)
    (hAd : ∀ s, ∏ w, (arch w).dualLFactor s = Ldinf s)
    (hAe : ∀ s, ∏ w, (arch w).epsilonFactor s = εinf s)
    (σL : ℝ) (hLne : ∀ s : ℂ, σL < s.re → Linf s ≠ 0 ∧ Ldinf s ≠ 0)
    (hl : ∀ v, NonzeroMeromorphic (l v) ∧ NonzeroMeromorphic (d v) ∧ NonzeroMeromorphic (e v))
    (hlhalf : ∀ v, ∃ σv : ℝ, ∀ s : ℂ, σv < s.re → l v s ≠ 0 ∧ d v s ≠ 0)
    (S B : Finset Q) (hSB : S ⊆ B) (he1 : ∀ v ∈ B, v ∉ S → ∀ s, e v s = 1)
    (σ : ℝ) (Λ Λd : ℂ → ℂ) (hΛ : MeromorphicOn Λ Set.univ) (hΛd : MeromorphicOn Λd Set.univ)
    (hprod : ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖l v s - 1‖) ∧ Summable (fun v => ‖d v s - 1‖) ∧
      ∃ p pd : ℂ, HasProd (fun v => l v s) p ∧ HasProd (fun v => d v s) pd ∧
        Λ s = Linf s * p ∧ Λd s = Ldinf s * pd)
    (hfe : ∀ᶠ s in Filter.codiscrete ℂ,
      Λ s = (∏ v ∈ S, e v s) * εinf s * Λd (1 - s)) :
    ∃ σ' : ℝ,
      Admissible (FiniteEulerData.mk (Sum.elim arch fun v => ⟨l v, d v, e v⟩)
          (fun s => Λ s * (Linf s)⁻¹ * (∏ z ∈ B, l z s)⁻¹)
          (fun s => Λd s * (Ldinf s)⁻¹ * (∏ z ∈ B, d z s)⁻¹))
        ((Finset.univ : Finset I).disjSum B) ∧
      HasEulerProductsOutside (FiniteEulerData.mk (Sum.elim arch fun v => ⟨l v, d v, e v⟩)
          (fun s => Λ s * (Linf s)⁻¹ * (∏ z ∈ B, l z s)⁻¹)
          (fun s => Λd s * (Ldinf s)⁻¹ * (∏ z ∈ B, d z s)⁻¹))
        ((Finset.univ : Finset I).disjSum B) σ' ∧
      FunctionalEquation (FiniteEulerData.mk (Sum.elim arch fun v => ⟨l v, d v, e v⟩)
          (fun s => Λ s * (Linf s)⁻¹ * (∏ z ∈ B, l z s)⁻¹)
          (fun s => Λd s * (Ldinf s)⁻¹ * (∏ z ∈ B, d z s)⁻¹))
        ((Finset.univ : Finset I).disjSum B) := by
  classical
  have hΛm : Meromorphic Λ := fun z => hΛ z (Set.mem_univ z)
  have hΛdm : Meromorphic Λd := fun z => hΛd z (Set.mem_univ z)
  have hLnm : NonzeroMeromorphic Linf := by
    have h := NonzeroMeromorphic.finsetProd (Finset.univ : Finset I)
      (f := fun w => (arch w).lFactor) fun w _ => (harch w).1
    have hfun : (fun s => ∏ w, (arch w).lFactor s) = Linf := funext hA
    rwa [hfun] at h
  have hLdnm : NonzeroMeromorphic Ldinf := by
    have h := NonzeroMeromorphic.finsetProd (Finset.univ : Finset I)
      (f := fun w => (arch w).dualLFactor) fun w _ => (harch w).2.1
    have hfun : (fun s => ∏ w, (arch w).dualLFactor s) = Ldinf := funext hAd
    rwa [hfun] at h
  have hΛe : NonzeroMeromorphic (fun s => Λ s * (Linf s)⁻¹) :=
    nonzeroMeromorphic_div_archimedean l (fun v => NonzeroMeromorphic.countable_zeros (hl v).1) Λ Linf hΛm hLnm (max σ σL)
      (fun s hs => (hLne s (lt_of_le_of_lt (le_max_right _ _) hs)).1)
      (fun s hs => by
        obtain ⟨h1, _, p, _, hp, _, hΛp, _⟩ := hprod s (lt_of_le_of_lt (le_max_left _ _) hs)
        exact ⟨h1, p, hp, hΛp⟩)
  have hΛde : NonzeroMeromorphic (fun s => Λd s * (Ldinf s)⁻¹) :=
    nonzeroMeromorphic_div_archimedean d (fun v => NonzeroMeromorphic.countable_zeros (hl v).2.1) Λd Ldinf hΛdm hLdnm (max σ σL)
      (fun s hs => (hLne s (lt_of_le_of_lt (le_max_right _ _) hs)).2)
      (fun s hs => by
        obtain ⟨_, h2, _, pd, _, hpd, _, hΛpd⟩ := hprod s (lt_of_le_of_lt (le_max_left _ _) hs)
        exact ⟨h2, pd, hpd, hΛpd⟩)
  have hPB : NonzeroMeromorphic (fun s => ∏ z ∈ B, l z s) :=
    NonzeroMeromorphic.finsetProd B fun z _ => (hl z).1
  have hPBd : NonzeroMeromorphic (fun s => ∏ z ∈ B, d z s) :=
    NonzeroMeromorphic.finsetProd B fun z _ => (hl z).2.1
  choose σv hσv using hlhalf
  set σB : ℝ := ∑ z ∈ B, |σv z|
  have hσB : ∀ z ∈ B, σv z ≤ σB := fun z hz =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun z => |σv z|)
      (fun i _ => abs_nonneg _) hz)
  refine ⟨max (max σ σL) σB, ⟨NonzeroMeromorphic.mul hΛe (NonzeroMeromorphic.inv hPB),
    NonzeroMeromorphic.mul hΛde (NonzeroMeromorphic.inv hPBd), fun v hv => ?_⟩,
    fun s hs => ?_, ?_⟩
  · rcases v with w | z
    · exact harch w
    · exact hl z
  · have hσ : σ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hs
    have hσL : σL < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hs
    have hσB' : σB < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    obtain ⟨_, _, p, pd, h1, h3, hΛp, hΛpd⟩ := hprod s hσ
    have hBl : ∀ z ∈ B, l z s ≠ 0 := fun z hz => (hσv z s (lt_of_le_of_lt (hσB z hz) hσB')).1
    have hBd : ∀ z ∈ B, d z s ≠ 0 := fun z hz => (hσv z s (lt_of_le_of_lt (hσB z hz) hσB')).2
    have hlB := hasProd_compl_of_ne_zero h1 B hBl
    have hdB := hasProd_compl_of_ne_zero h3 B hBd
    have hval : Λ s * (Linf s)⁻¹ = p := by
      rw [hΛp, mul_comm (Linf s) p, mul_assoc, mul_inv_cancel₀ (hLne s hσL).1, mul_one]
    have hvald : Λd s * (Ldinf s)⁻¹ = pd := by
      rw [hΛpd, mul_comm (Ldinf s) pd, mul_assoc, mul_inv_cancel₀ (hLne s hσL).2, mul_one]
    rw [← hval] at hlB
    rw [← hvald] at hdB
    exact ⟨(complDisjSumEquiv (I := I) B).hasProd_iff.mp hlB,
      (complDisjSumEquiv (I := I) B).hasProd_iff.mp hdB⟩
  · show MeromorphicEq
      (fun s ↦ (Λ s * (Linf s)⁻¹ * (∏ z ∈ B, l z s)⁻¹) *
        ∏ v ∈ (Finset.univ : Finset I).disjSum B,
          (Sum.elim arch (fun v => (⟨l v, d v, e v⟩ : LocalFactors)) v).lFactor s)
      (fun s ↦ (∏ v ∈ (Finset.univ : Finset I).disjSum B,
          (Sum.elim arch (fun v => (⟨l v, d v, e v⟩ : LocalFactors)) v).epsilonFactor s) *
        ((Λd (1 - s) * (Ldinf (1 - s))⁻¹ * (∏ z ∈ B, d z (1 - s))⁻¹) *
          ∏ v ∈ (Finset.univ : Finset I).disjSum B,
            (Sum.elim arch (fun v => (⟨l v, d v, e v⟩ : LocalFactors)) v).dualLFactor (1 - s)))
    simp only [Finset.prod_disjSum, Sum.elim_inl, Sum.elim_inr, hA, hAd, hAe]
    have hL1 : MeromorphicEq
        (fun s => Λ s * (Linf s)⁻¹ * (∏ z ∈ B, l z s)⁻¹ * (Linf s * ∏ z ∈ B, l z s)) Λ := by
      intro z
      filter_upwards [hLnm.eventually_ne_zero z, hPB.eventually_ne_zero z] with s h1 h2
      field_simp
    have hR1 : MeromorphicEq
        (fun s => εinf s * (∏ z ∈ B, e z s) *
          (Λd (1 - s) * (Ldinf (1 - s))⁻¹ * (∏ z ∈ B, d z (1 - s))⁻¹ *
            (Ldinf (1 - s) * ∏ z ∈ B, d z (1 - s))))
        (fun s => εinf s * (∏ z ∈ B, e z s) * Λd (1 - s)) := by
      intro z
      filter_upwards [hLdnm.reflect.eventually_ne_zero z, hPBd.reflect.eventually_ne_zero z]
        with s h1 h2
      field_simp
    have hprodS : ∀ s, ∏ v ∈ S, e v s = ∏ v ∈ B, e v s := fun s =>
      Finset.prod_subset hSB fun v hvB hvS => he1 v hvB hvS s
    have hmid : MeromorphicEq Λ (fun s => εinf s * (∏ z ∈ B, e z s) * Λd (1 - s)) := by
      refine (meromorphicEq_of_codiscrete hfe).trans (meromorphicEq_of_eq fun s => ?_)
      rw [hprodS]
      ring
    exact hL1.trans (hmid.trans hR1.symm)

end CompletedEquationAdapter

end Langlands.Global.FunctionalEquationComparison
