import Langlands.LocalFactor.DeligneHenniartPrimeNormTrace
import Langlands.LocalFactor.DeligneHenniartNormTrace
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Langlands.ClassFieldTheory.Local.NYLL.UniverseZeroModel

/-! # Norm and trace at a prescribed depth -/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open Langlands.LocalClassField

universe u v

variable {p : ℕ} [Fact p.Prime]
variable (K : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
variable [FiniteDimensional K.Carrier L.Carrier]

/-- The trace-lattice and first-order norm congruence for all nonzero elements
above a real input depth, with arbitrary supplied local-field realizations. -/
def NormTraceAtDepth (TK : K.TopologicalData) (TL : L.TopologicalData)
    (r : ℝ) (n : ℕ) : Prop :=
  ∀ y : L.Carrier, y ≠ 0 → r ≤ TL.ord y →
    Algebra.trace K.Carrier L.Carrier y ∈ TK.additiveLattice (-(n : ℤ)) ∧
    ∀ (z : L.Carrierˣ) (t : K.Carrierˣ), (z : L.Carrier) = 1 + y →
      (t : K.Carrier) = 1 + Algebra.trace K.Carrier L.Carrier y →
      Units.map (Algebra.norm K.Carrier) z * t⁻¹ ∈ TK.principalUnits (n + 1)

omit [IsScalarTower (Padic p) K.Carrier L.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] in
/-- Additive trace and norm-remainder bounds imply the multiplicative
first-order congruence, including for every possible choice of its two units. -/
theorem normTraceAtDepth_of_remainder (TK : K.TopologicalData) (TL : L.TopologicalData)
    (r : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ y : L.Carrier, y ≠ 0 → r ≤ TL.ord y →
      Algebra.trace K.Carrier L.Carrier y ∈ TK.additiveLattice (-(n : ℤ)) ∧
      normTraceRemainder K L y ∈ TK.additiveLattice (-((n + 1 : ℕ) : ℤ))) :
    NormTraceAtDepth K L TK TL r n := by
  intro y hy hyr
  obtain ⟨htrace, hrem⟩ := h y hy hyr
  refine ⟨htrace, ?_⟩
  intro z t hz ht
  have htv : TK.discreteValuation (t : K.Carrier) = 1 := by
    rw [ht]
    exact RankOneStability.valuation_one_add TK (by omega) htrace
  let q := Units.map (Algebra.norm K.Carrier) z * t⁻¹
  have hq : (q : K.Carrier) - 1 = normTraceRemainder K L y * (t : K.Carrier)⁻¹ := by
    dsimp only [q]
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change Algebra.norm K.Carrier (z : L.Carrier) * (t : K.Carrier)⁻¹ - 1 = _
    rw [hz, normTraceRemainder]
    have htn : (t : K.Carrier) ≠ 0 := Units.ne_zero t
    field_simp
    linear_combination -ht
  have hval : TK.discreteValuation ((q : K.Carrier) - 1) ≤
      WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    rw [hq, map_mul, map_inv₀, htv, inv_one, mul_one]
    exact hrem
  refine ⟨?_, hval⟩
  have hlt : TK.discreteValuation ((q : K.Carrier) - 1) < 1 :=
    hval.trans_lt (WithZero.exp_lt_one_iff.mpr (by omega))
  have hv := TK.discreteValuation.map_add_eq_of_lt_left
    (x := 1) (y := (q : K.Carrier) - 1) (by simpa using hlt)
  change TK.discreteValuation (q : K.Carrier) = 1
  simpa only [add_sub_cancel, map_one] using hv

omit [IsScalarTower (Padic p) K.Carrier L.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] in
/-- Canonical integral representatives with trace and remainder bounds give the
depth statement for every supplied realization of the same two fields. -/
theorem normTraceAtDepth_of_canonical_ideal_bounds
    (TK : K.TopologicalData) (TL : L.TopologicalData) (m n : ℕ) (hn : 1 ≤ n)
    (h : ∀ x : L.canonicalTopologicalData.Integers,
      x ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m →
      (∃ a : K.canonicalTopologicalData.Integers,
        a ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ n ∧
        (a : K.Carrier) = Algebra.trace K.Carrier L.Carrier (x : L.Carrier)) ∧
      (∃ b : K.canonicalTopologicalData.Integers,
        b ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ (n + 1) ∧
        (b : K.Carrier) = normTraceRemainder K L (x : L.Carrier))) :
    NormTraceAtDepth K L TK TL m n := by
  apply normTraceAtDepth_of_remainder K L TK TL m n hn
  intro y hy hym
  have horder : L.canonicalTopologicalData.ord y = TL.ord y :=
    NYLL.ord_eq_of_algEquiv (AlgEquiv.refl : L.Carrier ≃ₐ[Padic p] L.Carrier)
      TL L.canonicalTopologicalData y
  have hym' : (m : ℤ) ≤ L.canonicalTopologicalData.ord y := by
    rw [horder]
    exact_mod_cast hym
  have hvm : L.canonicalTopologicalData.discreteValuation y ≤
      WithZero.exp (-(m : ℤ)) := by
    rw [discreteValuation_eq_exp_neg_ord _ hy, WithZero.exp_le_exp]
    omega
  have hyI : y ∈ L.canonicalTopologicalData.Integers := by
    apply (L.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one _).mpr
    exact hvm.trans (WithZero.exp_le_one_iff.mpr (by omega))
  let x : L.canonicalTopologicalData.Integers := ⟨y, hyI⟩
  have hxm : x ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ m :=
    (L.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le m x).mpr hvm
  obtain ⟨⟨a, ha, hat⟩, ⟨b, hb, hbt⟩⟩ := h x hxm
  have htransport : ∀ k : ℕ, ∀ c : K.canonicalTopologicalData.Integers,
      c ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ k →
      (c : K.Carrier) ∈ TK.additiveLattice (-(k : ℤ)) := by
    intro k c hc
    have hvaleq : TK.discreteValuation (c : K.Carrier) =
        K.canonicalTopologicalData.discreteValuation (c : K.Carrier) :=
      NYLL.discreteValuation_eq_of_algEquiv
        (AlgEquiv.refl : K.Carrier ≃ₐ[Padic p] K.Carrier)
        K.canonicalTopologicalData TK (c : K.Carrier)
    rw [TK.mem_additiveLattice, hvaleq]
    exact (K.canonicalTopologicalData.mem_maximalIdeal_pow_iff_discreteValuation_le k c).mp hc
  exact ⟨hat ▸ htransport n a ha, hbt ▸ htransport (n + 1) b hb⟩

/-- The prime totally ramified arithmetic bounds give the desired trace and
unit conclusions at depth `t + [L:K] * (n-t)`, in arbitrary realizations. -/
theorem prime_normTrace_atDepth [IsGalois K.Carrier L.Carrier]
    (TK : K.TopologicalData) (TL : L.TopologicalData)
    (hprime : Nat.Prime (Module.finrank K.Carrier L.Carrier))
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank K.Carrier L.Carrier * K.canonicalTopologicalData.ramificationIndex)
    (t : ℕ)
    (hpat : ∀ i : ℕ, Langlands.Ramification.Padic.lowerRamificationGroup
      L.canonicalTopologicalData K.Carrier i = if i ≤ t then ⊤ else ⊥)
    (n : ℕ) (hnt : t < n) :
    NormTraceAtDepth K L TK TL
      (t + Module.finrank K.Carrier L.Carrier * (n - t) : ℕ) n := by
  apply normTraceAtDepth_of_canonical_ideal_bounds K L TK TL _ n (by omega)
  intro x hx
  exact prime_normTrace_ideal_bounds K L hprime htot t hpat n hnt x hx

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
