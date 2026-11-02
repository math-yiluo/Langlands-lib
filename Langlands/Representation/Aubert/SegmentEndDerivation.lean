import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentInitialTruncation
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Data.Finsupp.Weight

/-!
# End derivations of the segment polynomial ring

For a cuspidal datum `ρ`, the end derivation `D_ρ` of `ℤ[X_Δ]` removes the end
`ρ` of a segment: `D_ρ X_Δ = X_{Δ⁻}` when `Δ = [ν^(1-m) ρ, ρ]` with `m ≥ 2` and
`Δ⁻ = [ν^(1-m) ρ, ν^(-1) ρ]`, `D_ρ X_Δ = 1` when `Δ = [ρ]`, and `D_ρ X_Δ = 0` when
`Δ` does not end with `ρ`. A polynomial killed by every end derivation is
constant. Consequently a ring homomorphism `φ` out of `ℤ[X_Δ]` is injective when
the unit of its target has infinite additive order and some ring homomorphism
`E` into a group algebra over the target expands each `φ X_Δ` as
`φ X_Δ + φ (D_{end Δ} X_Δ) e^{end Δ}`.
-/

noncomputable section

open MvPolynomial

namespace Langlands.Aubert.SegmentEndDerivation

open PadicField.TopologicalData.Segment
  (dropLastNonempty dropLastNonempty_base dropLastNonempty_length)

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Segments are determined by their beginning and their length. -/
theorem segment_ext {Δ Δ' : T.Segment.{uV, uF}} (hb : Δ.base = Δ'.base)
    (hl : Δ.length = Δ'.length) : Δ = Δ' := by
  obtain ⟨b, l, hl₀⟩ := Δ
  obtain ⟨b', l', hl₀'⟩ := Δ'
  simp only at hb hl
  subst hb
  subst hl
  rfl

/-- Segments are determined by their end and their length. -/
theorem segment_ext_last {Δ Δ' : T.Segment.{uV, uF}} (he : Δ.last = Δ'.last)
    (hl : Δ.length = Δ'.length) : Δ = Δ' := by
  refine segment_ext ?_ hl
  have h := congrArg (PadicField.TopologicalData.CuspidalDatum.twist
    (-((Δ.length - 1 : ℕ) : ℝ))) he
  simp only [PadicField.TopologicalData.Segment.last,
    PadicField.TopologicalData.Segment.member,
    PadicField.TopologicalData.CuspidalDatum.twist_twist, hl, neg_add_cancel,
    PadicField.TopologicalData.CuspidalDatum.twist_zero] at h
  exact h

/-- The end of `Δ⁻` is `ν^(-1)` times the end of `Δ`. -/
theorem last_shorten (Δ : T.Segment.{uV, uF}) (h : 1 < Δ.length) :
    (dropLastNonempty Δ h).last = Δ.last.twist (-1) := by
  simp only [PadicField.TopologicalData.Segment.last,
    PadicField.TopologicalData.Segment.member, dropLastNonempty_length, dropLastNonempty_base,
    PadicField.TopologicalData.CuspidalDatum.twist_twist]
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The value of an end derivation on the variable of `Δ` when `Δ` ends with the
derivation's datum: the variable of `Δ⁻` when `Δ` has at least two elements, and
`1` otherwise. -/
def endTail (Δ : T.Segment.{uV, uF}) : MvPolynomial T.Segment.{uV, uF} ℤ :=
  if h : 1 < Δ.length then X (dropLastNonempty Δ h) else 1

open Classical in
/-- The end derivation `D_ρ` of the segment polynomial ring. -/
def endDerivation (ρ : T.CuspidalDatum.{uV, uF}) :
    Derivation ℤ (MvPolynomial T.Segment.{uV, uF} ℤ) (MvPolynomial T.Segment.{uV, uF} ℤ) :=
  mkDerivation ℤ fun Δ => if Δ.last = ρ then endTail Δ else 0

theorem endDerivation_X_of_ne {ρ : T.CuspidalDatum.{uV, uF}} {Δ : T.Segment.{uV, uF}}
    (h : Δ.last ≠ ρ) : endDerivation ρ (X Δ) = 0 := by
  rw [endDerivation, mkDerivation_X, ite_eq_right h]

theorem endDerivation_X_of_eq {ρ : T.CuspidalDatum.{uV, uF}} {Δ : T.Segment.{uV, uF}}
    (h : Δ.last = ρ) : endDerivation ρ (X Δ) = endTail Δ := by
  rw [endDerivation, mkDerivation_X, ite_eq_left h]

theorem endDerivation_X (ρ : T.CuspidalDatum.{uV, uF}) (Δ : T.Segment.{uV, uF}) [Decidable (Δ.last = ρ)] :
    endDerivation ρ (X Δ) = if Δ.last = ρ then endTail Δ else 0 := by
  split_ifs with h
  exacts [endDerivation_X_of_eq h, endDerivation_X_of_ne h]

theorem endTail_of_length_eq_one {Δ : T.Segment.{uV, uF}} (h : Δ.length = 1) :
    endTail Δ = 1 := by
  rw [endTail, dite_eq_right (by omega)]

theorem endTail_of_one_lt {Δ : T.Segment.{uV, uF}} (h : 1 < Δ.length) :
    endTail Δ = X (dropLastNonempty Δ h) := by
  rw [endTail, dite_eq_left h]

/-! ### The length filtration -/

/-- The length weight of a monomial: the sum of the lengths of its segments. -/
def lengthWeight : (T.Segment.{uV, uF} →₀ ℕ) →+ ℕ :=
  Finsupp.weight fun Δ : T.Segment.{uV, uF} => Δ.length

theorem lengthWeight_single (Δ : T.Segment.{uV, uF}) (k : ℕ) :
    lengthWeight (Finsupp.single Δ k) = k * Δ.length := by
  rw [lengthWeight, Finsupp.weight_single, smul_eq_mul]

theorem lengthWeight_sub_single_add {d : T.Segment.{uV, uF} →₀ ℕ} {Δ : T.Segment.{uV, uF}}
    (hΔ : Δ ∈ d.support) :
    lengthWeight (d - Finsupp.single Δ 1) + Δ.length = lengthWeight d := by
  have hle : Finsupp.single Δ 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hΔ))
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, lengthWeight_single, one_mul]

/-- Polynomials all of whose monomials have length weight below `n`. -/
def lowWeight (n : ℕ) : Submodule ℤ (MvPolynomial T.Segment.{uV, uF} ℤ) where
  carrier := {q | ∀ d ∈ q.support, lengthWeight d < n}
  add_mem' := by
    classical
    intro a b ha hb d hd
    rcases Finset.mem_union.mp (support_add hd) with h | h
    exacts [ha d h, hb d h]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha d hd
    exact ha d (support_smul hd)

theorem mem_lowWeight {n : ℕ} {q : MvPolynomial T.Segment.{uV, uF} ℤ} :
    q ∈ lowWeight n ↔ ∀ d ∈ q.support, lengthWeight d < n := Iff.rfl

theorem monomial_mem_lowWeight {n : ℕ} {d : T.Segment.{uV, uF} →₀ ℕ} (hd : lengthWeight d < n)
    (c : ℤ) : monomial d c ∈ lowWeight n := by
  intro e he
  rw [Finset.mem_singleton.mp (support_monomial_subset he)]
  exact hd

theorem mem_lowWeight_sup (q : MvPolynomial T.Segment.{uV, uF} ℤ) :
    q ∈ lowWeight (q.support.sup lengthWeight + 1) := fun _ hd =>
  Nat.lt_succ_of_le (Finset.le_sup hd)

theorem eq_zero_of_mem_lowWeight_zero {q : MvPolynomial T.Segment.{uV, uF} ℤ}
    (hq : q ∈ lowWeight 0) : q = 0 :=
  support_eq_empty.mp (Finset.eq_empty_of_forall_notMem fun d hd => Nat.not_lt_zero _ (hq d hd))

/-- An end derivation lowers the length weight by one. -/
theorem endDerivation_mem_lowWeight (ρ : T.CuspidalDatum.{uV, uF}) {n : ℕ}
    {q : MvPolynomial T.Segment.{uV, uF} ℤ} (hq : q ∈ lowWeight (n + 1)) :
    endDerivation ρ q ∈ lowWeight n := by
  classical
  rw [q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : lengthWeight d < n + 1 := hq d hd
  rw [endDerivation, mkDerivation_monomial, Finsupp.sum]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun Δ hΔ => ?_)
  have hsub := lengthWeight_sub_single_add hΔ
  have hpos := Δ.length_pos
  by_cases hb : Δ.last = ρ
  · rw [ite_eq_left hb, endTail]
    split_ifs with hl
    · rw [smul_eq_mul, X, monomial_mul_monomial, mul_one]
      refine monomial_mem_lowWeight ?_ _
      rw [map_add, lengthWeight_single, one_mul, dropLastNonempty_length]
      omega
    · rw [smul_eq_mul, mul_one]
      exact monomial_mem_lowWeight (by omega) _
  · rw [ite_eq_right hb, smul_zero]
    exact Submodule.zero_mem _

/-! ### Polynomials killed by every end derivation -/

/-- In a nonempty finite set of cuspidal data, some member has its `ν^(-1)`-twist
outside the set: integral twists act freely. -/
theorem exists_twist_neg_one_notMem (B : Finset T.CuspidalDatum.{uV, uF}) (hB : B.Nonempty) :
    ∃ ρ ∈ B, ρ.twist (-1) ∉ B := by
  by_contra! h
  obtain ⟨ρ₀, hρ₀⟩ := hB
  have hmem : ∀ n : ℕ, ρ₀.twist (-(n : ℝ)) ∈ (B : Set T.CuspidalDatum.{uV, uF}) := by
    intro n
    induction n with
    | zero => simpa using hρ₀
    | succ n ih =>
      have := h _ ih
      rwa [PadicField.TopologicalData.CuspidalDatum.twist_twist, ← neg_add, add_comm,
        ← Nat.cast_add_one] at this
  have hinj : Function.Injective fun n : ℕ => ρ₀.twist (-(n : ℝ)) := by
    intro a b hab
    simp only at hab
    wlog hle : a ≤ b generalizing a b
    · exact (this hab.symm (le_of_not_ge hle)).symm
    have key : (ρ₀.twist (-(b : ℝ))).twist (((b - a : ℕ) : ℤ) : ℝ) = ρ₀.twist (-(b : ℝ)) := by
      rw [PadicField.TopologicalData.CuspidalDatum.twist_twist, ← hab]
      congr 1
      push_cast [Nat.cast_sub hle]
      ring
    have hk := (Classification.cuspidalIntegralTwistFreeness.{uF, uV} F T _ _).mp key
    omega
  exact Set.infinite_of_injective_forall_mem hinj hmem B.finite_toSet

/-- A variable whose partial derivative vanishes does not occur. -/
theorem notMem_vars_of_pderiv_eq_zero {σ : Type*} {q : MvPolynomial σ ℤ} {i : σ}
    (h : pderiv i q = 0) : i ∉ q.vars := by
  classical
  intro hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp hi
  have hle : Finsupp.single i 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hid))
  have hc := coeff_pderiv (i := i) q (d - Finsupp.single i 1)
  rw [h, tsub_add_cancel_of_le hle] at hc
  have h0 : (0 : MvPolynomial σ ℤ).coeff (d - Finsupp.single i 1) = 0 := by simp
  rw [h0] at hc
  have hne : (((d - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : ℤ) + 1 ≠ 0 := by positivity
  exact mem_support_iff.mp hd (mul_eq_zero.mp hc.symm |>.resolve_right hne)

/-- Extraction of a derivation from `D` on polynomials supported on `s`, through an
additive map `L` that is linear over polynomials supported on `s`. -/
theorem extract_eq {σ : Type*}
    (D K : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (L : MvPolynomial σ ℤ →+ MvPolynomial σ ℤ) (s : Set σ)
    (hL : ∀ x ∈ supported ℤ s, ∀ z, L (x * z) = x * L z)
    (hgen : ∀ i ∈ s, L (D (X i)) = K (X i)) {x : MvPolynomial σ ℤ}
    (hx : x ∈ supported ℤ s) : L (D x) = K x := by
  rw [supported_eq_adjoin_X] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact hgen i hi
  | algebraMap c => simp
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy, map_add]
  | mul x y hx hy ihx ihy =>
    rw [Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, hL x hx, hL y hy, ihx, ihy]

/-- A polynomial killed by every end derivation is constant. -/
theorem eq_C_of_endDerivation_eq_zero (q : MvPolynomial T.Segment.{uV, uF} ℤ)
    (hq : ∀ ρ, endDerivation ρ q = 0) : q = C (q.coeff 0) := by
  classical
  rw [← vars_eq_empty_iff_eq_C]
  by_contra hne
  obtain ⟨ρ, hρB, hρ1⟩ := exists_twist_neg_one_notMem (F := F) (T := T)
    (q.vars.image fun Δ => Δ.last) (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hne))
  obtain ⟨Δ₀, hΔ₀, rfl⟩ := Finset.mem_image.mp hρB
  set s : Set T.Segment.{uV, uF} := {Δ | Δ.last ≠ Δ₀.last.twist (-1)} with hs
  have hsupp : q ∈ supported ℤ s := by
    rw [mem_supported]
    intro Δ hΔ h
    exact hρ1 (Finset.mem_image.mpr ⟨Δ, hΔ, h⟩)
  have hD := hq Δ₀.last
  -- Variables other than `Δ₀` have zero `Δ₀`-derivative.
  have hK : ∀ i : T.Segment.{uV, uF}, i ≠ Δ₀ → pderiv Δ₀ (X i : MvPolynomial _ ℤ) = 0 :=
    fun i hi => pderiv_X_of_ne hi
  have hpd : pderiv Δ₀ q = 0 := by
    by_cases hl : Δ₀.length = 1
    · -- Evaluate the variables outside `s` at zero.
      let ε : MvPolynomial T.Segment.{uV, uF} ℤ →+ MvPolynomial T.Segment.{uV, uF} ℤ :=
        (aeval fun i => if i ∈ s then X i else 0 :
          MvPolynomial T.Segment.{uV, uF} ℤ →ₐ[ℤ] MvPolynomial T.Segment.{uV, uF} ℤ)
      have hε : ∀ x ∈ supported ℤ s, ε x = x := fun x hx =>
        aeval_ite_mem_eq_self x (mem_supported.mp hx)
      have key := extract_eq (endDerivation Δ₀.last) (pderiv Δ₀) ε s
        (fun x hx z => by
          change aeval _ (x * z) = x * aeval _ z
          rw [map_mul]
          exact congrArg (· * _) (hε x hx))
        (fun i hi => by
          by_cases hb : i.last = Δ₀.last
          · rw [endDerivation_X_of_eq hb]
            by_cases hi1 : i.length = 1
            · have : i = Δ₀ := segment_ext_last hb (hi1.trans hl.symm)
              subst this
              rw [endTail_of_length_eq_one hi1, pderiv_X_self]
              exact map_one (aeval fun i => if i ∈ s then X i else 0 :
                MvPolynomial T.Segment.{uV, uF} ℤ →ₐ[ℤ] MvPolynomial T.Segment.{uV, uF} ℤ)
            · have hlt : 1 < i.length := by have := i.length_pos; omega
              rw [endTail_of_one_lt hlt, hK i (fun h => hi1 (h ▸ hl))]
              change aeval _ (X _) = 0
              rw [aeval_X, ite_eq_right]
              intro hmem
              exact hmem (by rw [last_shorten, hb])
          · rw [endDerivation_X_of_ne hb, map_zero, hK i (fun h => hb (h ▸ rfl))])
        hsupp
      rw [← key, hD, map_zero]
    · have hlt : 1 < Δ₀.length := by have := Δ₀.length_pos; omega
      have key := extract_eq (endDerivation Δ₀.last) (pderiv Δ₀)
        (pderiv (dropLastNonempty Δ₀ hlt)).toLinearMap.toAddMonoidHom s
        (fun x hx z => by
          change pderiv _ (x * z) = x * pderiv _ z
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
            pderiv_eq_zero_of_notMem_vars (fun hv => mem_supported.mp hx hv
              (last_shorten Δ₀ hlt)), mul_zero, add_zero])
        (fun i hi => by
          change pderiv _ (endDerivation Δ₀.last (X i)) = pderiv Δ₀ (X i)
          by_cases hb : i.last = Δ₀.last
          · rw [endDerivation_X_of_eq hb]
            by_cases hi1 : i.length = 1
            · rw [endTail_of_length_eq_one hi1, pderiv_one,
                hK i (fun h => hl (h ▸ hi1))]
            · have hlt' : 1 < i.length := by have := i.length_pos; omega
              rw [endTail_of_one_lt hlt']
              by_cases hiΔ : i = Δ₀
              · subst hiΔ
                rw [pderiv_X_self, pderiv_X_self]
              · rw [hK i hiΔ, pderiv_X_of_ne]
                intro h
                apply hiΔ
                refine segment_ext ?_ ?_
                · simpa using congrArg (fun Δ : T.Segment.{uV, uF} => Δ.base) h
                · have := congrArg (fun Δ : T.Segment.{uV, uF} => Δ.length) h
                  simp only [dropLastNonempty_length] at this
                  omega
          · rw [endDerivation_X_of_ne hb, map_zero, hK i (fun h => hb (h ▸ rfl))])
        hsupp
      rw [← key, hD, map_zero]
  exact notMem_vars_of_pderiv_eq_zero hpd hΔ₀

/-! ### Injectivity -/

/-- A ring homomorphism out of the segment polynomial ring is injective when its
kernel is stable under every end derivation and the unit of its target has
infinite additive order. -/
theorem injective_of_ker_stable {A : Type*} [CommRing A]
    (φ : MvPolynomial T.Segment.{uV, uF} ℤ →+* A)
    (hφ : ∀ ρ q, φ q = 0 → φ (endDerivation ρ q) = 0)
    (hA : ∀ c : ℤ, (c : A) = 0 → c = 0) : Function.Injective φ := by
  have key : ∀ n : ℕ, ∀ q ∈ lowWeight.{uF, uV} (T := T) n, φ q = 0 → q = 0 := by
    intro n
    induction n with
    | zero => exact fun q hq _ => eq_zero_of_mem_lowWeight_zero hq
    | succ n ih =>
      intro q hq h0
      have hD : ∀ ρ, endDerivation ρ q = 0 := fun ρ =>
        ih _ (endDerivation_mem_lowWeight ρ hq) (hφ ρ q h0)
      have hC := eq_C_of_endDerivation_eq_zero q hD
      have hcast : φ (C (q.coeff 0)) = ((q.coeff 0 : ℤ) : A) := by
        simp
      rw [hC, hcast] at h0
      rw [hC, hA _ h0, map_zero]
  exact (injective_iff_map_eq_zero φ).mpr fun q hq => key _ q (mem_lowWeight_sup q) hq

/-! ### The end expansion -/

/-- The polynomial end expansion `X_Δ ↦ X_Δ + D_{end Δ}(X_Δ) e^{end Δ}`, with values
in the monoid algebra of the free commutative monoid on the cuspidal data. -/
def endExpansion :
    MvPolynomial T.Segment.{uV, uF} ℤ →+*
      AddMonoidAlgebra (MvPolynomial T.Segment.{uV, uF} ℤ) (T.CuspidalDatum.{uV, uF} →₀ ℕ) :=
  eval₂Hom (Int.castRingHom _) fun Δ =>
    AddMonoidAlgebra.single 0 (X Δ) + AddMonoidAlgebra.single (Finsupp.single Δ.last 1) (endTail Δ)

theorem endExpansion_X (Δ : T.Segment.{uV, uF}) :
    endExpansion (X Δ) =
      AddMonoidAlgebra.single 0 (X Δ) +
        AddMonoidAlgebra.single (Finsupp.single Δ.last 1) (endTail Δ) :=
  eval₂Hom_X' _ _ _

/-- The degree-zero part of the end expansion is the polynomial itself, and the
part of degree `e^ρ` is its end derivation `D_ρ`. -/
theorem coeff_endExpansion (q : MvPolynomial T.Segment.{uV, uF} ℤ) :
    (endExpansion q).coeff 0 = q ∧
      ∀ ρ, (endExpansion q).coeff (Finsupp.single ρ 1) = endDerivation ρ q := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a =>
    have h : endExpansion (C a : MvPolynomial T.Segment.{uV, uF} ℤ) =
        AddMonoidAlgebra.single 0 (C a) := by
      rw [eq_intCast (C : ℤ →+* MvPolynomial T.Segment.{uV, uF} ℤ) a, map_intCast,
        AddMonoidAlgebra.intCast_def]
    refine ⟨by rw [h, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same], fun ρ => ?_⟩
    rw [h, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne, derivation_C]
    exact (Finsupp.single_ne_zero.mpr one_ne_zero)
  | add q q' ihq ihq' =>
    refine ⟨by rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihq.1, ihq'.1],
      fun ρ => ?_⟩
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ihq.2, ihq'.2, map_add]
  | mul_X q Δ ih =>
    have he : Finsupp.single Δ.last 1 ≠ (0 : T.CuspidalDatum.{uV, uF} →₀ ℕ) :=
      Finsupp.single_ne_zero.mpr one_ne_zero
    rw [map_mul, endExpansion_X, mul_add]
    refine ⟨?_, fun ρ => ?_⟩
    · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        AddMonoidAlgebra.coeff_mul_single_zero, ih.1,
        AddMonoidAlgebra.coeff_mul_single_of_forall_add_ne, add_zero]
      intro d hd
      exact he (add_eq_zero.mp hd).2
    · rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        AddMonoidAlgebra.coeff_mul_single_zero, ih.2, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, endDerivation_X]
      by_cases hρ : Δ.last = ρ
      · subst hρ
        rw [AddMonoidAlgebra.coeff_mul_single_eq_coeff_mul 0, ih.1, ite_eq_left rfl]
        · ring
        · intro d _
          constructor
          · intro hd
            simpa using hd
          · rintro rfl
            exact zero_add _
      · rw [AddMonoidAlgebra.coeff_mul_single_of_forall_add_ne, ite_eq_right hρ]
        · ring
        · intro d hd
          have := congrArg (fun f : T.CuspidalDatum.{uV, uF} →₀ ℕ => f Δ.last) hd
          simp [hρ] at this

/-- The inclusion of the free commutative monoid on the cuspidal data into the
free abelian group. -/
def cuspidalMonoidInclusion :
    (T.CuspidalDatum.{uV, uF} →₀ ℕ) →+ (T.CuspidalDatum.{uV, uF} →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem cuspidalMonoidInclusion_injective :
    Function.Injective (cuspidalMonoidInclusion (T := T)) :=
  Finsupp.mapRange_injective _ (Nat.cast_zero) Nat.cast_injective

theorem cuspidalMonoidInclusion_single (ρ : T.CuspidalDatum.{uV, uF}) (k : ℕ) :
    cuspidalMonoidInclusion (Finsupp.single ρ k) = Finsupp.single ρ (k : ℤ) := by
  simp [cuspidalMonoidInclusion]

/-- **Injectivity criterion.** A ring homomorphism `φ` out of the segment
polynomial ring is injective when the unit of its target has infinite additive
order and some ring homomorphism `E` from the target to its group algebra over
`CuspidalDatum →₀ ℤ` sends each `φ X_Δ` to `φ X_Δ + φ (D_{end Δ} X_Δ) e^{end Δ}`. -/
theorem injective_of_endExpansion {A : Type*} [CommRing A]
    (φ : MvPolynomial T.Segment.{uV, uF} ℤ →+* A)
    (E : A →+* AddMonoidAlgebra A (T.CuspidalDatum.{uV, uF} →₀ ℤ))
    (hE : ∀ Δ, E (φ (X Δ)) =
      AddMonoidAlgebra.single 0 (φ (X Δ)) +
        AddMonoidAlgebra.single (Finsupp.single Δ.last 1) (φ (endTail Δ)))
    (hA : ∀ c : ℤ, (c : A) = 0 → c = 0) : Function.Injective φ := by
  let Φ : AddMonoidAlgebra (MvPolynomial T.Segment.{uV, uF} ℤ) (T.CuspidalDatum.{uV, uF} →₀ ℕ) →+*
      AddMonoidAlgebra A (T.CuspidalDatum.{uV, uF} →₀ ℤ) :=
    (AddMonoidAlgebra.mapDomainRingHom A cuspidalMonoidInclusion).comp
      (AddMonoidAlgebra.mapRingHom _ φ)
  have hΦ : Φ.comp endExpansion = E.comp φ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun Δ => ?_)
    · simp only [RingHom.comp_apply]
      simp only [eq_intCast (C : ℤ →+* MvPolynomial T.Segment.{uV, uF} ℤ) a, map_intCast]
    · simp only [RingHom.comp_apply]
      rw [endExpansion_X, hE, map_add]
      simp [Φ, AddMonoidAlgebra.mapRingHom_single, cuspidalMonoidInclusion_single]
  have hcoeff : ∀ y m, (Φ y).coeff (cuspidalMonoidInclusion m) = φ (y.coeff m) := by
    intro y m
    simp only [Φ, RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.coeff_mapDomain]
    rw [Finsupp.mapDomain_apply_of_injective cuspidalMonoidInclusion_injective]
    exact AddMonoidAlgebra.coeff_mapRingHom _ _ _
  refine injective_of_ker_stable φ (fun ρ q hq => ?_) hA
  have h := hcoeff (endExpansion q) (Finsupp.single ρ 1)
  rw [(coeff_endExpansion q).2 ρ, ← RingHom.comp_apply Φ, hΦ, RingHom.comp_apply, hq,
    map_zero] at h
  exact h.symm

end Langlands.Aubert.SegmentEndDerivation
