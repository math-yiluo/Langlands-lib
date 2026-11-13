import Langlands.Representation.Whittaker.MirabolicFiniteLengthCharacters
import Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology
/-!
# Locally constant additive characters of a nonarchimedean local field

Every locally constant character of the additive group of a nonarchimedean local
field `F`, with the topology and lattices of the supplied data `T`, is
`x ↦ ψ(a x)` for one fixed locally constant `ψ`, and every locally constant
character of `F^n` is `v ↦ ψ(a ⬝ᵥ v)`. A nonzero row can be moved to the last
coordinate row by an invertible matrix. These are inputs of the mirabolic
finite-length proof.
-/

noncomputable section

open scoped WithZero
open Multiplicative Matrix

namespace Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker.MirabolicFiniteLength hiding additiveLattice_mul_mem div_mem_additiveLattice exists_dotProduct_eq exists_exact_conductor exists_generating_character exists_mem_additiveLattice exists_mul_eq exists_mul_eq_on_additiveLattice exists_trivial_additiveLattice finite_quotient_additiveLattice mem_additiveLattice_of_forall_mul
open Langlands.AllField.Whittaker.MirabolicFiniteLength
open Langlands.Whittaker
open Langlands.AllField.Whittaker

universe uF uK

section Lattices

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- Valuation lattices multiply additively in their indices. -/
theorem additiveLattice_mul_mem {j k : ℤ} {x y : F}
    (hx : x ∈ T.additiveLattice j) (hy : y ∈ T.additiveLattice k) :
    x * y ∈ T.additiveLattice (j + k) := by
  rw [Langlands.LocalFieldData.mem_additiveLattice] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

/-- Every element lies in some valuation lattice. -/
theorem exists_mem_additiveLattice (x : F) :
    ∃ n : ℤ, x ∈ T.additiveLattice n := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (T.additiveLattice 0).zero_mem⟩
  · refine ⟨WithZero.log (T.discreteValuation x), ?_⟩
    rw [Langlands.LocalFieldData.mem_additiveLattice,
      WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr hx)]

/-- Division by an element outside `L j` moves `L (c + 1)` into `L (c - j)`. -/
theorem div_mem_additiveLattice {c j : ℤ} {x z : F}
    (hx : x ∈ T.additiveLattice (c + 1)) (hz : z ∉ T.additiveLattice j) :
    x / z ∈ T.additiveLattice (c - j) := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ (T.additiveLattice j).zero_mem)
  have h1 : (1 : F) ∉ T.additiveLattice (j + T.ord z) := by
    rw [← T.mul_mem_additiveLattice_iff hz0, mul_one]
    exact hz
  have hord : j + T.ord z < 0 := by
    by_contra h
    push Not at h
    apply h1
    rw [Langlands.LocalFieldData.mem_additiveLattice, map_one, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr h
  have hxz : x / z ∈ T.additiveLattice (c + 1 + T.ord z) := by
    rw [← T.mul_mem_additiveLattice_iff hz0, mul_div_cancel₀ _ hz0]
    exact hx
  exact T.additiveLattice_mono (by omega) hxz

/-- A locally constant character is trivial on some valuation lattice. -/
theorem exists_trivial_additiveLattice (χ : Multiplicative F →* ℂˣ)
    (hχ : letI := T.topology
      IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) :
    ∃ m : ℤ, ∀ x ∈ T.additiveLattice m, χ (ofAdd x) = 1 := by
  let := T.topology
  have h0 : {x : F | (χ (ofAdd x) : ℂ) = 1} ∈ nhds (0 : F) :=
    (hχ.isOpen_fiber 1).mem_nhds (by simp)
  obtain ⟨m, hm⟩ := T.exists_additiveLattice_subset h0
  exact ⟨m, fun x hx => Units.ext (hm hx)⟩

/-- A nontrivial locally constant character has an exact conductor `t`: it is
trivial on `L t` and nontrivial on `L (t + 1)`. -/
theorem exists_exact_conductor (ψ : Multiplicative F →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)))
    (hne : ψ ≠ 1) :
    ∃ t : ℤ, (∀ x ∈ T.additiveLattice t, ψ (ofAdd x) = 1) ∧
      ∃ x₀ ∈ T.additiveLattice (t + 1), ψ (ofAdd x₀) ≠ 1 := by
  obtain ⟨x₁, hx₁⟩ : ∃ x : F, ψ (ofAdd x) ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext fun x => h (toAdd x))
  obtain ⟨j, hj⟩ := exists_mem_additiveLattice T x₁
  have hbdd : ∃ b : ℤ, ∀ n : ℤ, (∀ x ∈ T.additiveLattice n, ψ (ofAdd x) = 1) → n ≤ b := by
    refine ⟨j, fun n hn => ?_⟩
    by_contra h
    exact hx₁ (hn x₁ (T.additiveLattice_mono (by omega) hj))
  obtain ⟨t, ht, htmax⟩ := Int.exists_greatest_of_bdd hbdd
    (exists_trivial_additiveLattice T ψ hψ)
  refine ⟨t, ht, ?_⟩
  by_contra h
  push Not at h
  have := htmax (t + 1) h
  omega

/-- If `y ↦ ψ (a y)` is trivial on `L k`, then `a ∈ L (t - k)`. -/
theorem mem_additiveLattice_of_forall_mul (ψ : Multiplicative F →* ℂˣ)
    {t k : ℤ} {x₀ : F} (hx₀ : x₀ ∈ T.additiveLattice (t + 1))
    (hψx₀ : ψ (ofAdd x₀) ≠ 1) {a : F}
    (h : ∀ y ∈ T.additiveLattice k, ψ (ofAdd (a * y)) = 1) :
    a ∈ T.additiveLattice (t - k) := by
  by_contra ha
  have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ (T.additiveLattice _).zero_mem)
  have hy : x₀ / a ∈ T.additiveLattice k := by
    have := div_mem_additiveLattice T (c := t) (j := t - k) hx₀ ha
    rwa [sub_sub_cancel] at this
  apply hψx₀
  have := h _ hy
  rwa [mul_div_cancel₀ _ ha0] at this

/-- Quotients of valuation lattices by smaller valuation lattices are finite. -/
theorem finite_quotient_additiveLattice (m k : ℤ) :
    Finite (T.additiveLattice k ⧸ (T.additiveLattice m).addSubgroupOf (T.additiveLattice k)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : CompactSpace (T.additiveLattice k) :=
    isCompact_iff_compactSpace.mp (T.isCompact_additiveLattice k)
  exact AddSubgroup.quotient_finite_of_isOpen _
    (AddSubgroup.addSubgroupOf_isOpen _ _ (T.isOpen_additiveLattice m))

end Lattices

section Pairing

end Pairing

section Classification

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- On each lattice `L k` containing the triviality lattice `L m` of `χ`, the
character `χ` agrees with `y ↦ ψ (a y)` for some `a ∈ L (t - m)`. -/
theorem exists_mul_eq_on_additiveLattice (ψ χ : Multiplicative F →* ℂˣ) {t m k : ℤ}
    (ht : ∀ x ∈ T.additiveLattice t, ψ (ofAdd x) = 1) {x₀ : F}
    (hx₀ : x₀ ∈ T.additiveLattice (t + 1)) (hψx₀ : ψ (ofAdd x₀) ≠ 1)
    (hm : ∀ x ∈ T.additiveLattice m, χ (ofAdd x) = 1) :
    ∃ a ∈ T.additiveLattice (t - m), ∀ x ∈ T.additiveLattice k,
      χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  have := finite_quotient_additiveLattice T (t - k) (t - m)
  have := finite_quotient_additiveLattice T m k
  have hprod : ∀ {i j : ℤ} {a x : F}, a ∈ T.additiveLattice i →
      x ∈ T.additiveLattice j → i + j = t → ψ (ofAdd (a * x)) = 1 := by
    intro i j a x ha hx hij
    apply ht
    rw [← hij]
    exact additiveLattice_mul_mem T ha hx
  let β : T.additiveLattice (t - m) → AddChar (T.additiveLattice k) ℂ := fun a =>
    { toFun := fun x => (ψ (ofAdd (a.val * x.val)) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [mul_add, ofAdd_add] }
  obtain ⟨a, ha⟩ := exists_eq_of_pairing
    ((T.additiveLattice (t - k)).addSubgroupOf (T.additiveLattice (t - m)))
    ((T.additiveLattice m).addSubgroupOf (T.additiveLattice k)) β
    (fun a a' x => by simp [β, add_mul, ofAdd_add])
    (fun a ha x => by
      simp only [β, AddChar.coe_mk]
      rw [hprod (AddSubgroup.mem_addSubgroupOf.mp ha) x.property (by ring)]
      rfl)
    (fun x hx a => by
      simp only [β, AddChar.coe_mk]
      rw [hprod a.property (AddSubgroup.mem_addSubgroupOf.mp hx) (by ring)]
      rfl)
    (fun a h => by
      apply AddSubgroup.mem_addSubgroupOf.mpr
      apply mem_additiveLattice_of_forall_mul T ψ hx₀ hψx₀
      intro y hy
      exact Units.ext (h ⟨y, hy⟩))
    (fun x h => by
      apply AddSubgroup.mem_addSubgroupOf.mpr
      have hx := mem_additiveLattice_of_forall_mul T ψ (k := t - m) hx₀ hψx₀
        (a := x.val) (fun y hy => by
          rw [mul_comm]
          exact Units.ext (h ⟨y, hy⟩))
      rwa [sub_sub_cancel] at hx)
    { toFun := fun x => (χ (ofAdd x.val) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by simp [ofAdd_add] }
    (fun x hx => by
      simp only [AddChar.coe_mk]
      rw [hm x.val (AddSubgroup.mem_addSubgroupOf.mp hx)]
      rfl)
  exact ⟨a.val, a.property, fun x hx => Units.ext (ha ⟨x, hx⟩)⟩

/-- Every locally constant character of `F` is `x ↦ ψ (a x)` for a fixed
nontrivial locally constant `ψ`. -/
theorem exists_mul_eq (ψ χ : Multiplicative F →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)))
    (hψ1 : ψ ≠ 1)
    (hχ : letI := T.topology
      IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) :
    ∃ a : F, ∀ x : F, χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨t, ht, x₀, hx₀, hψx₀⟩ := exists_exact_conductor T ψ hψ hψ1
  obtain ⟨m, hm⟩ := exists_trivial_additiveLattice T χ hχ
  let S : ℕ → Set F := fun i =>
    {a | ∀ x ∈ T.additiveLattice (m + i), χ (ofAdd x) = ψ (ofAdd (a * x))}
  have hSc : ∀ i, IsClosed (S i) := by
    intro i
    have hS : S i = ⋂ x ∈ T.additiveLattice (m + i),
        {a | (ψ (ofAdd (a * x)) : ℂ) = χ (ofAdd x)} := by
      ext a
      simp only [S, Set.mem_iInter, Units.ext_iff, eq_comm]; rfl
    rw [hS]
    exact isClosed_biInter fun x _ =>
      isClosed_eq (hψ.continuous.comp (continuous_id.mul continuous_const)) continuous_const
  obtain ⟨a, -, ha⟩ := (T.isCompact_additiveLattice (t - m)).inter_iInter_nonempty S hSc (by
    intro u
    obtain ⟨a, haL, ha⟩ := exists_mul_eq_on_additiveLattice T ψ χ ht hx₀ hψx₀ hm
      (k := m + ((u.sup id : ℕ) : ℤ))
    refine ⟨a, haL, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi x hx
    have hle : i ≤ u.sup id := Finset.le_sup (f := id) hi
    exact ha x (T.additiveLattice_mono (by omega) hx))
  refine ⟨a, fun x => ?_⟩
  obtain ⟨j, hj⟩ := exists_mem_additiveLattice T x
  exact Set.mem_iInter.mp ha (j - m).toNat x (T.additiveLattice_mono (by omega) hj)

/-- There is a locally constant character `ψ` of `F` such that every locally
constant character is `x ↦ ψ (a x)`. If `F` has no nontrivial locally constant
character, then `ψ = 1` works. -/
theorem exists_generating_character :
    ∃ ψ : Multiplicative F →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ))) ∧
      ∀ χ : Multiplicative F →* ℂˣ,
        (letI := T.topology; IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) →
        ∃ a : F, ∀ x : F, χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  let := T.topology
  by_cases h : ∃ ψ : Multiplicative F →* ℂˣ,
      IsLocallyConstant (fun x : F => (ψ (ofAdd x) : ℂ)) ∧ ψ ≠ 1
  · obtain ⟨ψ, hψ, hψ1⟩ := h
    exact ⟨ψ, hψ, fun χ hχ => exists_mul_eq T ψ χ hψ hψ1 hχ⟩
  · push Not at h
    refine ⟨1, ?_, fun χ hχ => ⟨0, fun x => by rw [h χ hχ]; rfl⟩⟩
    simp only [MonoidHom.one_apply, Units.val_one]
    exact IsLocallyConstant.const 1

/-- With a generating character `ψ`, every locally constant character of `F^n`
is `v ↦ ψ (a ⬝ᵥ v)`. -/
theorem exists_dotProduct_eq (ψ : Multiplicative F →* ℂˣ)
    (hgen : ∀ χ : Multiplicative F →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F => (χ (ofAdd x) : ℂ))) →
      ∃ a : F, ∀ x : F, χ (ofAdd x) = ψ (ofAdd (a * x)))
    {n : ℕ} (χ : Multiplicative (Fin n → F) →* ℂˣ)
    (hχ : letI := T.topology
      IsLocallyConstant (fun v : Fin n → F => (χ (ofAdd v) : ℂ))) :
    ∃ a : Fin n → F, ∀ v : Fin n → F,
      χ (ofAdd v) = ψ (ofAdd (a ⬝ᵥ v)) := by
  let := T.topology
  have hi : ∀ i : Fin n, ∃ a : F, ∀ x : F,
      χ (ofAdd (Pi.single i x)) = ψ (ofAdd (a * x)) := fun i => by
    have hc : Continuous fun x : F => (Pi.single i x : Fin n → F) :=
      continuous_single (A := fun _ : Fin n => F) i
    exact hgen (χ.comp (AddMonoidHom.single (fun _ : Fin n => F) i).toMultiplicative)
      (hχ.comp_continuous hc)
  choose a ha using hi
  refine ⟨a, fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [ofAdd_sum, map_prod]
  simp only [ha, dotProduct, ofAdd_sum, map_prod]

end Classification

section Transitivity

end Transitivity

end Langlands.AllField.Whittaker.MirabolicFiniteLength
