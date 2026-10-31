import Langlands.HarmonicAnalysis.PadicLatticeTopology
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Group.GL.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Locally constant additive characters of a p-adic field

Every locally constant character of the additive group of a p-adic field is
`x ↦ ψ(a x)` for one fixed locally constant `ψ`, and every locally constant
character of `F^n` is `v ↦ ψ(a ⬝ᵥ v)`. A nonzero row can be moved to the last
coordinate row by an invertible matrix. These are inputs of the mirabolic
finite-length proof.
-/

noncomputable section

open scoped WithZero
open Multiplicative Matrix

namespace Langlands.Whittaker.MirabolicFiniteLength

universe uF uK

section Lattices

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Valuation lattices multiply additively in their indices. -/
theorem additiveLattice_mul_mem {j k : ℤ} {x y : F.Carrier}
    (hx : x ∈ T.additiveLattice j) (hy : y ∈ T.additiveLattice k) :
    x * y ∈ T.additiveLattice (j + k) := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

/-- Every element lies in some valuation lattice. -/
theorem exists_mem_additiveLattice (x : F.Carrier) :
    ∃ n : ℤ, x ∈ T.additiveLattice n := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (T.additiveLattice 0).zero_mem⟩
  · refine ⟨WithZero.log (T.discreteValuation x), ?_⟩
    rw [PadicField.TopologicalData.mem_additiveLattice,
      WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr hx)]

/-- Division by an element outside `L j` moves `L (c + 1)` into `L (c - j)`. -/
theorem div_mem_additiveLattice {c j : ℤ} {x z : F.Carrier}
    (hx : x ∈ T.additiveLattice (c + 1)) (hz : z ∉ T.additiveLattice j) :
    x / z ∈ T.additiveLattice (c - j) := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ (T.additiveLattice j).zero_mem)
  have h1 : (1 : F.Carrier) ∉ T.additiveLattice (j + T.ord z) := by
    rw [← T.mul_mem_additiveLattice_iff hz0, mul_one]
    exact hz
  have hord : j + T.ord z < 0 := by
    by_contra h
    push Not at h
    apply h1
    rw [PadicField.TopologicalData.mem_additiveLattice, map_one, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr h
  have hxz : x / z ∈ T.additiveLattice (c + 1 + T.ord z) := by
    rw [← T.mul_mem_additiveLattice_iff hz0, mul_div_cancel₀ _ hz0]
    exact hx
  exact T.additiveLattice_mono (by omega) hxz

/-- A locally constant character is trivial on some valuation lattice. -/
theorem exists_trivial_additiveLattice (χ : Multiplicative F.Carrier →* ℂˣ)
    (hχ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) :
    ∃ m : ℤ, ∀ x ∈ T.additiveLattice m, χ (ofAdd x) = 1 := by
  let := T.topology
  have h0 : {x : F.Carrier | (χ (ofAdd x) : ℂ) = 1} ∈ nhds (0 : F.Carrier) :=
    (hχ.isOpen_fiber 1).mem_nhds (by simp)
  obtain ⟨m, hm⟩ := T.exists_additiveLattice_subset h0
  exact ⟨m, fun x hx => Units.ext (hm hx)⟩

/-- A nontrivial locally constant character has an exact conductor `t`: it is
trivial on `L t` and nontrivial on `L (t + 1)`. -/
theorem exists_exact_conductor (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)))
    (hne : ψ ≠ 1) :
    ∃ t : ℤ, (∀ x ∈ T.additiveLattice t, ψ (ofAdd x) = 1) ∧
      ∃ x₀ ∈ T.additiveLattice (t + 1), ψ (ofAdd x₀) ≠ 1 := by
  obtain ⟨x₁, hx₁⟩ : ∃ x : F.Carrier, ψ (ofAdd x) ≠ 1 := by
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
theorem mem_additiveLattice_of_forall_mul (ψ : Multiplicative F.Carrier →* ℂˣ)
    {t k : ℤ} {x₀ : F.Carrier} (hx₀ : x₀ ∈ T.additiveLattice (t + 1))
    (hψx₀ : ψ (ofAdd x₀) ≠ 1) {a : F.Carrier}
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

/-- Descend an additive character trivial on a subgroup to the quotient. -/
private def descendChar {Y : Type*} [AddCommGroup Y] (Y₀ : AddSubgroup Y) (φ : AddChar Y ℂ)
    (h : ∀ y ∈ Y₀, φ y = 1) : AddChar (Y ⧸ Y₀) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift Y₀ φ.toAddMonoidHom fun y hy =>
      (AddMonoidHom.mem_ker).mpr (by simp [h y hy]))

private theorem descendChar_mk {Y : Type*} [AddCommGroup Y] (Y₀ : AddSubgroup Y)
    (φ : AddChar Y ℂ) (h : ∀ y ∈ Y₀, φ y = 1) (y : Y) :
    descendChar Y₀ φ h (y : Y ⧸ Y₀) = φ y := rfl

private theorem natCard_addChar (α : Type*) [AddCommGroup α] [Finite α] :
    Nat.card (AddChar α ℂ) = Nat.card α := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

/-- A pairing of finite quotient groups that is nondegenerate on both sides
realizes every character of the second quotient. -/
theorem exists_eq_of_pairing {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (X₀ : AddSubgroup X) (Y₀ : AddSubgroup Y) [Finite (X ⧸ X₀)] [Finite (Y ⧸ Y₀)]
    (β : X → AddChar Y ℂ) (hβ : ∀ x x' y, β (x + x') y = β x y * β x' y)
    (hX₀ : ∀ x ∈ X₀, ∀ y, β x y = 1) (hY₀ : ∀ y ∈ Y₀, ∀ x, β x y = 1)
    (hXnd : ∀ x, (∀ y, β x y = 1) → x ∈ X₀) (hYnd : ∀ y, (∀ x, β x y = 1) → y ∈ Y₀)
    (χ : AddChar Y ℂ) (hχ : ∀ y ∈ Y₀, χ y = 1) :
    ∃ x, ∀ y, χ y = β x y := by
  classical
  have hβneg : ∀ x y, β x y * β (-x) y = 1 := by
    intro x y
    rw [← hβ, add_neg_cancel]
    exact hX₀ 0 X₀.zero_mem y
  -- the pairing as a map into characters of `Y ⧸ Y₀`
  let Φ₀ : X →+ AddChar (Y ⧸ Y₀) ℂ :=
    { toFun := fun x => descendChar Y₀ (β x) fun y hy => hY₀ y hy x
      map_zero' := by
        ext y
        induction y using QuotientAddGroup.induction_on with
        | H y => exact hX₀ 0 X₀.zero_mem y
      map_add' := by
        intro x x'
        ext y
        induction y using QuotientAddGroup.induction_on with
        | H y => exact hβ x x' y }
  let Φ : X ⧸ X₀ →+ AddChar (Y ⧸ Y₀) ℂ := QuotientAddGroup.lift X₀ Φ₀ fun x hx => by
    ext y
    induction y using QuotientAddGroup.induction_on with
    | H y => exact hX₀ x hx y
  have hΦ : Function.Injective Φ := by
    intro q q' hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
    induction q' using QuotientAddGroup.induction_on with
    | H x' =>
    apply (QuotientAddGroup.eq).mpr
    apply hXnd
    intro y
    have h := congrArg (fun φ : AddChar (Y ⧸ Y₀) ℂ => φ (y : Y ⧸ Y₀)) hq
    change β x y = β x' y at h
    rw [hβ, ← h, mul_comm, hβneg]
  -- the transposed pairing
  let γ : Y → AddChar X ℂ := fun y =>
    { toFun := fun x => β x y
      map_zero_eq_one' := hX₀ 0 X₀.zero_mem y
      map_add_eq_mul' := fun x x' => hβ x x' y }
  let Ψ₀ : Y →+ AddChar (X ⧸ X₀) ℂ :=
    { toFun := fun y => descendChar X₀ (γ y) fun x hx => hX₀ x hx y
      map_zero' := by
        ext x
        induction x using QuotientAddGroup.induction_on with
        | H x => exact (β x).map_zero_eq_one
      map_add' := by
        intro y y'
        ext x
        induction x using QuotientAddGroup.induction_on with
        | H x => exact (β x).map_add_eq_mul y y' }
  let Ψ : Y ⧸ Y₀ →+ AddChar (X ⧸ X₀) ℂ := QuotientAddGroup.lift Y₀ Ψ₀ fun y hy => by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact hY₀ y hy x
  have hΨ : Function.Injective Ψ := by
    intro q q' hq
    induction q using QuotientAddGroup.induction_on with
    | H y =>
    induction q' using QuotientAddGroup.induction_on with
    | H y' =>
    apply (QuotientAddGroup.eq).mpr
    apply hYnd
    intro x
    have h := congrArg (fun φ : AddChar (X ⧸ X₀) ℂ => φ (x : X ⧸ X₀)) hq
    change β x y = β x y' at h
    rw [(β x).map_add_eq_mul, ← h, AddChar.map_neg_eq_inv, inv_mul_cancel₀]
    · exact (β x).val_isUnit y |>.ne_zero
  have hcard : Nat.card (AddChar (Y ⧸ Y₀) ℂ) ≤ Nat.card (X ⧸ X₀) := by
    rw [natCard_addChar]
    calc Nat.card (Y ⧸ Y₀) ≤ Nat.card (AddChar (X ⧸ X₀) ℂ) :=
          Nat.card_le_card_of_injective Ψ hΨ
      _ = Nat.card (X ⧸ X₀) := natCard_addChar _
  have : Finite (AddChar (Y ⧸ Y₀) ℂ) := Finite.of_fintype _
  obtain ⟨q, hq⟩ := (hΦ.bijective_of_nat_card_le hcard).2 (descendChar Y₀ χ hχ)
  induction q using QuotientAddGroup.induction_on with
  | H x =>
  refine ⟨x, fun y => ?_⟩
  have h := congrArg (fun φ : AddChar (Y ⧸ Y₀) ℂ => φ (y : Y ⧸ Y₀)) hq
  exact h.symm

end Pairing

section Classification

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- On each lattice `L k` containing the triviality lattice `L m` of `χ`, the
character `χ` agrees with `y ↦ ψ (a y)` for some `a ∈ L (t - m)`. -/
theorem exists_mul_eq_on_additiveLattice (ψ χ : Multiplicative F.Carrier →* ℂˣ) {t m k : ℤ}
    (ht : ∀ x ∈ T.additiveLattice t, ψ (ofAdd x) = 1) {x₀ : F.Carrier}
    (hx₀ : x₀ ∈ T.additiveLattice (t + 1)) (hψx₀ : ψ (ofAdd x₀) ≠ 1)
    (hm : ∀ x ∈ T.additiveLattice m, χ (ofAdd x) = 1) :
    ∃ a ∈ T.additiveLattice (t - m), ∀ x ∈ T.additiveLattice k,
      χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  have := finite_quotient_additiveLattice T (t - k) (t - m)
  have := finite_quotient_additiveLattice T m k
  have hprod : ∀ {i j : ℤ} {a x : F.Carrier}, a ∈ T.additiveLattice i →
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
theorem exists_mul_eq (ψ χ : Multiplicative F.Carrier →* ℂˣ)
    (hψ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)))
    (hψ1 : ψ ≠ 1)
    (hχ : letI := T.topology
      IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) :
    ∃ a : F.Carrier, ∀ x : F.Carrier, χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨t, ht, x₀, hx₀, hψx₀⟩ := exists_exact_conductor T ψ hψ hψ1
  obtain ⟨m, hm⟩ := exists_trivial_additiveLattice T χ hχ
  let S : ℕ → Set F.Carrier := fun i =>
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
    ∃ ψ : Multiplicative F.Carrier →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ))) ∧
      ∀ χ : Multiplicative F.Carrier →* ℂˣ,
        (letI := T.topology; IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) →
        ∃ a : F.Carrier, ∀ x : F.Carrier, χ (ofAdd x) = ψ (ofAdd (a * x)) := by
  let := T.topology
  by_cases h : ∃ ψ : Multiplicative F.Carrier →* ℂˣ,
      IsLocallyConstant (fun x : F.Carrier => (ψ (ofAdd x) : ℂ)) ∧ ψ ≠ 1
  · obtain ⟨ψ, hψ, hψ1⟩ := h
    exact ⟨ψ, hψ, fun χ hχ => exists_mul_eq T ψ χ hψ hψ1 hχ⟩
  · push Not at h
    refine ⟨1, ?_, fun χ hχ => ⟨0, fun x => by rw [h χ hχ]; rfl⟩⟩
    simp only [MonoidHom.one_apply, Units.val_one]
    exact IsLocallyConstant.const 1

/-- With a generating character `ψ`, every locally constant character of `F^n`
is `v ↦ ψ (a ⬝ᵥ v)`. -/
theorem exists_dotProduct_eq (ψ : Multiplicative F.Carrier →* ℂˣ)
    (hgen : ∀ χ : Multiplicative F.Carrier →* ℂˣ,
      (letI := T.topology; IsLocallyConstant (fun x : F.Carrier => (χ (ofAdd x) : ℂ))) →
      ∃ a : F.Carrier, ∀ x : F.Carrier, χ (ofAdd x) = ψ (ofAdd (a * x)))
    {n : ℕ} (χ : Multiplicative (Fin n → F.Carrier) →* ℂˣ)
    (hχ : letI := T.topology
      IsLocallyConstant (fun v : Fin n → F.Carrier => (χ (ofAdd v) : ℂ))) :
    ∃ a : Fin n → F.Carrier, ∀ v : Fin n → F.Carrier,
      χ (ofAdd v) = ψ (ofAdd (a ⬝ᵥ v)) := by
  let := T.topology
  have hi : ∀ i : Fin n, ∃ a : F.Carrier, ∀ x : F.Carrier,
      χ (ofAdd (Pi.single i x)) = ψ (ofAdd (a * x)) := fun i => by
    have hc : Continuous fun x : F.Carrier => (Pi.single i x : Fin n → F.Carrier) :=
      continuous_single (A := fun _ : Fin n => F.Carrier) i
    exact hgen (χ.comp (AddMonoidHom.single (fun _ : Fin n => F.Carrier) i).toMultiplicative)
      (hχ.comp_continuous hc)
  choose a ha using hi
  refine ⟨a, fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [ofAdd_sum, map_prod]
  simp only [ha, dotProduct, ofAdd_sum, map_prod]

end Classification

section Transitivity

/-- A nonzero row vector is moved to the last coordinate row: some invertible
matrix `g` satisfies `a ⬝ᵥ (g v) = v_last` for every `v`. -/
theorem exists_dotProduct_mulVec_eq_last {K : Type*} [Field K] {n : ℕ}
    (a : Fin (n + 1) → K) (ha : a ≠ 0) :
    ∃ g : Langlands.GeneralLinear (n + 1) K, ∀ v : Fin (n + 1) → K,
      a ⬝ᵥ (g.val *ᵥ v) = v (Fin.last n) := by
  classical
  obtain ⟨w, hw, hwl⟩ : ∃ w : Fin (n + 1) → K, a ⬝ᵥ w = 1 ∧ w (Fin.last n) ≠ 0 := by
    by_cases hl : a (Fin.last n) = 0
    · obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
        by_contra h
        push Not at h
        exact ha (funext h)
      have hkl : k ≠ Fin.last n := fun h => hk (h ▸ hl)
      refine ⟨Pi.single k (a k)⁻¹ + Pi.single (Fin.last n) 1, ?_, ?_⟩
      · rw [dotProduct_add, dotProduct_single, dotProduct_single, hl,
          mul_inv_cancel₀ hk, zero_mul, add_zero]
      · simp [hkl.symm]
    · refine ⟨Pi.single (Fin.last n) (a (Fin.last n))⁻¹, ?_, ?_⟩
      · rw [dotProduct_single, mul_inv_cancel₀ hl]
      · simp [hl]
  let u : Fin (n + 1) → K := Pi.single (Fin.last n) 1 - a
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) K := 1 + Matrix.of fun i j => w i * u j
  have hM : ∀ v, M *ᵥ v = v + (u ⬝ᵥ v) • w := by
    intro v
    ext i
    simp only [M, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hu : ∀ v, u ⬝ᵥ v = v (Fin.last n) - a ⬝ᵥ v := by
    intro v
    simp only [u, sub_dotProduct, single_dotProduct, one_mul]
  have hdot : ∀ v, a ⬝ᵥ (M *ᵥ v) = v (Fin.last n) := by
    intro v
    rw [hM, dotProduct_add, dotProduct_smul, hw, hu, smul_eq_mul, mul_one]
    ring
  have hinj : Function.Injective M.mulVec := by
    intro v v' h
    have h0 : M *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    have hl : (v - v') (Fin.last n) = 0 := by rw [← hdot (v - v'), h0, dotProduct_zero]
    have hd : v - v' = (a ⬝ᵥ (v - v')) • w := by
      have h1 := hM (v - v')
      rw [h0, hu, hl, zero_sub, neg_smul] at h1
      exact add_neg_eq_zero.mp h1.symm
    have had : a ⬝ᵥ (v - v') = 0 := by
      have h2 := congrFun hd (Fin.last n)
      rw [hl, Pi.smul_apply, smul_eq_mul] at h2
      exact (mul_eq_zero.mp h2.symm).resolve_right hwl
    rw [had, zero_smul] at hd
    exact sub_eq_zero.mp hd
  have hunit := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ⟨hunit.unit, hdot⟩

end Transitivity

end Langlands.Whittaker.MirabolicFiniteLength
