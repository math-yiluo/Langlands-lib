/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Pointwise
public import Mathlib.RingTheory.Trace.Basic

/-!
# Commensurability of a discrete valuation ring with its multiples

Let `K ⊇ k` be fields and `O ⊆ K` a `k`-subalgebra which is a discrete valuation ring with
fraction field `K` and residue field finite over `k` (for instance the local ring of a smooth
curve over `k` at a closed point). Then for every `f ∈ K` the `k`-subspaces `f O` and `O` of `K`
are commensurable: `(f O + O) / O` is finite-dimensional, and so is `(f O + O) / (f O ∩ O)` for
`f ≠ 0` (`Subalgebra.finiteDimensional_sup_quotient_inf`). This is the hypothesis on the local
rings in Tate's construction of residues.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

open Pointwise

namespace Submodule

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A subquotient `P₃ ⧸ P₂` of a finite-dimensional subquotient `P₄ ⧸ P₁`, with
`P₁ ≤ P₂` and `P₃ ≤ P₄`, is finite-dimensional. -/
lemma finiteDimensional_subquotient_of_le {P₁ P₂ P₃ P₄ : Submodule k V} (h12 : P₁ ≤ P₂)
    (h34 : P₃ ≤ P₄) [FiniteDimensional k (↥P₄ ⧸ P₁.comap P₄.subtype)] :
    FiniteDimensional k (↥P₃ ⧸ P₂.comap P₃.subtype) := by
  let φ : ↥P₃ →ₗ[k] ↥P₄ ⧸ P₁.comap P₄.subtype :=
    (P₁.comap P₄.subtype).mkQ ∘ₗ Submodule.inclusion h34
  have hker : LinearMap.ker φ ≤ LinearMap.ker (P₂.comap P₃.subtype).mkQ := by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.ker_mkQ]
    exact h12 hx
  have : FiniteDimensional k (↥P₃ ⧸ LinearMap.ker φ) :=
    Module.Finite.equiv φ.quotKerEquivRange.symm
  refine Module.Finite.of_surjective ((LinearMap.ker φ).liftQ _ hker) fun y ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

variable {K : Type*} [Field K] [Algebra k K]

/-- Multiplying by `t ∈ K` maps a finite-dimensional subquotient `P ⧸ Q` of `K` onto
`t P ⧸ t Q`. -/
lemma finiteDimensional_smul_subquotient (t : K) {P Q : Submodule k K}
    [FiniteDimensional k (↥P ⧸ Q.comap P.subtype)] :
    FiniteDimensional k (↥(t • P) ⧸ (t • Q).comap (t • P).subtype) := by
  let ψ : ↥P →ₗ[k] ↥(t • P) :=
    { toFun p := ⟨t • (p : K), Submodule.smul_mem_pointwise_smul _ t P p.2⟩
      map_add' p q := Subtype.ext (smul_add t (p : K) q)
      map_smul' c p := Subtype.ext (smul_comm t c (p : K)) }
  have hker : Q.comap P.subtype ≤ LinearMap.ker (((t • Q).comap (t • P).subtype).mkQ ∘ₗ ψ) := by
    intro p hp
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ t Q hp
  refine Module.Finite.of_surjective ((Q.comap P.subtype).liftQ _ hker) fun y ↦ ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨p, hp, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact ⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩

end Submodule

namespace Subalgebra

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (O : Subalgebra k K)

lemma smul_toSubmodule_le {c : K} (hc : c ∈ O) : c • toSubmodule O ≤ toSubmodule O := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  exact O.mul_mem hc hy

lemma units_smul_toSubmodule (u : Oˣ) : ((u : O) : K) • toSubmodule O = toSubmodule O := by
  refine le_antisymm (smul_toSubmodule_le O (u : O).2) fun x hx ↦ ?_
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
    ⟨((u⁻¹ : Oˣ) : O) * x, O.mul_mem (u⁻¹ : Oˣ).1.2 hx, ?_⟩
  change ((u : O) : K) * ((((u⁻¹ : Oˣ) : O) : K) * x) = x
  rw [← mul_assoc, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, one_mul]

variable [IsDiscreteValuationRing O] [Module.Finite k (IsLocalRing.ResidueField O)]

/-- `O ⧸ ϖ O` is finite-dimensional for a uniformiser `ϖ`: it embeds into the residue field. -/
lemma finiteDimensional_quotient_uniformizer {ϖ : O} (hϖ : Irreducible ϖ) :
    FiniteDimensional k (↥(toSubmodule O) ⧸
      ((ϖ : K) • toSubmodule O).comap (toSubmodule O).subtype) := by
  let ρ : ↥(toSubmodule O) →ₗ[k] IsLocalRing.ResidueField O :=
    (IsScalarTower.toAlgHom k O (IsLocalRing.ResidueField O)).toLinearMap ∘ₗ
      { toFun a := ⟨a.1, a.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
  have hker : LinearMap.ker ρ = ((ϖ : K) • toSubmodule O).comap (toSubmodule O).subtype := by
    ext ⟨a, ha⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    change IsLocalRing.residue O ⟨a, ha⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, b.2, ?_⟩
      exact (congr_arg Subtype.val hb).symm
    · intro h
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      exact ⟨⟨b, hb⟩, rfl⟩
  exact Module.Finite.equiv
    ((Submodule.quotEquivOfEq _ _ hker).symm.trans ρ.quotKerEquivRange).symm

/-- `O ⧸ ϖⁿ O` is finite-dimensional, by induction on `n`. -/
lemma finiteDimensional_quotient_uniformizer_pow {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    FiniteDimensional k (↥(toSubmodule O) ⧸
      (((ϖ : K) ^ n) • toSubmodule O).comap (toSubmodule O).subtype) := by
  have := finiteDimensional_quotient_uniformizer O hϖ
  induction n with
  | zero =>
    have : Subsingleton (↥(toSubmodule O) ⧸
        (((ϖ : K) ^ 0) • toSubmodule O).comap (toSubmodule O).subtype) := by
      rw [pow_zero, one_smul, Submodule.comap_subtype_self, Submodule.Quotient.subsingleton_iff]
    infer_instance
  | succ n ih =>
    set A := toSubmodule O
    have hmem (m : ℕ) (a : K) (ha : a ∈ A) : (ϖ : K) ^ m * a ∈ A :=
      O.mul_mem (O.pow_mem ϖ.2 m) ha
    have hle : ((ϖ : K) ^ (n + 1)) • A ≤ ((ϖ : K) ^ n) • A := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨(ϖ : K) * a, by simpa using hmem 1 a ha, ?_⟩
      simp only [smul_eq_mul]
      ring
    let mul : ↥A →ₗ[k] ↥A :=
      { toFun a := ⟨(ϖ : K) ^ n * a, hmem n a a.2⟩
        map_add' a b := Subtype.ext (mul_add _ _ _)
        map_smul' c a := Subtype.ext (mul_smul_comm c _ _) }
    have hf : (((ϖ : K) ^ 1) • A).comap A.subtype ≤
        LinearMap.ker (Submodule.mkQ ((((ϖ : K) ^ (n + 1)) • A).comap A.subtype) ∘ₗ mul) := by
      rintro ⟨a, ha⟩ h
      rw [Submodule.mem_comap, Submodule.subtype_apply] at h
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, hb, ?_⟩
      change _ = (ϖ : K) ^ n * ((ϖ : K) ^ 1 * b)
      simp only [smul_eq_mul]
      ring
    let f := ((((ϖ : K) ^ 1) • A).comap A.subtype).liftQ _ hf
    let g := Submodule.mapQ ((((ϖ : K) ^ (n + 1)) • A).comap A.subtype)
      ((((ϖ : K) ^ n) • A).comap A.subtype) LinearMap.id (Submodule.comap_mono hle)
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.mkQ_surjective _ y
      constructor
      · intro h
        rw [Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at h
        obtain ⟨b, hb, hab⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
        exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, congr_arg Submodule.Quotient.mk (Subtype.ext hab)⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ z
        change Submodule.Quotient.mk (mul ⟨b, hb⟩) = 0
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
        exact Submodule.smul_mem_pointwise_smul _ _ _ hb
    have : FiniteDimensional k (↥A ⧸ (((ϖ : K) ^ 1) • A).comap A.subtype) := by
      rwa [pow_one]
    refine Module.Finite.of_exact hex fun y ↦ ?_
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk a, rfl⟩

/-- `O ⧸ c O` is finite-dimensional for every nonzero `c ∈ O`. -/
lemma finiteDimensional_quotient_smul {c : K} (hc : c ∈ O) (hc0 : c ≠ 0) :
    FiniteDimensional k (↥(toSubmodule O) ⧸ (c • toSubmodule O).comap (toSubmodule O).subtype) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hc0' : (⟨c, hc⟩ : O) ≠ 0 := fun h ↦ hc0 (congr_arg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc0' hϖ
  have : c • toSubmodule O = ((ϖ : K) ^ n) • toSubmodule O := by
    have hc' : c = (ϖ : K) ^ n * (((u⁻¹ : Oˣ) : O) : K) := by
      have := congr_arg Subtype.val hu
      simp only [Subalgebra.coe_mul, SubmonoidClass.coe_pow] at this
      rw [← this, mul_assoc, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, mul_one]
    rw [hc', mul_smul, units_smul_toSubmodule]
  rw [this]
  exact finiteDimensional_quotient_uniformizer_pow O hϖ n

variable [IsFractionRing O K]

/-- **One-sided commensurability**: `(f O + O) ⧸ O` is finite-dimensional for every `f ∈ K`. -/
theorem finiteDimensional_sup_quotient (f : K) :
    FiniteDimensional k (↥(f • toSubmodule O ⊔ toSubmodule O) ⧸
      (toSubmodule O).comap (f • toSubmodule O ⊔ toSubmodule O).subtype) := by
  set A := toSubmodule O
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) f
  have hb0 : (b : K) ≠ 0 := fun h ↦ nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have : FiniteDimensional k (↥A ⧸ ((b : K) • A).comap A.subtype) :=
    finiteDimensional_quotient_smul O b.2 hb0
  have h := Submodule.finiteDimensional_smul_subquotient (k := k) (b : K)⁻¹ (P := A)
    (Q := (b : K) • A)
  rw [inv_smul_smul₀ hb0] at h
  refine Submodule.finiteDimensional_subquotient_of_le (P₁ := A) (P₄ := (b : K)⁻¹ • A) le_rfl
    (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(a : K) * y, O.mul_mem a.2 hy, ?_⟩
    change (b : K)⁻¹ * ((a : K) * y) = (a : K) / (b : K) * y
    ring
  · intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(b : K) * x, O.mul_mem b.2 hx, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]

/-- **Commensurability** of `f O` and `O` for `f ≠ 0`: `(f O + O) ⧸ (f O ∩ O)` is
finite-dimensional over `k`. -/
theorem finiteDimensional_sup_quotient_inf {f : K} (hf : f ≠ 0) :
    FiniteDimensional k (↥(f • toSubmodule O ⊔ toSubmodule O) ⧸
      (f • toSubmodule O ⊓ toSubmodule O).comap (f • toSubmodule O ⊔ toSubmodule O).subtype) := by
  set A := toSubmodule O
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) f
  have hb0 : (b : K) ≠ 0 := fun h ↦ nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have ha0 : (a : K) ≠ 0 := fun h ↦ hf (by
    change (a : K) / (b : K) = 0
    rw [h, zero_div])
  have : FiniteDimensional k (↥A ⧸ (((b : K) * a) • A).comap A.subtype) :=
    finiteDimensional_quotient_smul O (O.mul_mem b.2 a.2) (mul_ne_zero hb0 ha0)
  have h := Submodule.finiteDimensional_smul_subquotient (k := k) (b : K)⁻¹ (P := A)
    (Q := ((b : K) * a) • A)
  rw [mul_smul, inv_smul_smul₀ hb0] at h
  have hdiv : ∀ y : K, ((a : K) / (b : K)) • y = (b : K)⁻¹ • ((a : K) * y) := fun y ↦ by
    change (a : K) / (b : K) * y = (b : K)⁻¹ * ((a : K) * y)
    ring
  refine Submodule.finiteDimensional_subquotient_of_le (P₁ := (a : K) • A)
    (P₄ := (b : K)⁻¹ • A) (le_inf ?_ (smul_toSubmodule_le O a.2)) (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(b : K) * y, O.mul_mem b.2 hy, ?_⟩
    change (a : K) / (b : K) * ((b : K) * y) = (a : K) * y
    field_simp
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(a : K) * y, O.mul_mem a.2 hy, ?_⟩
    exact (hdiv y).symm
  · intro x hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(b : K) * x, O.mul_mem b.2 hx, ?_⟩
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hb0, one_mul]

omit [IsFractionRing O K] in
/-- The residue map identifies `O ⧸ ϖ O` with the residue field of `O`, `k`-linearly. -/
noncomputable def quotientUniformizerEquiv {ϖ : O} (hϖ : Irreducible ϖ) :
    (↥(toSubmodule O) ⧸ ((ϖ : K) • toSubmodule O).comap (toSubmodule O).subtype) ≃ₗ[k]
      IsLocalRing.ResidueField O := by
  let ρ : ↥(toSubmodule O) →ₗ[k] IsLocalRing.ResidueField O :=
    (IsScalarTower.toAlgHom k O (IsLocalRing.ResidueField O)).toLinearMap ∘ₗ
      { toFun a := ⟨a.1, a.2⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
  have hker : LinearMap.ker ρ = ((ϖ : K) • toSubmodule O).comap (toSubmodule O).subtype := by
    ext ⟨a, ha⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    change IsLocalRing.residue O ⟨a, ha⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨b, hb⟩
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, b.2, ?_⟩
      exact (congr_arg Subtype.val hb).symm
    · intro h
      obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      exact ⟨⟨b, hb⟩, rfl⟩
  have hsurj : Function.Surjective ρ := fun r ↦ by
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨⟨o.1, o.2⟩, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker).symm.trans (ρ.quotKerEquivOfSurjective hsurj)

omit [IsFractionRing O K] [Module.Finite k (IsLocalRing.ResidueField O)] in
@[simp]
lemma quotientUniformizerEquiv_mk {ϖ : O} (hϖ : Irreducible ϖ) (a : ↥(toSubmodule O)) :
    quotientUniformizerEquiv O hϖ (Submodule.Quotient.mk a) = IsLocalRing.residue O ⟨a.1, a.2⟩ :=
  rfl

/-- Multiplication by `u ∈ O` on `O`, as a `k`-linear map. -/
noncomputable def mulToSubmodule (u : O) : ↥(toSubmodule O) →ₗ[k] ↥(toSubmodule O) where
  toFun a := ⟨(u : K) * a, O.mul_mem u.2 a.2⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' c _ := Subtype.ext (mul_smul_comm c _ _)

omit [IsDiscreteValuationRing O] [Module.Finite k (IsLocalRing.ResidueField O)]
  [IsFractionRing O K] in
lemma mulToSubmodule_le_comap (u : O) (c : K) :
    (c • toSubmodule O).comap (toSubmodule O).subtype ≤
      ((c • toSubmodule O).comap (toSubmodule O).subtype).comap (mulToSubmodule O u) := by
  rintro ⟨a, ha⟩ h
  rw [Submodule.mem_comap, Submodule.subtype_apply] at h
  obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
  refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(u : K) * b, O.mul_mem u.2 hb, ?_⟩
  change c * ((u : K) * b) = (u : K) * (c * b)
  ring

omit [IsFractionRing O K] in
/-- The trace of multiplication by `u ∈ O` on `O ⧸ ϖ O` is the trace `Tr_{κ/k}` of the residue
of `u`. -/
theorem trace_mapQ_mulToSubmodule {ϖ : O} (hϖ : Irreducible ϖ) (u : O) :
    LinearMap.trace k _ (Submodule.mapQ _ _ (mulToSubmodule O u)
      (mulToSubmodule_le_comap O u (ϖ : K))) =
      Algebra.trace k (IsLocalRing.ResidueField O) (IsLocalRing.residue O u) := by
  have := finiteDimensional_quotient_uniformizer O hϖ
  rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ (quotientUniformizerEquiv O hϖ)]
  congr 1
  refine LinearMap.ext fun r ↦ ?_
  obtain ⟨q, rfl⟩ := (quotientUniformizerEquiv O hϖ).surjective r
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Submodule.mkQ_apply,
    Submodule.mapQ_apply, quotientUniformizerEquiv_mk, quotientUniformizerEquiv_mk]
  change _ = IsLocalRing.residue O u * IsLocalRing.residue O ⟨a.1, a.2⟩
  rw [← map_mul]
  rfl

omit [IsFractionRing O K] in
/-- If the residue field of `O` is separable over `k`, then some `u ∈ O` has residue of nonzero
trace. -/
theorem exists_trace_residue_ne_zero [Algebra.IsSeparable k (IsLocalRing.ResidueField O)] :
    ∃ u : O, Algebra.trace k (IsLocalRing.ResidueField O) (IsLocalRing.residue O u) ≠ 0 := by
  by_contra! H
  have h := (traceForm_nondegenerate k (IsLocalRing.ResidueField O)).1 1 fun r ↦ by
    obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective r
    rw [Algebra.traceForm_apply, one_mul]
    exact H u
  exact one_ne_zero h

end Subalgebra
