/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.ZMod

/-!
# Continuous `ℤ_[p]`-valued characters as compatible systems of finite characters

The `p`-adic integers are the inverse limit of the rings `ZMod (p ^ n)`. This file records the
consequence for characters: for a topological group `G`, a continuous homomorphism `G → ℤ_[p]`
is the same thing as a compatible system of continuous homomorphisms `G → ZMod (p ^ n)`, namely
its reductions modulo `p ^ n`.

## Main definitions

- `PadicInt.ofCompatible`: the `p`-adic integer with prescribed compatible residues.
- `PadicInt.toZModPowContinuousMonoidHom`: reduction modulo `p ^ n`, as a continuous
  homomorphism of the underlying additive groups.
- `PadicInt.continuousMonoidHomEquiv`: continuous homomorphisms `G → ℤ_[p]` are compatible
  systems of continuous homomorphisms `G → ZMod (p ^ n)`.
-/

@[expose] public section

open Topology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- Reduction modulo `p ^ n` is continuous for the discrete topology of `ZMod (p ^ n)`: it is
constant on the open ball of radius `p ^ (-n)` around every point. -/
theorem continuous_toZModPow (n : ℕ) : Continuous (toZModPow (p := p) n) := by
  refine continuous_of_continuousAt_zero (toZModPow (p := p) n) ?_
  rw [ContinuousAt, nhds_discrete (ZMod (p ^ n)), Filter.tendsto_pure, map_zero]
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds (0 : ℤ_[p]) hpos] with x hx
  rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact hx.le

/-- Reduction modulo `p ^ n`, as a continuous homomorphism of the underlying additive groups
written multiplicatively. -/
noncomputable def toZModPowContinuousMonoidHom (n : ℕ) :
    Multiplicative ℤ_[p] →ₜ* Multiplicative (ZMod (p ^ n)) where
  toMonoidHom := (toZModPow (p := p) n).toAddMonoidHom.toMultiplicative
  continuous_toFun := continuous_toZModPow n

@[simp]
theorem toZModPowContinuousMonoidHom_apply (n : ℕ) (x : Multiplicative ℤ_[p]) :
    (toZModPowContinuousMonoidHom n x).toAdd = toZModPow n x.toAdd :=
  rfl

/-- A compatible system of residues `a n ∈ ZMod (p ^ n)` lifts to integer representatives
which are congruent modulo `p ^ n`. -/
theorem pow_dvd_val_sub_val {a : ∀ n : ℕ, ZMod (p ^ n)}
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n)) (a (n + 1)) =
      a n) (n : ℕ) :
    (p : ℤ) ^ n ∣ ((a (n + 1)).val : ℤ) - (a n).val := by
  have h := ha n
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← ZMod.natCast_zmod_val (a n)] at h
  have h' : (((a (n + 1)).val : ℤ) : ZMod (p ^ n)) = (((a n).val : ℤ) : ZMod (p ^ n)) := by
    exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  rw [← dvd_neg, neg_sub]
  exact_mod_cast h'

/-- The `p`-adic integer whose residue modulo `p ^ n` is `a n`, for a compatible system of
residues `a`. -/
noncomputable def ofCompatible (a : ∀ n : ℕ, ZMod (p ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n)) (a (n + 1)) =
      a n) :
    ℤ_[p] :=
  ofIntSeq _ (isCauSeq_padicNorm_of_pow_dvd_sub (fun n ↦ ((a n).val : ℤ)) p
    (pow_dvd_val_sub_val ha))

@[simp]
theorem toZModPow_ofCompatible (a : ∀ n : ℕ, ZMod (p ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n)) (a (n + 1)) =
      a n) (n : ℕ) : toZModPow n (ofCompatible a ha) = a n := by
  rw [ofCompatible, toZModPow_ofIntSeq_of_pow_dvd_sub _ _ (pow_dvd_val_sub_val ha)]
  simp

/-- Reduction modulo `p ^ (n + 1)` followed by reduction modulo `p ^ n` is reduction modulo
`p ^ n`. -/
theorem castHom_toZModPow_succ (n : ℕ) (x : ℤ_[p]) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n)) (toZModPow (n + 1) x) =
      toZModPow n x := by
  rw [← RingHom.comp_apply, zmod_cast_comp_toZModPow n (n + 1) (Nat.le_add_right n 1)]

section Characters

variable {G : Type*} [Group G]

/-- The homomorphism `G → ℤ_[p]` whose reductions modulo `p ^ n` are a given compatible system
of homomorphisms `G → ZMod (p ^ n)`. -/
noncomputable def monoidHomOfCompatible (f : ∀ n : ℕ, G →* Multiplicative (ZMod (p ^ n)))
    (hf : ∀ n g, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n))
      (f (n + 1) g).toAdd = (f n g).toAdd) :
    G →* Multiplicative ℤ_[p] where
  toFun g := .ofAdd (ofCompatible (fun n ↦ (f n g).toAdd) (hf · g))
  map_one' := congrArg Multiplicative.ofAdd (ext_of_toZModPow.mp fun n ↦ by simp)
  map_mul' g h := congrArg Multiplicative.ofAdd (ext_of_toZModPow.mp fun n ↦ by simp)

@[simp]
theorem toZModPow_monoidHomOfCompatible (f : ∀ n : ℕ, G →* Multiplicative (ZMod (p ^ n)))
    (hf : ∀ n g, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n))
      (f (n + 1) g).toAdd = (f n g).toAdd) (n : ℕ) (g : G) :
    toZModPow n (monoidHomOfCompatible f hf g).toAdd = (f n g).toAdd :=
  toZModPow_ofCompatible _ (hf · g) n

end Characters

variable (p) in
/-- Blueprint `lemma-invariant-additive-characters`: Continuous `ℤ_ℓ`-characters are compatible
finite-level classes, the group-theoretic half.

For a topological group `G`, a continuous homomorphism `G → ℤ_[p]` is the same thing as a
compatible system of continuous homomorphisms `G → ZMod (p ^ n)`, the bijection sending a
homomorphism to its reductions modulo `p ^ n`. It is natural in `G`
(`PadicInt.continuousMonoidHomEquiv_comp`). -/
noncomputable def continuousMonoidHomEquiv (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    (G →ₜ* Multiplicative ℤ_[p]) ≃
      {f : ∀ n : ℕ, G →ₜ* Multiplicative (ZMod (p ^ n)) //
        ∀ n g, ZMod.castHom (pow_dvd_pow p (Nat.le_add_right n 1)) (ZMod (p ^ n))
          (f (n + 1) g).toAdd = (f n g).toAdd} where
  toFun b := ⟨fun n ↦ (toZModPowContinuousMonoidHom n).comp b,
    fun n g ↦ castHom_toZModPow_succ n (b g).toAdd⟩
  invFun f :=
    { toMonoidHom := monoidHomOfCompatible (fun n ↦ (f.1 n).toMonoidHom) f.2
      continuous_toFun := by
        let φ := monoidHomOfCompatible (fun n ↦ (f.1 n).toMonoidHom) f.2
        refine continuous_of_continuousAt_one φ ?_
        rw [ContinuousAt, map_one, Metric.tendsto_nhds]
        intro ε hε
        obtain ⟨n, hn⟩ := exists_pow_neg_lt p hε
        have hU : IsOpen ((f.1 n : G → Multiplicative (ZMod (p ^ n))) ⁻¹' {1}) :=
          (isOpen_discrete _).preimage (f.1 n).continuous
        filter_upwards [hU.mem_nhds (by simp)] with g hg
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hg
        have h0 : toZModPow n (φ g).toAdd = 0 := by
          rw [toZModPow_monoidHomOfCompatible]
          exact congrArg Multiplicative.toAdd hg
        rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow] at h0
        change dist (φ g).toAdd 0 < ε
        rw [dist_zero_right]
        exact h0.trans_lt hn }
  left_inv b := ContinuousMonoidHom.ext fun g ↦ ext_of_toZModPow.mp fun n ↦
    toZModPow_monoidHomOfCompatible (fun n ↦ ((toZModPowContinuousMonoidHom n).comp b).toMonoidHom)
      (fun n g ↦ castHom_toZModPow_succ n (b g).toAdd) n g
  right_inv f := Subtype.ext <| funext fun n ↦ ContinuousMonoidHom.ext fun g ↦
    toZModPow_monoidHomOfCompatible (fun n ↦ (f.1 n).toMonoidHom) f.2 n g

@[simp]
theorem continuousMonoidHomEquiv_apply_coe {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (b : G →ₜ* Multiplicative ℤ_[p]) (n : ℕ) (g : G) :
    ((continuousMonoidHomEquiv p G b).1 n g).toAdd = toZModPow n (b g).toAdd := by
  simp only [continuousMonoidHomEquiv, Equiv.coe_fn_mk]
  rfl

/-- Blueprint `lemma-invariant-additive-characters`: Continuous `ℤ_ℓ`-characters are compatible
finite-level classes, the naturality.

The bijection `PadicInt.continuousMonoidHomEquiv` is natural in the group: the reductions of
`b ∘ φ` are the reductions of `b` composed with `φ`. In particular it intertwines the
precomposition by an automorphism, which is how the Frobenius acts on both sides. -/
theorem continuousMonoidHomEquiv_comp {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (b : G →ₜ* Multiplicative ℤ_[p]) (φ : H →ₜ* G) (n : ℕ) :
    (continuousMonoidHomEquiv p H (b.comp φ)).1 n =
      ((continuousMonoidHomEquiv p G b).1 n).comp φ := by
  simp only [continuousMonoidHomEquiv, Equiv.coe_fn_mk]
  rfl


end PadicInt
