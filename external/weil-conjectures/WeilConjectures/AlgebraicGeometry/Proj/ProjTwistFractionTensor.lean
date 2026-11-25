/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.Ring

/-! # Scalar extension of one homogeneous fraction piece

## References

* Stacks Project, Tags 01MY and 01N2, standard-open calculation
* Stacks, Tag 01N2, standard-open zero criterion
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open TensorProduct

namespace AlgebraicGeometry.Proj

/-- The degree-j fraction piece in A_f, constructed as a span of homogeneous fractions. -/
def twistChartFractionSubmodule
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) (n : ℕ) (f : A) (j : ℤ) :
    Submodule R (Localization.Away f) :=
  Submodule.span R {z | ∃ (m i : ℕ) (a : A),
    (i : ℤ) = j + (m : ℤ) * n ∧ a ∈ 𝒜 i ∧
      Localization.mk a (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) = z}

section Fractions
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
  {n : ℕ} {f : A} (hf : f ∈ 𝒜 n) (hn : 0 < n) (j : ℤ)

private lemma degree_add (m i k : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n) :
    ((i + k * n : ℕ) : ℤ) = j + ((m + k : ℕ) : ℤ) * n := by
  push_cast
  rw [hi]
  ring

private def fractionMap (m i : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n) :
    𝒜 i →ₗ[R] twistChartFractionSubmodule 𝒜 n f j where
  toFun a := ⟨Localization.mk (a : A) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f),
    Submodule.subset_span ⟨m, i, a, hi, a.property, rfl⟩⟩
  map_add' _ _ := Subtype.ext (Localization.add_mk_self _ _ _).symm
  map_smul' r a := Subtype.ext (Localization.smul_mk r (a : A) _).symm

private def transition (i k : ℕ) : 𝒜 i →ₗ[R] 𝒜 (i + k * n) where
  toFun a := ⟨(a : A) * f ^ k, by
    simpa only [nsmul_eq_mul, Nat.cast_id] using
      SetLike.mul_mem_graded a.property (SetLike.pow_mem_graded k hf)⟩
  map_add' a b := Subtype.ext (add_mul _ _ _)
  map_smul' r a := Subtype.ext (smul_mul_assoc _ _ _)

private lemma fraction_transition (m i k : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n)
    (a : 𝒜 i) :
    fractionMap 𝒜 (f := f) j (m + k) (i + k * n) (degree_add j m i k hi)
      (transition 𝒜 hf i k a) = fractionMap 𝒜 (f := f) j m i hi a := by
  apply Subtype.ext
  change Localization.mk ((a : A) * f ^ k) _ = Localization.mk (a : A) _
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change f ^ (m + k) * (a : A) = f ^ m * ((a : A) * f ^ k)
  rw [pow_add]
  ring

include hn in
private lemma nonnegative_offset : 0 ≤ j + (j.natAbs : ℤ) * n := by
  have hj := Int.natCast_natAbs j
  have hn' : (1 : ℤ) ≤ n := by omega
  have habs : 0 ≤ (j.natAbs : ℤ) := by omega
  nlinarith [neg_le_abs j]

include hf hn in
/-- Every element of the span is a single homogeneous fraction. Common denominators
preserve its degree. -/
theorem twistChartFraction_representative
    (z : twistChartFractionSubmodule 𝒜 n f j) :
    ∃ (m i : ℕ) (a : A), (i : ℤ) = j + (m : ℤ) * n ∧ a ∈ 𝒜 i ∧
      Localization.mk a (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) = (z : Localization.Away f) := by
  suffices h : ∀ x ∈ twistChartFractionSubmodule 𝒜 n f j,
      ∃ (m i : ℕ) (a : A), (i : ℤ) = j + (m : ℤ) * n ∧ a ∈ 𝒜 i ∧
        Localization.mk a (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) = x from
    h z z.property
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨j.natAbs, (j + (j.natAbs : ℤ) * n).toNat, 0,
      Int.toNat_of_nonneg (nonnegative_offset hn j), (𝒜 _).zero_mem, ?_⟩
    exact Localization.mk_zero _
  | add x y hx hy hx' hy' =>
    obtain ⟨m, i, a, hi, ha, rfl⟩ := hx'
    obtain ⟨k, l, b, hl, hb, rfl⟩ := hy'
    have hil : i + k * n = l + m * n := by
      have := degree_add j m i k hi
      have := degree_add j k l m hl
      omega
    refine ⟨m + k, i + k * n, a * f ^ k + b * f ^ m,
      degree_add j m i k hi, ?_, ?_⟩
    · apply (𝒜 _).add_mem
      · simpa only [nsmul_eq_mul, Nat.cast_id] using
          SetLike.mul_mem_graded ha (SetLike.pow_mem_graded k hf)
      · rw [hil]
        simpa only [nsmul_eq_mul, Nat.cast_id] using
          SetLike.mul_mem_graded hb (SetLike.pow_mem_graded m hf)
    · rw [Localization.add_mk]
      simp only [Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      change f ^ (m + k) * (f ^ m * b + f ^ k * a) =
        (f ^ m * f ^ k) * (a * f ^ k + b * f ^ m)
      rw [pow_add]
      ring
  | smul r x hx hx' =>
    obtain ⟨m, i, a, hi, ha, rfl⟩ := hx'
    exact ⟨m, i, r • a, hi, (𝒜 i).smul_mem r ha, (Localization.smul_mk r a _).symm⟩

include hf hn in
private lemma tensor_representative {S : Type u} [CommRing S] [Algebra R S]
    (x : S ⊗[R] twistChartFractionSubmodule 𝒜 n f j) :
    ∃ (m i : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n) (c : S ⊗[R] 𝒜 i),
      (fractionMap 𝒜 (f := f) j m i hi).baseChange S c = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s z =>
    obtain ⟨m, i, a, hi, ha, hz⟩ := twistChartFraction_representative 𝒜 hf hn j z
    refine ⟨m, i, hi, s ⊗ₜ[R] ⟨a, ha⟩, ?_⟩
    rw [LinearMap.baseChange_tmul]
    congr 1
    exact Subtype.ext hz
  | add x y hx hy =>
    obtain ⟨m, i, hi, c, rfl⟩ := hx
    obtain ⟨k, l, hl, c', rfl⟩ := hy
    have hil : i + k * n = l + m * n := by
      have := degree_add j m i k hi
      have := degree_add j k l m hl
      omega
    have htrans (m i k : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n)
        (c : S ⊗[R] 𝒜 i) :
        (fractionMap 𝒜 (f := f) j (m + k) (i + k * n) (degree_add j m i k hi)).baseChange S
          ((transition 𝒜 hf i k).baseChange S c) =
        (fractionMap 𝒜 (f := f) j m i hi).baseChange S c := by
      induction c using TensorProduct.inductionOn with
      | tmul s a =>
        simp only [LinearMap.baseChange_tmul]
        exact congrArg (fun z ↦ s ⊗ₜ[R] z) (fraction_transition 𝒜 hf j m i k hi a)
      | add c d hc hd => simp only [map_add, hc, hd]
    have hy' : ∃ d : S ⊗[R] 𝒜 (i + k * n),
        (fractionMap 𝒜 (f := f) j (m + k) (i + k * n) (degree_add j m i k hi)).baseChange S d =
          (fractionMap 𝒜 (f := f) j k l hl).baseChange S c' := by
      have hh : ∃ d : S ⊗[R] 𝒜 (l + m * n),
          (fractionMap 𝒜 (f := f) j (k + m) (l + m * n)
            (degree_add j k l m hl)).baseChange S d =
              (fractionMap 𝒜 (f := f) j k l hl).baseChange S c' :=
        ⟨(transition 𝒜 hf l m).baseChange S c', htrans k l m hl c'⟩
      have hcast (q : ℕ) (hq : q = l + m * n)
          (hqi : (q : ℤ) = j + ((m + k : ℕ) : ℤ) * n) :
          ∃ d : S ⊗[R] 𝒜 q,
            (fractionMap 𝒜 (f := f) j (m + k) q hqi).baseChange S d =
              (fractionMap 𝒜 (f := f) j k l hl).baseChange S c' := by
        subst q
        simpa only [Nat.add_comm m k] using hh
      exact hcast _ hil _
    obtain ⟨d, hd⟩ := hy'
    refine ⟨m + k, i + k * n, degree_add j m i k hi,
      (transition 𝒜 hf i k).baseChange S c + d, ?_⟩
    rw [map_add, htrans, hd]

end Fractions

/-- Scalar extension of the inclusion of a homogeneous fraction piece is injective.
The map is normalized as coefficient multiplication followed by the localization of ψ. -/
theorem exists_twistChartFraction_tensor_embedding
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (1 ⊗ₜ[R] a) = ψ a)
    (j : ℤ) (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    ∃ L : (S ⊗[R] twistChartFractionSubmodule 𝒜 n f j) →ₗ[S]
        Localization.Away (ψ f),
      Function.Injective L ∧
      ∀ (s : S) (z : twistChartFractionSubmodule 𝒜 n f j),
        L (s ⊗ₜ[R] z) = s •
          IsLocalization.Away.map (Localization.Away f) (Localization.Away (ψ f))
            ψ.toRingHom f (z : Localization.Away f) := by
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hψR (r : R) : ψ (algebraMap R A r) = algebraMap R B r := by
    rw [← hβψ, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact β.commutes (algebraMap R S r)
  let ψR : A →ₐ[R] B := { ψ.toRingHom with commutes' := hψR }
  let μ : Localization.Away f →ₐ[R] Localization.Away (ψ f) :=
    IsLocalization.Away.mapₐ _ _ ψR f
  let l := μ.toLinearMap.comp (twistChartFractionSubmodule 𝒜 n f j).subtype
  let L := l.liftBaseChange S
  have hL (s : S) (z : twistChartFractionSubmodule 𝒜 n f j) :
      L (s ⊗ₜ[R] z) = s • μ (z : Localization.Away f) := rfl
  let num (m : ℕ) : B →ₗ[S] Localization.Away (ψ f) :=
    { toFun := fun b ↦ Localization.mk b
        (⟨ψ f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers (ψ f))
      map_add' := fun _ _ ↦ (Localization.add_mk_self _ _ _).symm
      map_smul' := fun s b ↦ (Localization.smul_mk s b _).symm }
  have hfrac (s : S) (m i : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n) (a : 𝒜 i) :
      L (s ⊗ₜ[R] fractionMap 𝒜 (f := f) j m i hi a) = num m (s • ψ (a : A)) := by
    rw [hL]
    change s • IsLocalization.Away.map _ _ ψ.toRingHom f
      (Localization.mk (a : A) _) = _
    simp only [IsLocalization.Away.map, Localization.mk_eq_mk', IsLocalization.map_mk',
      map_pow, map_smul, num]
    rfl
  have hnum (m i : ℕ) (hi : (i : ℤ) = j + (m : ℤ) * n) (c : S ⊗[R] 𝒜 i) :
      L ((fractionMap 𝒜 (f := f) j m i hi).baseChange S c) =
        num m (β (((𝒜 i).toBaseChange S c : (𝒜 i).baseChange S) : S ⊗[R] A)) := by
    induction c using TensorProduct.inductionOn with
    | tmul s a =>
      rw [LinearMap.baseChange_tmul, hfrac]
      change num m (s • ψ (a : A)) = num m (β (s ⊗ₜ[R] (a : A)))
      congr 1
      rw [show s ⊗ₜ[R] (a : A) = s • (1 ⊗ₜ[R] (a : A)) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hβψ]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  refine ⟨L, ?_, hL⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, i, hi, c, rfl⟩ := tensor_representative 𝒜 hf hn j x
  rw [hnum] at hx
  change Localization.mk (β (((𝒜 i).toBaseChange S c : (𝒜 i).baseChange S) :
    S ⊗[R] A)) (⟨ψ f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers (ψ f)) = 0 at hx
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hx
  have ht : (((𝒜 (i + k * n)).toBaseChange S
      ((transition 𝒜 hf i k).baseChange S c) : (𝒜 (i + k * n)).baseChange S) :
        S ⊗[R] A) =
      (((𝒜 i).toBaseChange S c : (𝒜 i).baseChange S) : S ⊗[R] A) *
        (1 ⊗ₜ[R] f) ^ k := by
    clear hk
    induction c using TensorProduct.inductionOn with
    | tmul s a =>
      change s ⊗ₜ[R] ((a : A) * f ^ k) = (s ⊗ₜ[R] (a : A)) * (1 ⊗ₜ[R] f) ^ k
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_pow, mul_one]
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy, add_mul]
  have hz : (transition 𝒜 hf i k).baseChange S c = 0 := by
    apply DirectSum.toBaseChange_injective 𝒜 (S := S) (i + k * n)
    apply Subtype.ext
    rw [ht, map_zero, ZeroMemClass.coe_zero]
    apply β.injective
    rw [map_mul, map_pow, hβψ, map_zero]
    simpa only [mul_comm] using hk
  have htrans :
      (fractionMap 𝒜 (f := f) j (m + k) (i + k * n) (degree_add j m i k hi)).baseChange S
        ((transition 𝒜 hf i k).baseChange S c) =
      (fractionMap 𝒜 (f := f) j m i hi).baseChange S c := by
    clear hk ht hz
    induction c using TensorProduct.inductionOn with
    | tmul s a =>
      simp only [LinearMap.baseChange_tmul]
      exact congrArg (fun z ↦ s ⊗ₜ[R] z) (fraction_transition 𝒜 hf j m i k hi a)
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← htrans, hz, map_zero]

end AlgebraicGeometry.Proj
