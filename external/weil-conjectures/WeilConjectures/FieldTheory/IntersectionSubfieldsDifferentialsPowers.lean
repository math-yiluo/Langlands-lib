/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.FieldTheory.IntersectionSubfieldsSubspace
import WeilConjectures.FieldTheory.FrobeniusBasisCompositum

/-! # Finite-extension p-power intersection

Source: Stacks Project, More on Algebra, Tag 07P4.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-powers)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
namespace FieldTheory
local instance zmodAlgebraPowers (p : ℕ) (K : Type u) [Field K] [CharP K p] :
    Algebra (ZMod p) K := ZMod.algebra (R := K) p

/-- Finite-extension p-power intersection.
Source: Stacks Project, More on Algebra, Tag 07P4 (`lemma-intersection-subfields`),
`literature/stacks-project/more-algebra.tex`.
(blueprint: lem-weil-pbc-intersection-subfields-differentials-powers)

Proof:
For an empty family, the intersection hypothesis makes Frobenius surjective on K.
Thus K is perfect, and its finite extension L is perfect too, giving L^p = L.

For a nonempty family, choose a finite K-basis e_i and put b_i = e_i^p. Applying
Frobenius to basis expansions identifies L^p with the K^p-span of the b_i. Choosing
p-th roots of coefficients and using injectivity of Frobenius proves independence
over K^p. The compositum-span theorem identifies each L^p Kα with the Kα-span of b.

Set F = K^p and view Kα as intermediate fields over F. For an element x common to
all composita, the kernel of the K-linear map (t,a) ↦ sum a_i b_i - t*x has a
nonzero vector over every Kα, obtained from a coefficient expansion with t = 1.
The subspace-intersection theorem, Tag 07P3, gives a nonzero kernel vector over F.
Its t-coordinate cannot vanish, by independence over F. Dividing by t gives an
F-coefficient expansion of x, so x belongs to L^p. The other inclusion follows
from the generators of each compositum. No independence over the larger Kα is used. -/
theorem intersection_subfields_differentials_powers
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    {ι : Type v} (Kα : ι → IntermediateField (ZMod p) K)
    (h₁ : ∀ α : ι, Set.range (fun x : K => x ^ p) ⊆ (Kα α : Set K))
    (h₂ : Set.range (fun x : K => x ^ p) =
      ((⨅ α, Kα α : IntermediateField (ZMod p) K) : Set K))
    (h₃ : ∀ α β : ι, ∃ γ : ι, Kα γ ≤ Kα α ⊓ Kα β) :
    ∀ (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L],
      Set.range (fun x : L => x ^ p) =
        ⋂ α : ι, ((Subfield.closure (Set.range (fun x : L => x ^ p) ∪
          (algebraMap K L '' (Kα α : Set K))) : Set L)) := by
  classical
  intro L _ _ _
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  by_cases hi : Nonempty ι
  · let := hi
    let n := Module.finrank K L
    let e : Module.Basis (Fin n) K L := Module.finBasis K L
    let b : Fin n → L := fun i ↦ (e i) ^ p
    have hsum (c : Fin n → K) :
        (∑ i, algebraMap K L (c i) * e i) ^ p =
          ∑ i, algebraMap K L (c i ^ p) * b i := by
      rw [sum_pow_char]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_pow, map_pow, b]
    have hind : ∀ c : Fin n → K,
        (∀ i, c i ∈ Set.range (fun y : K ↦ y ^ p)) →
          (∑ i, algebraMap K L (c i) * b i) = 0 → c = 0 := by
      intro c hc he
      choose d hd using hc
      have hz : (∑ i, algebraMap K L (d i) * e i) = 0 := by
        apply frobenius_inj L p
        change (∑ i, algebraMap K L (d i) * e i) ^ p = 0 ^ p
        rw [hsum, zero_pow (Fact.out : p.Prime).ne_zero]
        simpa only [hd] using he
      have hd0 := linearIndependent_iff'.mp e.linearIndependent Finset.univ d
        (by simpa only [Algebra.smul_def] using hz)
      funext i
      rw [← hd i, hd0 i (Finset.mem_univ i)]
      change (0 : K) ^ p = 0
      exact zero_pow (Fact.out : p.Prime).ne_zero
    have hpow : ∀ x : L, x ∈ Set.range (fun y : L ↦ y ^ p) ↔
        ∃ c : Fin n → K, (∀ i, c i ∈ Set.range (fun y : K ↦ y ^ p)) ∧
          x = ∑ i, algebraMap K L (c i) * b i := by
      intro x
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨fun i ↦ (e.repr y i) ^ p, fun i ↦ ⟨e.repr y i, rfl⟩, ?_⟩
        rw [← hsum]
        symm
        apply congrArg (fun z : L ↦ z ^ p)
        simpa only [Algebra.smul_def] using e.sum_repr y
      · rintro ⟨c, hc, he⟩
        choose d hd using hc
        refine ⟨∑ i, algebraMap K L (d i) * e i, ?_⟩
        change (∑ i, algebraMap K L (d i) * e i) ^ p = x
        rw [hsum]
        simpa only [hd] using he.symm
    have hspan := frobenius_basis_compositum p K L e
    let F : Subfield K := (frobenius K p).fieldRange
    have hF (α : ι) : F ≤ (Kα α).toSubfield := h₁ α
    let S : ι → IntermediateField F K := fun α ↦ Subfield.extendScalars (hF α)
    have hS : (⨅ α, S α) = ⊥ := by
      ext y
      change y ∈ ((⨅ α, S α : IntermediateField F K) : Set K) ↔
        y ∈ (⊥ : IntermediateField F K)
      rw [IntermediateField.coe_iInf]
      simp only [Set.mem_iInter, IntermediateField.mem_bot]
      change (∀ α, y ∈ Kα α) ↔ y ∈ Set.range F.subtype
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        change y ∈ Set.range (fun z : K ↦ z ^ p)
        rw [h₂, IntermediateField.coe_iInf]
        exact Set.mem_iInter.mpr hy
      · rintro ⟨a, rfl⟩
        have ha : (a : K) ∈ Set.range (fun z : K ↦ z ^ p) := a.property
        rw [h₂, IntermediateField.coe_iInf] at ha
        exact Set.mem_iInter.mp ha
    have hd : ∀ α β, ∃ γ, S γ ≤ S α ⊓ S β := by
      intro α β
      obtain ⟨γ, hγ⟩ := h₃ α β
      refine ⟨γ, ?_⟩
      intro y hy
      have hyγ : y ∈ Kα γ := hy
      have hyαβ : y ∈ Kα α ⊓ Kα β := hγ hyγ
      exact ⟨hyαβ.1, hyαβ.2⟩
    apply Set.Subset.antisymm
    · intro x hx
      apply Set.mem_iInter.mpr
      intro α
      exact Subfield.subset_closure (Or.inl hx)
    · intro x hx
      let f : (Fin (n + 1) → K) →ₗ[K] L :=
        { toFun := fun v ↦ (∑ i : Fin n, algebraMap K L (v i.succ) * b i) -
            algebraMap K L (v 0) * x
          map_add' := by
            intro v w
            simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
            ring
          map_smul' := by
            intro c v
            simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def,
              mul_sub, Finset.mul_sum, mul_assoc, RingHom.id_apply] }
      have hf (v : Fin (n + 1) → K) :
          f v = (∑ i : Fin n, algebraMap K L (v i.succ) * b i) -
            algebraMap K L (v 0) * x := rfl
      have hw : ∀ α, ∃ v : Fin (n + 1) → K,
          v ∈ LinearMap.ker f ∧ v ≠ 0 ∧ ∀ i, v i ∈ S α := by
        intro α
        obtain ⟨c, hc, he⟩ := (hspan (Kα α).toSubfield (h₁ α) x).mp
          (Set.mem_iInter.mp hx α)
        refine ⟨Fin.cons 1 c, ?_, ?_, ?_⟩
        · rw [LinearMap.mem_ker, hf]
          simpa using sub_eq_zero.mpr he.symm
        · intro h
          have := congrFun h 0
          simp at this
        · intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact (S α).one_mem
          · exact hc j
      obtain ⟨v, hv, hvne, hvF⟩ :=
        (IntermediateField.exists_ne_zero_mem_base_iff_forall_mem_intermediateField
          S hS hd (n + 1) (Nat.le_add_left 1 n) (LinearMap.ker f)).mpr hw
      have hvpow (i : Fin (n + 1)) : v i ∈ Set.range (fun y : K ↦ y ^ p) := by
        obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp (hvF i)
        exact ha ▸ a.property
      have hve : (∑ i : Fin n, algebraMap K L (v i.succ) * b i) =
          algebraMap K L (v 0) * x := by
        exact sub_eq_zero.mp (by simpa only [LinearMap.mem_ker, hf] using hv)
      have hv0 : v 0 ≠ 0 := by
        intro hzero
        have htail : (fun i : Fin n ↦ v i.succ) = 0 :=
          hind _ (fun i ↦ hvpow i.succ) (by simpa [hzero] using hve)
        apply hvne
        funext i
        exact Fin.cases hzero (fun j ↦ congrFun htail j) i
      apply (hpow x).mpr
      refine ⟨fun i ↦ v i.succ / v 0, ?_, ?_⟩
      · intro i
        exact F.div_mem (hvpow i.succ) (hvpow 0)
      · calc
          x = (algebraMap K L (v 0))⁻¹ *
              (∑ i : Fin n, algebraMap K L (v i.succ) * b i) := by
            rw [hve, ← mul_assoc, inv_mul_cancel₀]
            · simp
            · exact fun h ↦ hv0 ((algebraMap K L).injective (by simpa using h))
          _ = ∑ i : Fin n, algebraMap K L (v i.succ / v 0) * b i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [map_div₀]
            ring
  · have : IsEmpty ι := not_nonempty_iff.mp hi
    have hsurj : Function.Surjective (fun y : K ↦ y ^ p) := by
      intro y
      have hy : y ∈ Set.range (fun y : K ↦ y ^ p) := by
        rw [h₂]
        simp
      exact hy
    let : PerfectRing K p := PerfectRing.ofSurjective K p hsurj
    let : PerfectField K := PerfectRing.toPerfectField K p
    let : PerfectField L := Algebra.IsAlgebraic.perfectField K
    ext x
    simp only [Set.mem_range, Set.mem_iInter]
    constructor
    · intro _ α
      exact isEmptyElim α
    · intro _
      exact PerfectRing.bijective_frobenius.2 x
end FieldTheory
