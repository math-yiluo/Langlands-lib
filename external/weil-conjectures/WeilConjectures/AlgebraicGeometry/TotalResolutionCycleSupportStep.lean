/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

private noncomputable def totalProjection
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) [K.HasTotal (ComplexShape.up ℤ)]
    (p q n : ℤ) : (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X p).X q := by
  classical
  exact K.totalDesc (fun a b _ ↦
    if h : a = p ∧ b = q then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0)

private theorem inclusion_projection
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) [K.HasTotal (ComplexShape.up ℤ)]
    (a b p q n : ℤ) (hab : a + b = n) :
    K.ιTotalOrZero (ComplexShape.up ℤ) a b n ≫ totalProjection K p q n =
      if h : a = p ∧ b = q then (K.XXIsoOfEq _ _ _ h.1 h.2).hom else 0 := by
  classical
  rw [K.ιTotalOrZero_eq _ _ _ _ hab]
  exact K.ι_totalDesc _ _ _ _

private theorem inclusion_projection_self
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) [K.HasTotal (ComplexShape.up ℤ)]
    (p q n : ℤ) (h : p + q = n) (x : (K.X p).X q) :
    totalProjection K p q n (K.ιTotalOrZero (ComplexShape.up ℤ) p q n x) = x := by
  have he := inclusion_projection K p q p q n h
  simpa using congrArg (fun f ↦ f x) he

private theorem inclusion_projection_zero
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) [K.HasTotal (ComplexShape.up ℤ)]
    (a b p q n : ℤ) (hab : a + b = n) (h : a ≠ p)
    (x : (K.X a).X b) :
    totalProjection K p q n (K.ιTotalOrZero (ComplexShape.up ℤ) a b n x) = 0 := by
  have he := inclusion_projection K a b p q n hab
  simpa [h] using congrArg (fun f ↦ f x) he

private theorem projected_boundary
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)) [K.HasTotal (ComplexShape.up ℤ)]
    [∀ p q, (K.X p).HasHomology q]
    (a b p q n : ℤ) (hab : a + (b + 1) = n) (x : (K.X a).X b) :
    (K.X p).pOpcycles q (totalProjection K p q n
      (K.ιTotalOrZero (ComplexShape.up ℤ) a (b + 1) n ((K.X a).d b (b + 1) x))) =
        0 := by
  classical
  have he := inclusion_projection K a (b + 1) p q n hab
  by_cases hp : a = p
  · subst p
    by_cases hq : b + 1 = q
    · subst q
      rw [inclusion_projection_self K a (b + 1) n hab]
      exact congrArg (fun f ↦ f x) ((K.X a).d_pOpcycles b (b + 1))
    · have hz : K.ιTotalOrZero (ComplexShape.up ℤ) a (b + 1) n ≫
          totalProjection K a q n = 0 := by simpa [hq] using he
      have hx := congrArg (fun f ↦ f ((K.X a).d b (b + 1) x)) hz
      change totalProjection K a q n
        (K.ιTotalOrZero (ComplexShape.up ℤ) a (b + 1) n
          ((K.X a).d b (b + 1) x)) = 0 at hx
      rw [hx, map_zero]
  · rw [inclusion_projection_zero K a (b + 1) p q n hab hp, map_zero]

private theorem total_d_apply
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (p q n : ℤ) (h : p + q = n) (x : (K.X p).X q) :
    (K.total (ComplexShape.up ℤ)).d n (n + 1)
      (K.ιTotalOrZero (ComplexShape.up ℤ) p q n x) =
      K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q (n + 1)
        ((K.d p (p + 1)).f q x) +
      p.negOnePow • K.ιTotalOrZero (ComplexShape.up ℤ) p (q + 1) (n + 1)
        ((K.X p).d q (q + 1) x) := by
  have hm : K.ιTotalOrZero (ComplexShape.up ℤ) p q n ≫
      (K.total (ComplexShape.up ℤ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q (n + 1) +
      p.negOnePow • ((K.X p).d q (q + 1) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) p (q + 1) (n + 1)) := by
    rw [K.ιTotalOrZero_eq _ _ _ _ h]
    change K.ιTotal (ComplexShape.up ℤ) p q n h ≫
      (K.D₁ (ComplexShape.up ℤ) n (n + 1) +
        K.D₂ (ComplexShape.up ℤ) n (n + 1)) = _
    rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
      K.d₁_eq' (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
      K.d₂_eq' (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
    simp
  exact congrArg (fun f ↦ f x) hm

private theorem outer_cycle
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ) (r : ℕ) (z : (K.total (ComplexShape.up ℤ)).cycles n)
    (x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)))
    (hx : (K.total (ComplexShape.up ℤ)).iCycles n z =
      ∑ i ∈ Finset.range (r + 1 + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i)) :
    ∃ y : (K.X (-((r + 1 : ℕ) : ℤ))).cycles (n + ((r + 1 : ℕ) : ℤ)),
      (K.X (-((r + 1 : ℕ) : ℤ))).iCycles (n + ((r + 1 : ℕ) : ℤ)) y = x (r + 1) ∧
      HomologicalComplex.homologyMap
        (K.d (-((r + 1 : ℕ) : ℤ)) (-((r + 1 : ℕ) : ℤ) + 1))
        (n + ((r + 1 : ℕ) : ℤ))
        ((K.X (-((r + 1 : ℕ) : ℤ))).homologyπ (n + ((r + 1 : ℕ) : ℤ)) y) = 0  := by
  classical
  let p : ℤ := -((r + 1 : ℕ) : ℤ)
  let q : ℤ := n + ((r + 1 : ℕ) : ℤ)
  have hd :
      (∑ i ∈ Finset.range (r + 1 + 1),
        (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ) + 1) (n + (i : ℤ)) (n + 1)
          ((K.d (-(i : ℤ)) (-(i : ℤ) + 1)).f (n + (i : ℤ)) (x i)) +
        (-(i : ℤ)).negOnePow •
          K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ) + 1) (n + 1)
            ((K.X (-(i : ℤ))).d (n + (i : ℤ)) (n + (i : ℤ) + 1) (x i)))) = 0 := by
    have hz := congrArg (fun f ↦ f z)
      ((K.total (ComplexShape.up ℤ)).iCycles_d n (n + 1))
    change (K.total (ComplexShape.up ℤ)).d n (n + 1)
      ((K.total (ComplexShape.up ℤ)).iCycles n z) = 0 at hz
    rw [hx, map_sum] at hz
    calc
      _ = ∑ i ∈ Finset.range (r + 1 + 1),
          (K.total (ComplexShape.up ℤ)).d n (n + 1)
            (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (total_d_apply K (-(i : ℤ)) (n + (i : ℤ)) n (by omega) (x i)).symm
      _ = 0 := hz
  have hv : (K.X p).d q (q + 1) (x (r + 1)) = 0 := by
    have hpz := congrArg (fun v ↦ totalProjection K p (q + 1) (n + 1) v) hd
    rw [map_sum, map_zero] at hpz
    have hs :
        (∑ i ∈ Finset.range (r + 1 + 1),
          totalProjection K p (q + 1) (n + 1)
            (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ) + 1) (n + (i : ℤ)) (n + 1)
              ((K.d (-(i : ℤ)) (-(i : ℤ) + 1)).f (n + (i : ℤ)) (x i)) +
            (-(i : ℤ)).negOnePow •
              K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ))
                (n + (i : ℤ) + 1) (n + 1)
                ((K.X (-(i : ℤ))).d (n + (i : ℤ)) (n + (i : ℤ) + 1) (x i)))) =
        p.negOnePow • (K.X p).d q (q + 1) (x (r + 1)) := by
      calc
        _ = ∑ i ∈ Finset.range (r + 1 + 1),
            if i = r + 1 then
              p.negOnePow • (K.X p).d q (q + 1) (x (r + 1)) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          rw [map_add, map_zsmul_unit]
          rw [inclusion_projection_zero K (-(i : ℤ) + 1) (n + (i : ℤ))
            p (q + 1) (n + 1) (by omega) (by dsimp [p]; omega)]
          by_cases h : i = r + 1
          · subst i
            rw [inclusion_projection_self K p (q + 1) (n + 1)
              (by dsimp [p, q]; omega)]
            simp only [ite_true, zero_add]
            rfl
          · rw [inclusion_projection_zero K (-(i : ℤ)) (n + (i : ℤ) + 1)
              p (q + 1) (n + 1) (by omega) (by dsimp [p]; omega)]
            simp [h]
        _ = _ := by simp
    rw [hs] at hpz
    have hh := congrArg (fun v ↦ p.negOnePow • v) hpz
    simpa only [smul_smul, Int.units_mul_self, one_smul, smul_zero] using hh
  let y : (K.X p).cycles q := ((K.X p).sc q).cyclesMk (x (r + 1)) (by
    change (K.X p).d q ((ComplexShape.up ℤ).next q) (x (r + 1)) = 0
    rw [CochainComplex.next]
    exact hv)
  have hy : (K.X p).iCycles q y = x (r + 1) := ((K.X p).sc q).i_cyclesMk _ _
  have hpo : (K.X (p + 1)).pOpcycles q
      ((K.d p (p + 1)).f q (x (r + 1))) = 0 := by
    have hpz := congrArg (fun v ↦ (K.X (p + 1)).pOpcycles q
      (totalProjection K (p + 1) q (n + 1) v)) hd
    simp only [map_sum, map_zero] at hpz
    have hs :
        (∑ i ∈ Finset.range (r + 1 + 1),
          (K.X (p + 1)).pOpcycles q (totalProjection K (p + 1) q (n + 1)
            (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ) + 1) (n + (i : ℤ)) (n + 1)
              ((K.d (-(i : ℤ)) (-(i : ℤ) + 1)).f (n + (i : ℤ)) (x i)) +
            (-(i : ℤ)).negOnePow •
              K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ))
                (n + (i : ℤ) + 1) (n + 1)
                ((K.X (-(i : ℤ))).d (n + (i : ℤ)) (n + (i : ℤ) + 1) (x i))))) =
        (K.X (p + 1)).pOpcycles q ((K.d p (p + 1)).f q (x (r + 1))) := by
      calc
        _ = ∑ i ∈ Finset.range (r + 1 + 1),
            if i = r + 1 then
              (K.X (p + 1)).pOpcycles q ((K.d p (p + 1)).f q (x (r + 1)))
            else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_add, map_add, map_zsmul_unit, map_zsmul_unit,
            projected_boundary K (-(i : ℤ)) (n + (i : ℤ)) (p + 1) q (n + 1)
              (by omega) (x i), smul_zero, add_zero]
          by_cases h : i = r + 1
          · subst i
            rw [inclusion_projection_self K (p + 1) q (n + 1)
              (by dsimp [p, q]; omega)]
            simp only [ite_true]
            rfl
          · rw [inclusion_projection_zero K (-(i : ℤ) + 1) (n + (i : ℤ))
              (p + 1) q (n + 1) (by omega) (by dsimp [p]; omega), map_zero]
            simp [h]
        _ = _ := by simp
    rw [hs] at hpz
    exact hpz
  refine ⟨y, hy, ?_⟩
  apply (ModuleCat.mono_iff_injective ((K.X (p + 1)).homologyι q)).mp inferInstance
  rw [map_zero]
  have hn := congrArg (fun f ↦ f y)
    (HomologicalComplex.homologyπ_naturality (K.d p (p + 1)) q)
  change HomologicalComplex.homologyMap (K.d p (p + 1)) q
    ((K.X p).homologyπ q y) =
    (K.X (p + 1)).homologyπ q (HomologicalComplex.cyclesMap (K.d p (p + 1)) q y) at hn
  rw [hn]
  have hh := congrArg (fun f ↦ f (HomologicalComplex.cyclesMap (K.d p (p + 1)) q y))
    ((K.X (p + 1)).homology_π_ι q)
  change (K.X (p + 1)).homologyι q
      ((K.X (p + 1)).homologyπ q (HomologicalComplex.cyclesMap (K.d p (p + 1)) q y)) =
    (K.X (p + 1)).pOpcycles q
      ((K.X (p + 1)).iCycles q (HomologicalComplex.cyclesMap (K.d p (p + 1)) q y)) at hh
  have hi := congrArg (fun f ↦ f y) (HomologicalComplex.cyclesMap_i (K.d p (p + 1)) q)
  change (K.X (p + 1)).iCycles q (HomologicalComplex.cyclesMap (K.d p (p + 1)) q y) =
    (K.d p (p + 1)).f q ((K.X p).iCycles q y) at hi
  rw [hi, hy] at hh
  exact hh.trans hpo



private theorem lift_outer_class
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [∀ p q, (K.X p).HasHomology q]
    (p q : ℤ) (y : (K.X p).cycles q)
    (he : Function.Exact
      (HomologicalComplex.homologyMap (K.d (p - 1) p) q).hom
      (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom)
    (hy : HomologicalComplex.homologyMap (K.d p (p + 1)) q
      ((K.X p).homologyπ q y) = 0) :
    ∃ a : (K.X (p - 1)).cycles q, ∃ t : (K.X p).X (q - 1),
      (K.X p).iCycles q y =
        (K.d (p - 1) p).f q ((K.X (p - 1)).iCycles q a) + (K.X p).d (q - 1) q t := by
  obtain ⟨c, hc⟩ := (he ((K.X p).homologyπ q y)).mp hy
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective
    ((K.X (p - 1)).homologyπ q)).mp inferInstance c
  let v := HomologicalComplex.cyclesMap (K.d (p - 1) p) q a
  have hv : (K.X p).homologyπ q v = (K.X p).homologyπ q y := by
    have hn := congrArg (fun f ↦ f a)
      (HomologicalComplex.homologyπ_naturality (K.d (p - 1) p) q)
    change HomologicalComplex.homologyMap (K.d (p - 1) p) q
      ((K.X (p - 1)).homologyπ q a) = (K.X p).homologyπ q v at hn
    rw [ha, hc] at hn
    exact hn.symm
  have hz : (K.X p).pOpcycles q ((K.X p).iCycles q (y - v)) = 0 := by
    have hh := congrArg (fun f ↦ f (y - v)) ((K.X p).homology_π_ι q)
    change (K.X p).homologyι q ((K.X p).homologyπ q (y - v)) =
      (K.X p).pOpcycles q ((K.X p).iCycles q (y - v)) at hh
    rw [map_sub, hv, sub_self, map_zero] at hh
    exact hh.symm
  have hb : ∃ t : (K.X p).X ((ComplexShape.up ℤ).prev q),
      (K.X p).d ((ComplexShape.up ℤ).prev q) q t =
        (K.X p).iCycles q (y - v) :=
    ((K.X p).sc q).moduleCat_pOpcycles_eq_zero_iff
      ((K.X p).iCycles q (y - v)) |>.mp hz
  rw [CochainComplex.prev] at hb
  obtain ⟨t, ht⟩ := hb
  have hi := congrArg (fun f ↦ f a)
    (HomologicalComplex.cyclesMap_i (K.d (p - 1) p) q)
  change (K.X p).iCycles q v =
    (K.d (p - 1) p).f q ((K.X (p - 1)).iCycles q a) at hi
  refine ⟨a, t, ?_⟩
  rw [ht, map_sub, hi]
  abel

private theorem outer_boundary
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ p q, (K.X p).HasHomology q]
    (p q n : ℤ) (h : p + q = n) (y : (K.X p).cycles q)
    (he : Function.Exact
      (HomologicalComplex.homologyMap (K.d (p - 1) p) q).hom
      (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom)
    (hy : HomologicalComplex.homologyMap (K.d p (p + 1)) q
      ((K.X p).homologyπ q y) = 0) :
    ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
      ∃ w : (K.X (p + 1)).X (q - 1),
        (K.total (ComplexShape.up ℤ)).d (n - 1) n b =
          K.ιTotalOrZero (ComplexShape.up ℤ) p q n ((K.X p).iCycles q y) +
          K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (q - 1) n w := by
  obtain ⟨a, t, ht⟩ := lift_outer_class K p q y he hy
  let b := K.ιTotalOrZero (ComplexShape.up ℤ) (p - 1) q (n - 1)
      ((K.X (p - 1)).iCycles q a) +
    p.negOnePow • K.ιTotalOrZero (ComplexShape.up ℤ) p (q - 1) (n - 1) t
  let w := p.negOnePow • (K.d p (p + 1)).f (q - 1) t
  have ha : (K.X (p - 1)).d q (q + 1) ((K.X (p - 1)).iCycles q a) = 0 :=
    congrArg (fun f ↦ f a) ((K.X (p - 1)).iCycles_d q (q + 1))
  have hda := total_d_apply K (p - 1) q (n - 1) (by omega)
    ((K.X (p - 1)).iCycles q a)
  have hdt := total_d_apply K p (q - 1) (n - 1) (by omega) t
  have hp : p - 1 + 1 = p := by omega
  have hq : q - 1 + 1 = q := by omega
  have hn : n - 1 + 1 = n := by omega
  rw [hp, hn, ha, map_zero, smul_zero, add_zero] at hda
  rw [hq, hn] at hdt
  refine ⟨b, w, ?_⟩
  dsimp [b, w]
  simp only [Units.smul_def] at hdt ⊢
  rw [map_add, map_zsmul, hda, hdt, smul_add, smul_smul,
    ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
    map_zsmul, ht, map_add]
  abel

/-- Remove one specified outer column of a finitely supported total cycle.
Source: Stacks Project, Homology, Tag 09IZ, proof, the two boundary corrections.
(blueprint: aux-total-resolution-cycle-support-step)

Proof. Set s=r+1 and q=n+s. Project the total cocycle equation to column -s.
Since no column to its left occurs, the component x_s is a vertical cycle.
Projection to column 1-s shows that the horizontal image of x_s is a vertical
boundary, up to the total sign. Its homology class is thus in the kernel of
H^q(K.X(-s)) -> H^q(K.X(1-s)). Apply h_homology at p=-s-1 (< -1) to lift this
class from H^q(K.X(-s-1)), and choose a vertical cycle representative a there.
Its total degree is n-1. Subtract the appropriately signed total boundary of
a. Its vertical boundary vanishes; its horizontal boundary changes only column
-s, making that component a vertical boundary. Choose a primitive t in vertical
degree q-1 in column -s, and subtract its signed total boundary. This kills
column -s and changes only column 1-s in addition. The difference remains a
cycle because the square of the total differential is zero. Call it z' and
write its remaining coordinates as x' from column 0 through -r. Let b be the
sum of these two signed corrections. Then z = z' + d(b), as asserted. No
iteration, column-zero identification, or choice of descent measure is used. -/
theorem total_resolution_cycle_support_step
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_homology : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom)
    (r : ℕ) (z : (K.total (ComplexShape.up ℤ)).cycles n)
    (x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)))
    (hx : (K.total (ComplexShape.up ℤ)).iCycles n z =
      ∑ i ∈ Finset.range (r + 1 + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i)) :
    ∃ z' : (K.total (ComplexShape.up ℤ)).cycles n,
      ∃ x' : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
      ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z' =
          (∑ i ∈ Finset.range (r + 1),
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x' i)) ∧
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          (K.total (ComplexShape.up ℤ)).iCycles n z' +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
  classical
  obtain ⟨y, hy, hker⟩ := outer_cycle K n r z x hx
  let p : ℤ := -((r + 1 : ℕ) : ℤ)
  let q : ℤ := n + ((r + 1 : ℕ) : ℤ)
  have he := h_homology (p - 1) q (by dsimp [p]; omega)
  have he₁ : p - 1 + 1 = p := by omega
  have he₂ : p - 1 + 2 = p + 1 := by omega
  rw [he₁, he₂] at he
  have hb := outer_boundary K p q n (by dsimp [p, q]; omega) y he hker
  dsimp only [p, q] at hb
  rw [hy] at hb
  have hp : -((r + 1 : ℕ) : ℤ) + 1 = -(r : ℤ) := by omega
  have hq : n + ((r + 1 : ℕ) : ℤ) - 1 = n + (r : ℤ) := by omega
  rw [hp, hq] at hb
  obtain ⟨b, w, hb⟩ := hb
  let x' : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)) :=
    Function.update x r (x r - w)
  have hs :
      (∑ i ∈ Finset.range (r + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x' i)) =
      (∑ i ∈ Finset.range (r + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i)) -
      K.ιTotalOrZero (ComplexShape.up ℤ) (-(r : ℤ)) (n + (r : ℤ)) n w := by
    calc
      _ = ∑ i ∈ Finset.range (r + 1),
          (K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i) -
            if i = r then
              K.ιTotalOrZero (ComplexShape.up ℤ) (-(r : ℤ)) (n + (r : ℤ)) n w
            else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i = r
        · subst i
          simp [x', map_sub]
        · simp [x', h]
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp
  let v := (K.total (ComplexShape.up ℤ)).iCycles n z -
    (K.total (ComplexShape.up ℤ)).d (n - 1) n b
  have hv : (K.total (ComplexShape.up ℤ)).d n (n + 1) v = 0 := by
    dsimp [v]
    rw [map_sub]
    have hz := congrArg (fun f ↦ f z)
      ((K.total (ComplexShape.up ℤ)).iCycles_d n (n + 1))
    change (K.total (ComplexShape.up ℤ)).d n (n + 1)
      ((K.total (ComplexShape.up ℤ)).iCycles n z) = 0 at hz
    have hdb := congrArg (fun f ↦ f b)
      ((K.total (ComplexShape.up ℤ)).d_comp_d (n - 1) n (n + 1))
    change (K.total (ComplexShape.up ℤ)).d n (n + 1)
      ((K.total (ComplexShape.up ℤ)).d (n - 1) n b) = 0 at hdb
    rw [hz, hdb, sub_self]
  let z' : (K.total (ComplexShape.up ℤ)).cycles n :=
    ((K.total (ComplexShape.up ℤ)).sc n).cyclesMk v (by
      change (K.total (ComplexShape.up ℤ)).d n ((ComplexShape.up ℤ).next n) v = 0
      rw [CochainComplex.next]
      exact hv)
  have hz' : (K.total (ComplexShape.up ℤ)).iCycles n z' = v :=
    ((K.total (ComplexShape.up ℤ)).sc n).i_cyclesMk v _
  refine ⟨z', x', b, ?_, ?_⟩
  · rw [hz', hs]
    dsimp [v]
    rw [hx, Finset.sum_range_succ, hb]
    abel
  · rw [hz']
    dsimp [v]
    abel

end WeilConjectures.DerivedTotalResolution
