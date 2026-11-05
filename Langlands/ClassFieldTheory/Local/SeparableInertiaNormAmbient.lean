import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring
import Langlands.ClassFieldTheory.Local.SeparableInertiaNormReduction
import Langlands.Galois.Local.SeparableUnramifiedArithmeticProof

/-! # Unit norm surjectivity inside a Galois ambient field

Let `Ω / U` be a Galois extension, possibly infinite, and let `w` be a real valuation on `Ω`
that is invariant under `Gal(Ω/U)`. Assume that `w` satisfies Hensel's lemma for simple roots
on `Ω`, that its restriction to `U` has root finding modulo the maximal ideal, and that this
restriction has a uniformizer. Then for every finite extension `E` of `U` inside `Ω` and every
finite extension `L` of `E` inside `Ω`, every unit of `E` is the norm of a unit of `L`.

The first part converts the ring-theoretic hypotheses (Henselian valuation ring, algebraically
closed residue field, discrete valuation ring) into the valuation-theoretic hypotheses of the
earlier modules. It also proves that some prime `p` has the property that every integer prime
to `p` has value `1`. The second part applies the reduction theorem to the normal closure of
`L / E` in `Ω`.
-/

noncomputable section

open Polynomial Module IsLocalRing
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

section Field

variable {K : Type*} [Field K]

/-- A polynomial with integral coefficients lifts to the valuation ring. -/
theorem exists_lift {v : Valuation K ℝ≥0} {f : K[X]} (hf : IntPoly v f) :
    ∃ g : v.valuationSubring[X], g.map (algebraMap v.valuationSubring K) = f :=
  (mem_lifts f).mp ((lifts_iff_coeff_lifts f).mpr fun n => ⟨⟨f.coeff n, hf n⟩, rfl⟩)

theorem eval_lift {v : Valuation K ℝ≥0} (g : v.valuationSubring[X]) (b : v.valuationSubring) :
    (g.map (algebraMap v.valuationSubring K)).eval (b : K) =
      ((g.eval b : v.valuationSubring) : K) := by
  rw [eval_map, ← ValuationSubring.algebraMap_apply, eval₂_hom]
  rfl

/-- A Henselian valuation ring satisfies simple-root Hensel lifting. -/
theorem valHensel_of_henselian (v : Valuation K ℝ≥0) [HenselianLocalRing v.valuationSubring] :
    ValHensel v := by
  intro f hmon hint a₀ ha₀ hev hder
  obtain ⟨g, hg⟩ := exists_lift hint
  have hinj : Function.Injective (algebraMap v.valuationSubring K) := fun a b h =>
    Subtype.ext h
  have hgm : g.Monic := monic_of_injective hinj (by rw [hg]; exact hmon)
  set a : v.valuationSubring := ⟨a₀, ha₀⟩
  have hev' : g.eval a ∈ maximalIdeal v.valuationSubring := by
    rw [Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt, ← eval_lift, hg]
    exact hev
  have hder' : IsUnit (g.derivative.eval a) := by
    rw [Langlands.LocalGalois.Separable.isUnit_iff_eq_one, ← eval_lift, ← derivative_map, hg]
    exact hder
  obtain ⟨b, hb, hsub⟩ := HenselianLocalRing.is_henselian g hgm a hev' hder'
  refine ⟨b, ?_, ?_⟩
  · rw [← hg, eval_lift, hb.eq_zero]
    rfl
  · rw [Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt] at hsub
    exact hsub

/-- An algebraically closed residue field gives root finding modulo the maximal ideal. -/
theorem valResidueRoot_of_isAlgClosed (v : Valuation K ℝ≥0)
    [IsAlgClosed (ResidueField v.valuationSubring)] : ValResidueRoot v := by
  intro f hint ⟨i0, hi0, hu⟩
  obtain ⟨g, hg⟩ := exists_lift hint
  set gb := g.map (residue v.valuationSubring) with hgb
  have hunit : IsUnit (g.coeff i0) := by
    rw [Langlands.LocalGalois.Separable.isUnit_iff_eq_one]
    rw [← hg, coeff_map] at hu
    exact hu
  have hne : gb.coeff i0 ≠ 0 := by
    rw [hgb, coeff_map]
    exact (residue_ne_zero_iff_isUnit _).mpr hunit
  have hdeg : gb.degree ≠ 0 := by
    intro h0
    have := le_degree_of_ne_zero hne
    rw [h0] at this
    have : i0 ≤ 0 := by exact_mod_cast this
    omega
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root gb hdeg
  obtain ⟨b, rfl⟩ := residue_surjective r
  refine ⟨b, b.2, ?_⟩
  have hres : residue v.valuationSubring (g.eval b) = 0 := by
    rw [← hr.eq_zero, hgb, eval_map, eval₂_hom]
  rw [residue_eq_zero_iff, Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt, ← eval_lift, hg] at hres
  exact hres

/-- The valuation ring of a discrete valuation ring has a uniformizer. -/
theorem exists_valUniformizer_of_dvr (v : Valuation K ℝ≥0)
    [IsDiscreteValuationRing v.valuationSubring] : ∃ π : K, ValUniformizer v π := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨ϖ, ?_, ?_, fun b hb0 hb1 => ?_⟩
  · rw [pos_iff_ne_zero, Ne, Valuation.zero_iff]
    exact hϖ0
  · rw [← Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt]
    exact hϖ.not_isUnit
  · set b' : v.valuationSubring := ⟨b, hb1⟩
    have hb' : b' ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb' hϖ
    refine ⟨n, ?_⟩
    have hb : b = ((u : v.valuationSubring) : K) * (ϖ : K) ^ n := by
      rw [show b = (b' : K) from rfl, hu]
      rfl
    rw [hb, map_mul, map_pow, (Langlands.LocalGalois.Separable.isUnit_iff_eq_one v _).mp u.isUnit, one_mul]

/-- Some prime `p` has the property that every natural number prime to `p` has value `1`:
the residue characteristic if it is positive, and any prime otherwise. -/
theorem exists_prime_natCast (v : Valuation K ℝ≥0) :
    ∃ p : ℕ, p.Prime ∧ ∀ m : ℕ, ¬ p ∣ m → v (m : K) = 1 := by
  classical
  by_cases hS : ∃ m : ℕ, 0 < m ∧ v (m : K) < 1
  · obtain ⟨hp0, hpv⟩ := Nat.find_spec hS
    set p := Nat.find hS
    have hmin : ∀ m : ℕ, 0 < m → m < p → v (m : K) = 1 := fun m hm hmp =>
      le_antisymm (val_natCast_le_one m) (not_lt.mp fun h => Nat.find_min hS hmp ⟨hm, h⟩)
    have hp1 : p ≠ 1 := by
      intro h
      rw [h, Nat.cast_one, map_one] at hpv
      exact lt_irrefl _ hpv
    have hprime : p.Prime := by
      refine Nat.prime_def_lt.mpr ⟨by omega, fun m hmp hmd => ?_⟩
      by_contra hm1
      obtain ⟨k, hk⟩ := hmd
      have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hk; omega
      have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
      have hkp : k < p := by
        rw [hk]
        exact lt_mul_left hk0 (by omega)
      have : v (p : K) = 1 := by
        rw [hk, Nat.cast_mul, map_mul, hmin m hm0 hmp, hmin k hk0 hkp, one_mul]
      exact (ne_of_lt hpv) this
    refine ⟨p, hprime, fun m hm => ?_⟩
    have hr0 : 0 < m % p := Nat.pos_of_ne_zero fun h => hm (Nat.dvd_of_mod_eq_zero h)
    have hvr : v ((m % p : ℕ) : K) = 1 := hmin _ hr0 (Nat.mod_lt _ hp0)
    have hdec : (m : K) = ((m % p : ℕ) : K) + (p : K) * ((m / p : ℕ) : K) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    have hlt : v ((p : K) * ((m / p : ℕ) : K)) < v ((m % p : ℕ) : K) := by
      rw [hvr, map_mul]
      exact (mul_le_of_le_one_right zero_le (val_natCast_le_one _)).trans_lt hpv
    rw [hdec, Valuation.map_add_eq_of_lt_left _ hlt, hvr]
  · push Not at hS
    refine ⟨2, Nat.prime_two, fun m hm => ?_⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hm (h ▸ dvd_zero 2)
    exact le_antisymm (val_natCast_le_one m) (hS m hm0)

theorem IntPoly.mul {v : Valuation K ℝ≥0} {f g : K[X]} (hf : IntPoly v f) (hg : IntPoly v g) :
    IntPoly v (f * g) := fun i => by
  rw [coeff_mul]
  exact v.map_sum_le fun x _ => by rw [map_mul]; exact mul_le_one' (hf _) (hg _)

theorem IntPoly.multiset_prod_X_sub_C {v : Valuation K ℝ≥0} (s : Multiset K)
    (hs : ∀ r ∈ s, v r ≤ 1) : IntPoly v (s.map fun r => X - C r).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using IntPoly.X_pow (v := v) 0
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine IntPoly.mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr))
    have : (X - C a : K[X]) = X ^ 1 + C (-a) * X ^ 0 := by
      rw [pow_one, pow_zero, mul_one, C_neg, sub_eq_add_neg]
    rw [this]
    refine (IntPoly.X_pow 1).add (IntPoly.C_mul_X_pow ?_ 0)
    rw [Valuation.map_neg]
    exact hs a (Multiset.mem_cons_self a s)

end Field

section Conjugates

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω]
  [IsScalarTower K L Ω] {w : Valuation Ω ℝ≥0}

/-- All roots of the minimal polynomial of `y` have the value of `y`. -/
theorem val_eq_of_mem_aroots [Normal K Ω] (hinv : ∀ (σ : Gal(Ω/K)) (y : Ω), w (σ y) = w y)
    {y r : Ω} (hr : r ∈ (minpoly K y).aroots Ω) : w r = w y := by
  rw [mem_aroots] at hr
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic (R := K) y) hr.2
  rw [← hσ, hinv]

/-- The value of a norm, for a finite extension `L / K` inside a normal extension `Ω / K` with
an invariant valuation. -/
theorem val_norm_eq [Normal K Ω] [FiniteDimensional K L]
    (hinv : ∀ (σ : Gal(Ω/K)) (y : Ω), w (σ y) = w y) (x : L) :
    w (algebraMap K Ω (Algebra.norm K x)) = w (algebraMap L Ω x) ^ finrank K L := by
  set y := algebraMap L Ω x
  have hmin : minpoly K y = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap L Ω).injective x
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hsplit : ((minpoly K x).map (algebraMap K Ω)).Splits :=
    hmin ▸ Normal.splits inferInstance y
  rw [Algebra.norm_eq_prod_roots Ω hsplit, map_pow, map_multiset_prod]
  have hroots : ∀ r ∈ (minpoly K x).aroots Ω, w r = w y := fun r hr =>
    val_eq_of_mem_aroots hinv (hmin ▸ hr)
  rw [Multiset.map_congr rfl hroots, Multiset.map_const', Multiset.prod_replicate, ← pow_mul]
  congr 1
  rw [aroots, ← hsplit.natDegree_eq_card_roots, natDegree_map,
    ← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank]

end Conjugates

/-! ### The ambient hypotheses -/

variable {U Ω : Type*} [Field U] [Field Ω] [Algebra U Ω] [IsGalois U Ω]

/-- Hypotheses on a valuation of a Galois extension `Ω / U`. -/
structure AmbientHyp (w : Valuation Ω ℝ≥0) : Prop where
  inv : ∀ (σ : Gal(Ω/U)) (x : Ω), w (σ x) = w x
  hensel : ValHensel w
  residueRoot : ValResidueRoot (w.comap (algebraMap U Ω))
  unif : ∃ π : U, ValUniformizer (w.comap (algebraMap U Ω)) π

namespace AmbientHyp

variable {w : Valuation Ω ℝ≥0} (h : AmbientHyp (U := U) w)

include h

omit [IsGalois U Ω] in
/-- Invariance under `Gal(Ω/K)` for every intermediate field `K` of a tower `U → K → Ω`. -/
theorem inv_of {K : Type*} [Field K] [Algebra U K] [Algebra K Ω] [IsScalarTower U K Ω]
    (σ : Gal(Ω/K)) (x : Ω) : w (σ x) = w x :=
  h.inv (σ.restrictScalars U) x

/-- Every integral element of `Ω` is congruent modulo the maximal ideal to an integral element
of `U`. -/
theorem res (x : Ω) (hx : w x ≤ 1) :
    ∃ c : U, w (algebraMap U Ω c) ≤ 1 ∧ w (x - algebraMap U Ω c) < 1 := by
  classical
  set f := minpoly U x with hf
  have hint : IsIntegral U x := Algebra.IsIntegral.isIntegral x
  have hsplit : (f.map (algebraMap U Ω)).Splits := Normal.splits inferInstance x
  have hmon : (f.map (algebraMap U Ω)).Monic := (minpoly.monic hint).map _
  have hroots : ∀ r ∈ (f.map (algebraMap U Ω)).roots, w r = w x := fun r hr =>
    val_eq_of_mem_aroots (K := U) h.inv hr
  have hprod := hsplit.eq_prod_roots_of_monic hmon
  have hfint : IntPoly (w.comap (algebraMap U Ω)) f := by
    intro i
    rw [Valuation.comap_apply, ← coeff_map, hprod]
    exact IntPoly.multiset_prod_X_sub_C _ (fun r hr => (hroots r hr).trans_le hx) i
  have hdeg : 0 < f.natDegree := minpoly.natDegree_pos hint
  have hfm : f.Monic := minpoly.monic hint
  obtain ⟨b, hb1, hb2⟩ := h.residueRoot f hfint ⟨f.natDegree, hdeg, by
    rw [Valuation.comap_apply, hfm.coeff_natDegree, map_one, map_one]⟩
  rw [Valuation.comap_apply] at hb1 hb2
  refine ⟨b, hb1, ?_⟩
  set b' := algebraMap U Ω b
  have hev : algebraMap U Ω (f.eval b) =
      ((f.map (algebraMap U Ω)).roots.map fun r => b' - r).prod := by
    rw [← hsplit.eval_eq_prod_roots_of_monic hmon, eval_map, eval₂_hom]
  rw [hev, map_multiset_prod, Multiset.map_map] at hb2
  by_contra hne
  apply (ne_of_lt hb2)
  refine Multiset.prod_eq_one fun t ht => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp ht
  rw [Function.comp_apply]
  have hr' : r ∈ (minpoly U x).aroots Ω := hr
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic (R := U) x) (mem_aroots.mp hr').2
  have hb'σ : b' - r = σ (b' - x) := by
    rw [map_sub, ← hσ, AlgEquiv.commutes]
  have hle : w (b' - r) ≤ 1 := (w.map_sub _ _).trans
    (max_le hb1 ((hroots r hr).trans_le hx))
  refine le_antisymm hle (not_lt.mp fun hlt => hne ?_)
  rw [hb'σ, h.inv, Valuation.map_sub_swap] at hlt
  exact hlt

/-- **Unit norm surjectivity for a tower.** Let `U → E → L → M → Ω` be a tower with `E / U`
and `M / E` finite and `M / E` Galois. Every unit of `E` is the norm of a unit of `L`. -/
theorem exists_norm_eq_of_tower {E L M : Type*} [Field E] [Field L] [Field M]
    [Algebra U E] [Algebra E Ω] [IsScalarTower U E Ω] [FiniteDimensional U E]
    [Algebra E L] [Algebra L Ω] [IsScalarTower E L Ω]
    [Algebra E M] [Algebra L M] [Algebra M Ω] [IsScalarTower E L M] [IsScalarTower L M Ω]
    [IsScalarTower E M Ω] [FiniteDimensional E M] [IsGalois E M]
    (u : E) (hu : w (algebraMap E Ω u) = 1) :
    ∃ x : L, w (algebraMap L Ω x) = 1 ∧ Algebra.norm E x = u := by
  have hEΩ : IsGalois E Ω := IsGalois.tower_top_of_isGalois U E Ω
  have hLΩ : IsGalois L Ω := IsGalois.tower_top_of_isGalois E L Ω
  have hMΩ : IsGalois M Ω := IsGalois.tower_top_of_isGalois E M Ω
  have hLM : FiniteDimensional L M := Module.Finite.right E L M
  have hcomp : (w.comap (algebraMap M Ω)).comap (algebraMap E M) =
      w.comap (algebraMap E Ω) := by
    rw [← Valuation.comap_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨p, hp, hpm⟩ := exists_prime_natCast (w.comap (algebraMap M Ω))
  obtain ⟨ϖ, hϖ⟩ := h.unif
  have hR : ReductionHyp (E := E) (w.comap (algebraMap M Ω)) p := by
    refine ⟨fun σ x => ?_, hp, hpm, ?_, ?_, fun x hx => ?_, ?_, ?_⟩
    · simp only [Valuation.comap_apply]
      rw [← AlgEquiv.liftNormal_commutes σ Ω x, h.inv_of]
    · exact valHensel_comap h.hensel (fun σ x => h.inv_of (σ.restrictScalars E) x)
        fun x hx => (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx
    · rw [hcomp]
      exact valResidueRoot_comap h.residueRoot h.res
    · obtain ⟨c, hc1, hc2⟩ := h.res (algebraMap M Ω x) hx
      refine ⟨algebraMap U E c, ?_, ?_⟩
      · simp only [Valuation.comap_apply]
        rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      · simp only [Valuation.comap_apply]
        rwa [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    · refine ⟨finrank E M * finrank U E, Nat.mul_pos finrank_pos finrank_pos,
        (w.comap (algebraMap U Ω)) ϖ, hϖ.1, hϖ.2.1, fun x hx0 hx1 => ?_⟩
      have hc : w (algebraMap U Ω (Algebra.norm U (Algebra.norm E x))) =
          (w.comap (algebraMap M Ω)) x ^ (finrank E M * finrank U E) := by
        rw [val_norm_eq h.inv, val_norm_eq (fun σ y => h.inv_of σ y) x, pow_mul]
        rfl
      have hc0 : Algebra.norm U (Algebra.norm E x) ≠ 0 := by
        rw [Ne, Algebra.norm_eq_zero_iff, Algebra.norm_eq_zero_iff]
        exact hx0
      have hc1 : (w.comap (algebraMap U Ω)) (Algebra.norm U (Algebra.norm E x)) ≤ 1 := by
        rw [Valuation.comap_apply, hc]
        exact pow_le_one₀ zero_le hx1
      obtain ⟨k, hk⟩ := hϖ.2.2 _ hc0 hc1
      exact ⟨k, by rw [← hc, ← hk]; rfl⟩
    · refine ⟨algebraMap U E ϖ, ?_, ?_⟩
      · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact hϖ.1
      · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact hϖ.2.1
  obtain ⟨z, hz, hzN⟩ := hR.exists_norm_eq u (by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
    exact hu)
  refine ⟨Algebra.norm L z, ?_, ?_⟩
  · rw [val_norm_eq (K := L) (L := M) (fun σ y => h.inv_of (σ.restrictScalars E) y) z]
    change (w.comap (algebraMap M Ω)) z ^ _ = 1
    rw [hz, one_pow]
  · rw [Algebra.norm_norm, hzN]

/-- **Unit norm surjectivity.** For a finite extension `E` of `U` inside `Ω` and a finite
extension `L` of `E` inside `Ω`, every unit of `E` is the norm of a unit of `L`. -/
theorem exists_norm_eq (E : IntermediateField U Ω) [FiniteDimensional U E]
    (L : IntermediateField E Ω) [FiniteDimensional E L] (u : E) (hu : w (u : Ω) = 1) :
    ∃ x : L, w (x : Ω) = 1 ∧ Algebra.norm E x = u := by
  have hEΩ : IsGalois E Ω := IsGalois.tower_top_of_isGalois U E Ω
  exact h.exists_norm_eq_of_tower (M := IntermediateField.normalClosure E L Ω) u hu

end AmbientHyp

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
