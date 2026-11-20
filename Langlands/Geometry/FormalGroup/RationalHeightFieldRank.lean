import Langlands.Geometry.FormalGroup.IsogenyDual
import Langlands.Geometry.FormalGroup.RationalHeightRankCongruence
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Field ranks of kernels of finite-height formal-module isogenies -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory FiniteKernelComposition MvPolynomial
open RationalHeightJets RationalHeightLinearization RationalHeightRankCongruence

attribute [local instance] coefficientAlgebra coefficientScalarTower

section Arithmetic

private theorem pow_pow_of_dvd_of_modEq {p s D j : ℕ} (hp : p.Prime) (hs : 0 < s)
    (hd : D ∣ (p ^ s) ^ j) (hc : D ≡ 1 [MOD p ^ s - 1]) :
    ∃ h : ℕ, D = (p ^ s) ^ h := by
  rw [← pow_mul] at hd
  obtain ⟨a, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hq := one_lt_pow₀ hp.one_lt hs.ne'
  have hbase : p ^ s ≡ 1 [MOD p ^ s - 1] := Nat.modEq_sub hq.le
  have he : p ^ a = p ^ (a % s) * (p ^ s) ^ (a / s) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  have hr : p ^ (a % s) ≡ 1 [MOD p ^ s - 1] := by
    have h := (Nat.ModEq.refl (p ^ (a % s))).mul (hbase.pow (a / s))
    rw [← he, one_pow, mul_one] at h
    exact h.symm.trans hc
  have hlt := pow_lt_pow_right₀ hp.one_lt (Nat.mod_lt a hs)
  have hz := Nat.eq_zero_of_dvd_of_lt hr.symm.dvd' (show p ^ (a % s) - 1 < p ^ s - 1 by omega)
  have hrem : a % s = 0 := by
    by_contra hne
    have := one_lt_pow₀ hp.one_lt hne
    omega
  exact ⟨a / s, by rw [he, hrem, pow_zero, one_mul]⟩

end Arithmetic

section Divisibility

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {k : Type v} [Field k] [Algebra O k]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ} {π : O} {q d : ℕ}

private def residueToField (hπ : Irreducible π) (hπk : algebraMap O k π = 0) :
    IsLocalRing.ResidueField O →+* k :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O k) fun x hx => by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, hπk, zero_mul]

@[simp]
private theorem residueToField_residue (hπ : Irreducible π) (hπk : algebraMap O k π = 0) (a : O) :
    residueToField hπ hπk (IsLocalRing.residue O a) = algebraMap O k a := rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem fieldKernelRank_dvd (hM : M.HasPiHeight π q d) (hN : N.IsPiDivisible π)
    {f : Hom M N} (hf : f.IsIsogeny) (K : Hom.FiniteKernelModel f) :
    ∃ j : ℕ, Module.finrank k K.coordinateAlgebra ∣ q ^ j := by
  obtain ⟨j, hj⟩ := hf.exists_dual hM.1 hN
  obtain ⟨g, hg, hgf, _⟩ := hj j le_rfl
  obtain ⟨L⟩ := hg.2
  obtain ⟨H, hH⟩ := Hom.finiteKernelCompositionStatement M N M f g hf.1 K L
  obtain ⟨J, hJ⟩ := hM.scalarPower_rank j
  let p : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  have compare {a b : Hom M M} (hab : a = b)
      (A : a.FiniteKernelModel) (B : b.FiniteKernelModel) : A.rank p = B.rank p := by
    subst b
    exact congrFun (A.rank_eq B) p
  have hK : K.rank p = Module.finrank k K.coordinateAlgebra :=
    congrFun Module.rankAtStalk_eq_finrank_of_free p
  refine ⟨j * d, L.rank p, ?_⟩
  rw [← hJ p, ← compare hgf H J, hH, hK]

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem card_eq_of_isogeny {p : ℕ} [ExpChar k p] (hp : 1 < p)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {f : Hom M N} (hf : f.IsIsogeny) (K : Hom.FiniteKernelModel f) :
    Nat.card σ = Nat.card τ := by
  obtain ⟨j, hj⟩ := hf.exists_dual hM hN
  obtain ⟨g, hg, _, _⟩ := hj j le_rfl
  obtain ⟨L⟩ := hg.2
  exact le_antisymm (RationalHeightJets.card_le_of_finiteKernel hp K)
    (RationalHeightJets.card_le_of_finiteKernel hp L)

private theorem exists_scalar_lift [Fintype (IsLocalRing.ResidueField O)]
    (hπ : Irreducible π) (c : IsLocalRing.ResidueField O)
    (hc : c ^ (Fintype.card (IsLocalRing.ResidueField O) - 1) = 1) (t : ℕ) :
    ∃ a : O, IsLocalRing.residue O a = c ∧
      π ^ t ∣ a ^ (Fintype.card (IsLocalRing.ResidueField O) - 1) - 1 := by
  let q := Fintype.card (IsLocalRing.ResidueField O)
  change c ^ (q - 1) = 1 at hc
  let ρ := IsLocalRing.residue O
  have hdvd {b : O} (hb : ρ b = 0) : π ∣ b := by
    have hm := (IsLocalRing.residue_eq_zero_iff b).mp hb
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  induction t with
  | zero =>
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := O) c
    exact ⟨a, ha, by simp⟩
  | succ t ih =>
    obtain ⟨a, ha, ht⟩ := ih
    change ρ a = c at ha
    refine ⟨a ^ q, by rw [map_pow, ha, FiniteField.pow_card], ?_⟩
    have he : (a ^ q) ^ (q - 1) = (a ^ (q - 1)) ^ q := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have hb : π ∣ ∑ i ∈ Finset.range q, (a ^ (q - 1)) ^ i := by
      apply hdvd
      rw [map_sum]
      simp only [map_pow, ha, hc, one_pow, Finset.sum_const, Finset.card_range, nsmul_one]
      exact FiniteField.cast_card_eq_zero (IsLocalRing.ResidueField O)
    rw [he, ← mul_geom_sum, pow_succ]
    exact mul_dvd_mul ht hb

/-- The field-valued kernel rank of an isogeny between strict, divisible formal
modules is a power of the actual residue cardinality when the source has finite
height with that normalization. -/
theorem Hom.finrank_finiteKernel_eq_pow_residueCard [Finite (IsLocalRing.ResidueField O)]
    (hπ : Irreducible π) (hM : M.HasPiHeight π (Nat.card (IsLocalRing.ResidueField O)) d)
    (hN : N.IsPiDivisible π) {f : Hom M N} (hf : f.IsIsogeny) (K : Hom.FiniteKernelModel f) :
    ∃ h : ℕ, Module.finrank k K.coordinateAlgebra = (Nat.card (IsLocalRing.ResidueField O)) ^ h := by
  classical
  let κ := IsLocalRing.ResidueField O
  let : Fintype κ := Fintype.ofFinite κ
  let q := Fintype.card κ
  have hqNat : Nat.card κ = q := Nat.card_eq_fintype_card
  change ∃ h : ℕ, Module.finrank k K.coordinateAlgebra = (Nat.card κ) ^ h
  rw [hqNat]
  have hq : 1 < q := Fintype.one_lt_card
  obtain ⟨p, hpκ, s, hp, hqPow⟩ := FiniteField.card' κ
  change q = p ^ (s : ℕ) at hqPow
  let ρ := residueToField hπ hM.1.base_nilpotent.eq_zero
  let : CharP κ p := hpκ
  let : CharP k p := charP_of_injective_ringHom ρ.injective p
  let : ExpChar k p := ExpChar.prime hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
  have hgOrder : orderOf (g : κ) = q - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hqNat]
  have hgPow : (g : κ) ^ (q - 1) = 1 := by rw [← hgOrder, pow_orderOf_eq_one]
  let c := ρ (g : κ)
  have hcOrder : orderOf c = q - 1 := by
    change orderOf (ρ.toMonoidHom (g : κ)) = _
    rw [orderOf_injective _ ρ.injective, hgOrder]
  have hc : c ^ (q - 1) = 1 := by rw [← hcOrder, pow_orderOf_eq_one]
  have hc₀ : c ≠ 0 := fun h => g.ne_zero (ρ.injective (h.trans (map_zero ρ).symm))
  have hq₀ : (q : k) = 0 := by
    have h := congrArg ρ (FiniteField.cast_card_eq_zero κ)
    simpa only [map_natCast, map_zero] using h
  have hm : ((q - 1 : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_sub hq.le, hq₀, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨b₀, hb₀⟩ := exists_kernel_bound K.represents
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (max 1 (b₀ + 1)) hp.one_lt
  have hb₁ : 1 < p ^ b := (le_max_left 1 (b₀ + 1)).trans_lt hb
  have hwidth : 2 * p ^ b ≤ p ^ (b + 1) := by
    rw [pow_succ, mul_comm (p ^ b) p]
    exact Nat.mul_le_mul_right _ hp.two_le
  have hle : p ^ b ≤ p ^ (b + 1) := by omega
  have hdeep : 1 < p ^ (b + 1) := hb₁.trans_le hle
  have rank_at_width (w : ℕ) (hw : b₀ + 1 ≤ w) :
      Module.finrank k (kerAlg f w) = Module.finrank k K.coordinateAlgebra :=
    finrank_kerAlg_eq K fun A x hx i => pow_eq_zero_of_le hw (hb₀ A x hx i)
  obtain ⟨tM, htM⟩ := hM.1.torsion _ (truncPoint M (p ^ (b + 1)))
  obtain ⟨tN, htN⟩ := hN.torsion _ (truncPoint N (p ^ (b + 1)))
  obtain ⟨a, ha, hadvd⟩ := exists_scalar_lift hπ (g : κ) hgPow (max tM tN)
  have ha' : algebraMap O k a = c := by
    change ρ (IsLocalRing.residue O a) = ρ (g : κ)
    rw [ha]
  have fixed {ι : Type} [Finite ι] (P : ModuleLaw O k ι) {A : CommAlgCat.{v} k}
      (z : P.AlgebraPoint A) {t : ℕ} (ht : t ≤ max tM tN)
      (hz : π ^ t • z = 0) : a ^ (q - 1) • z = z := by
    obtain ⟨y, hy⟩ := (pow_dvd_pow π ht).trans hadvd
    have hzero : (a ^ (q - 1) - 1) • z = 0 := by
      rw [hy, mul_comm, mul_smul, hz, smul_zero]
    simpa only [sub_smul, one_smul, sub_eq_zero] using hzero
  obtain ⟨F, hF, hFr⟩ := exists_equivariant_equations hdeep f a ha' hm hc hc₀
    (fixed M _ (le_max_left _ _) htM) (fixed N _ (le_max_right _ _) htN)
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype τ := Fintype.ofFinite τ
  let E : σ ≃ τ := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card] using card_eq_of_isogeny hp.one_lt hM.1 hN hf K)
  let G (i : σ) := F (E i)
  have hG (w : ℕ) : Set.range (fun i => truncProj k σ w (G i)) =
      Set.range (fun i => truncProj k σ w (F i)) := by
    ext z
    exact ⟨fun ⟨i, hi⟩ => ⟨E i, hi⟩, fun ⟨i, hi⟩ =>
      ⟨E.symm i, by simpa only [G, E.apply_symm_apply] using hi⟩⟩
  have hr (j : ℕ) (hj : 1 < p ^ j) (hjle : p ^ j ≤ p ^ (b + 1)) (hj' : b₀ + 1 ≤ p ^ j) :
      Module.finrank k (truncAlg k σ (p ^ j) ⧸
        Ideal.span (Set.range fun i => truncProj k σ (p ^ j) (G i))) =
        Module.finrank k K.coordinateAlgebra := by
    rw [hG, hFr j hj hjle, rank_at_width _ hj']
  obtain ⟨l, hl⟩ := pow_unbounded_of_one_lt
    (max (p ^ (b + 1)) (Finset.univ.sup fun i : σ => (G i).totalDegree)) hq
  have hL : p ^ (b + 1) ≤ q ^ l := (le_max_left _ _).trans hl.le
  have hdeg (i : σ) : (G i).totalDegree < q ^ l :=
    ((Finset.le_sup (f := fun j => (G j).totalDegree) (Finset.mem_univ i)).trans
      (le_max_right _ _)).trans_lt hl
  have hLmod : q ^ l ≡ 1 [MOD q - 1] := by
    simpa only [one_pow] using (Nat.modEq_sub hq.le).pow l
  have hcL : c ^ (q ^ l) = c := (pow_eq_pow_of_modEq hLmod hc).trans (pow_one _)
  have hbwidth : b₀ + 1 ≤ p ^ b := (le_max_right _ _).trans hb.le
  have hcong := finrank_modEq_of_equivariant_equations G hc₀ (fun i => hF (E i))
    (show 0 < p ^ b from zero_lt_one.trans hb₁) hwidth hL hdeg hcL
    (hr b hb₁ hle hbwidth) (hr (b + 1) hdeep le_rfl (hbwidth.trans hle))
  rw [hcOrder] at hcong
  have hD : Module.finrank k K.coordinateAlgebra ≡ 1 [MOD q - 1] :=
    hcong.symm.trans (by simpa only [one_pow] using hLmod.pow (Nat.card σ))
  obtain ⟨j, hj⟩ := fieldKernelRank_dvd hM hN hf K
  change Module.finrank k K.coordinateAlgebra ∣ (Nat.card κ) ^ j at hj
  rw [hqNat, hqPow] at hj
  rw [hqPow] at hD ⊢
  exact pow_pow_of_dvd_of_modEq hp s.pos hj hD

end Divisibility

end Langlands.FormalGroup.ModuleLaw
