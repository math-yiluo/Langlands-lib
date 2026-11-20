import Langlands.Geometry.FormalGroup.RationalHeightLinearization
import Langlands.Representation.Archimedean.Kostant.CoprimeGroebner
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Nat.ModEq
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Rank congruence for the finite quotients of equivariant kernel equations -/

noncomputable section

universe v

namespace Langlands.FormalGroup.ModuleLaw.RationalHeightRankCongruence

open FiniteKernelComposition MvPolynomial RationalHeightJets RationalHeightLinearization
open Langlands.Algebra.PolynomialBoxQuotient
open Langlands.Archimedean.Kostant
open MonomialOrder
open scoped MonomialOrder

variable {k : Type v} [Field k]

section BoxPowers

variable {B : Type*} [CommRing B] [Algebra k B] {σ : Type}

private def boxPowers (x : σ → B) (n : ℕ) : Ideal B :=
  Ideal.span (Set.range fun i => x i ^ n)

private theorem boxPowers_antitone (x : σ → B) : Antitone (boxPowers x) := by
  intro n t hnt
  rw [boxPowers, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  apply (boxPowers x n).mem_of_dvd (pow_dvd_pow (x i) hnt)
  exact Ideal.subset_span (Set.mem_range_self i)

/-- Equal ranks at two widths force all later box ideals to agree, once the
second width is at least twice the first. -/
private theorem boxPowers_eq_of_finrank [Module.Finite k B] [Finite σ]
    (x : σ → B) {n m : ℕ} (hn : 0 < n) (hm : 2 * n ≤ m)
    (hrank : Module.finrank k (B ⧸ boxPowers x n) =
      Module.finrank k (B ⧸ boxPowers x m)) {t : ℕ} (ht : n ≤ t) :
    boxPowers x t = boxPowers x n := by
  let J := boxPowers x n
  let J' := boxPowers x m
  have hle : J' ≤ J := boxPowers_antitone x (by omega)
  have hr₁ := (J.restrictScalars k).finrank_quotient_add_finrank
  have hr₂ := (J'.restrictScalars k).finrank_quotient_add_finrank
  change Module.finrank k (B ⧸ J) + Module.finrank k J = Module.finrank k B at hr₁
  change Module.finrank k (B ⧸ J') + Module.finrank k J' = Module.finrank k B at hr₂
  change Module.finrank k (B ⧸ J) = Module.finrank k (B ⧸ J') at hrank
  have hfin : Module.finrank k (J'.restrictScalars k) =
      Module.finrank k (J.restrictScalars k) := by
    change Module.finrank k J' = Module.finrank k J
    omega
  have hsub := Submodule.eq_of_le_of_finrank_eq
    (show J'.restrictScalars k ≤ J.restrictScalars k from hle) hfin
  have heq : J' = J := SetLike.ext fun y => by
    change y ∈ J'.restrictScalars k ↔ y ∈ J.restrictScalars k
    rw [hsub]
  have hidem : IsIdempotentElem J := by
    change J * J = J
    refine le_antisymm Ideal.mul_le_left ?_
    calc
      J = J' := heq.symm
      _ ≤ J * J := by
        change boxPowers x m ≤ J * J
        rw [boxPowers, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        apply (J * J).mem_of_dvd (pow_dvd_pow (x i) hm)
        rw [two_mul, pow_add]
        have hi : x i ^ n ∈ J := Ideal.subset_span (Set.mem_range_self i)
        exact Ideal.mul_mem_mul hi hi
  let f := Ideal.Quotient.mk (boxPowers x t)
  have hnil : IsNilpotent (J.map f) := by
    have hfg : (J.map f).FG := by
      change (Ideal.map f (Ideal.span _)).FG
      rw [Ideal.map_span]
      exact Submodule.fg_span ((Set.finite_range _).image _)
    refine hfg.isNilpotent_iff_le_nilradical.mpr ?_
    change Ideal.map f (Ideal.span _) ≤ _
    rw [Ideal.map_span, ← Set.range_comp, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change f (x i ^ n) ∈ nilradical _
    rw [map_pow]
    have hx : f (x i) ∈ nilradical _ := mem_nilradical.mpr ⟨t, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩⟩
    exact Ideal.pow_mem_of_mem _ hx n hn
  obtain ⟨b, hb⟩ := hnil
  have hmap : IsIdempotentElem (J.map f) := by
    change J.map f * J.map f = J.map f
    rw [← Ideal.map_mul, hidem.eq]
  have hbot : J.map f = ⊥ := calc
    J.map f = (J.map f) ^ (b + 1) := (hmap.pow_succ_eq b).symm
    _ = ⊥ := by rw [pow_succ, hb, zero_mul]; rfl
  refine le_antisymm (boxPowers_antitone x ht) ?_
  have hh := (Ideal.map_eq_bot_iff_le_ker f).mp hbot
  exact fun y hy => Ideal.Quotient.eq_zero_iff_mem.mp (hh hy)

end BoxPowers

section PolynomialQuotient

variable {σ : Type} [Finite σ]

/-- Adding sufficiently high pure powers gives the same monomial basis as a box.
Division gives spanning and the coprime leading monomials give independence. -/
private theorem finite_perturbation (F : σ → MvPolynomial σ k) {L : ℕ} (hL : 0 < L)
    (hdeg : ∀ i, (F i).totalDegree < L) :
    let I := Ideal.span (Set.range fun i => (X i : MvPolynomial σ k) ^ L + F i)
    Module.Finite k (MvPolynomial σ k ⧸ I) ∧
      Module.finrank k (MvPolynomial σ k ⧸ I) = L ^ Nat.card σ := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let ord := Fintype.equivFin σ
  let : LinearOrder σ := LinearOrder.lift' ord ord.injective
  let m : MonomialOrder σ := degLex
  let G : σ → MvPolynomial σ k := fun i => X i ^ L + F i
  let I := Ideal.span (Set.range G)
  change Module.Finite k (MvPolynomial σ k ⧸ I) ∧
    Module.finrank k (MvPolynomial σ k ⧸ I) = _
  have hlt (i : σ) : m.degree (F i) ≺[m] m.degree ((X i : MvPolynomial σ k) ^ L) := by
    change degLex.degree (F i) ≺[degLex] degLex.degree ((X i : MvPolynomial σ k) ^ L)
    rw [degLex_lt_iff, Finsupp.DegLex.lt_iff]
    left
    simp only [ofDegLex_toDegLex, degree_degLexDegree, totalDegree_X_pow]
    exact hdeg i
  have hd (i : σ) : m.degree (G i) = Finsupp.single i L := by
    change m.degree ((X i : MvPolynomial σ k) ^ L + F i) = _
    rw [m.degree_add_of_lt (hlt i), X_pow_eq_monomial, m.degree_monomial, ite_eq_right one_ne_zero]
  have hm (i : σ) : m.Monic (G i) := by
    change m.leadingCoeff ((X i : MvPolynomial σ k) ^ L + F i) = 1
    rw [m.leadingCoeff_add_of_lt (hlt i), X_pow_eq_monomial]
    exact (m.monic_monomial_one).leadingCoeff_eq_one
  have hdj (i j : σ) (hij : i ≠ j) (a : σ) :
      m.degree (G i) a = 0 ∨ m.degree (G j) a = 0 := by
    rw [hd, hd]
    by_cases h : a = i
    · right
      simp [h, hij]
    · left
      simp [h]
  let N : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => L - 1
  have hN (i : σ) : N i = L - 1 := by simp [N]
  let V := restrictSupport k (Set.Iic N)
  let φ := (Ideal.Quotient.mkₐ k I).toLinearMap.comp V.subtype
  have hinj : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun f hf => by
    have hmem : (f : MvPolynomial σ k) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hf
    apply Subtype.ext
    change (f : MvPolynomial σ k) = 0
    by_contra hne
    obtain ⟨i, hi⟩ := CoprimeGroebner.exists_degree_le m G hm hdj hmem hne
    have hb : m.degree (f : MvPolynomial σ k) ≤ N := by
      have hs : (f : MvPolynomial σ k) ∈ restrictSupport k (Set.Iic N) := f.property
      rw [mem_restrictSupport_iff] at hs
      exact hs (m.degree_mem_support hne)
    have h := hi.trans hb
    rw [hd, Finsupp.single_le_iff, hN] at h
    omega
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
    obtain ⟨q, r, hr, _, hrem⟩ := MonomialOrder.div (m := m) (b := G)
      (fun i => (hm i).leadingCoeff_eq_one ▸ isUnit_one) P
    have hb : r ∈ V := by
      change r ∈ restrictSupport k (Set.Iic N)
      rw [mem_restrictSupport_iff]
      intro d hd'
      change d ≤ N
      intro i
      have hi := hrem d hd' i
      rw [hd, Finsupp.single_le_iff] at hi
      rw [hN]
      omega
    refine ⟨⟨r, hb⟩, ?_⟩
    have hq : Finsupp.linearCombination _ G q ∈ I := by
      change _ ∈ Submodule.span (MvPolynomial σ k) (Set.range G)
      rw [← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ q
    change Ideal.Quotient.mkₐ k I r = Ideal.Quotient.mkₐ k I P
    rw [hr, map_add, show Ideal.Quotient.mkₐ k I (Finsupp.linearCombination _ G q) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hq, zero_add]
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let : Fintype (Set.Iic N) := Fintype.ofFinite _
  let b := basisRestrictSupport k (Set.Iic N)
  let : Module.Finite k V := Module.Finite.of_basis b
  refine ⟨Module.Finite.equiv e, ?_⟩
  have he := (e.symm.trans (b.equivFun.trans (coefficientsEquiv (k := k) N).symm)).finrank_eq
  change Module.finrank k (MvPolynomial σ k ⧸ I) = _
  rw [he]
  change Module.finrank k
    (MvPolynomial σ k ⧸ Langlands.Algebra.PolynomialBoxQuotient.boxIdeal (k := k) N) = _
  rw [← show truncIdeal k σ L = _ from truncIdeal_eq_boxIdeal L hL]
  exact finrank_truncAlg L hL

omit [Finite σ] in
/-- Inside a box of width at most `L`, the perturbing pure powers vanish. -/
private theorem perturbation_box_finrank (F : σ → MvPolynomial σ k) {n L : ℕ}
    (hnL : n ≤ L) :
    let I := Ideal.span (Set.range fun i => (X i : MvPolynomial σ k) ^ L + F i)
    let x := fun i => Ideal.Quotient.mkₐ k I (X i)
    Module.finrank k ((MvPolynomial σ k ⧸ I) ⧸ boxPowers x n) =
      Module.finrank k (truncAlg k σ n ⧸
        Ideal.span (Set.range fun i => truncProj k σ n (F i))) := by
  let I := Ideal.span (Set.range fun i => (X i : MvPolynomial σ k) ^ L + F i)
  let T := truncIdeal k σ n
  let H := Ideal.span (Set.range F)
  let x := fun i => Ideal.Quotient.mkₐ k I (X i)
  have hx : boxPowers x n = T.map (Ideal.Quotient.mkₐ k I) := by
    rw [boxPowers, show T = Ideal.span (Set.range fun i => (X i : MvPolynomial σ k) ^ n)
      from rfl, Ideal.map_span, ← Set.range_comp]
    simp [x, Function.comp_def, map_pow]
  have hF : Ideal.span (Set.range fun i => truncProj k σ n (F i)) =
      H.map (Ideal.Quotient.mkₐ k T) := by
    rw [show H = Ideal.span (Set.range F) from rfl, Ideal.map_span, ← Set.range_comp]
    rfl
  have hpure (i : σ) : (X i : MvPolynomial σ k) ^ L ∈ T := by
    apply T.mem_of_dvd (pow_dvd_pow (X i) hnL)
    exact Ideal.subset_span (Set.mem_range_self i)
  have hsum : I ⊔ T = T ⊔ H := by
    refine le_antisymm (sup_le ?_ le_sup_left) ?_
    · rw [show I = Ideal.span _ from rfl, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hleft : T ≤ T ⊔ H := le_sup_left
      have hright : H ≤ T ⊔ H := le_sup_right
      exact (T ⊔ H).add_mem (hleft (hpure i))
        (hright (Ideal.subset_span (Set.mem_range_self i)))
    · refine sup_le le_sup_right ?_
      rw [show H = Ideal.span (Set.range F) from rfl, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : X i ^ L + F i ∈ I := Ideal.subset_span (Set.mem_range_self i)
      have hleft : I ≤ I ⊔ T := le_sup_left
      have hright : T ≤ I ⊔ T := le_sup_right
      simpa using (I ⊔ T).sub_mem (hleft hi) (hright (hpure i))
  change Module.finrank k ((MvPolynomial σ k ⧸ I) ⧸ boxPowers x n) = _
  rw [hx, hF]
  exact ((DoubleQuot.quotQuotEquivQuotSupₐ k I T).trans
    ((Ideal.quotientEquivAlgOfEq k hsum).trans
      (DoubleQuot.quotQuotEquivQuotSupₐ k T H).symm)).toLinearEquiv.finrank_eq

end PolynomialQuotient

section Determinants

variable {B : Type*} [CommRing B] [Algebra k B]

private theorem map_span_of_eigenvectors (δ : B →ₐ[k] B) (S : Set B)
    (hS : ∀ x ∈ S, ∃ c : k, c ≠ 0 ∧ δ x = c • x) :
    (Ideal.span S).map δ.toRingHom = Ideal.span S := by
  rw [Ideal.map_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, _, hc⟩ := hS x hx
    change δ x ∈ Ideal.span S
    rw [hc]
    exact Submodule.smul_of_tower_mem _ c (Ideal.subset_span hx)
  · intro x hx
    obtain ⟨c, hc, hδ⟩ := hS x hx
    change x ∈ Ideal.span (δ.toRingHom '' S)
    have hmem : δ x ∈ Ideal.span (δ.toRingHom '' S) :=
      Ideal.subset_span ⟨x, hx, rfl⟩
    rw [hδ] at hmem
    simpa only [inv_smul_smul₀ hc] using
      Submodule.smul_of_tower_mem (Ideal.span (δ.toRingHom '' S)) c⁻¹ hmem

private theorem scale_eigen_pow {δ : B →ₐ[k] B} {c : k} {x : B}
    (hx : δ x = c • x) (t : ℕ) : δ (x ^ t) = c ^ t • x ^ t := by
  rw [map_pow, hx, Algebra.smul_def, mul_pow, ← map_pow, ← Algebra.smul_def]

/-- The ideal generated by a stabilized power of a scalar eigenvector has
dimension divisible by the order of its eigenvalue. -/
private theorem modEq_finrank_quotient_power [Module.Finite k B] (δ : B ≃ₐ[k] B)
    {c : k} (hc : c ≠ 0) (x : B) (hx : δ x = c • x) (t : ℕ)
    (hstable : ∃ y : B, x ^ (t + 1) * y = x ^ t) :
    Module.finrank k B ≡ Module.finrank k (B ⧸ Ideal.span {x ^ t}) [MOD orderOf c] := by
  let I := Ideal.span ({x ^ t} : Set B)
  let W := I.restrictScalars k
  have hI : I.map δ.toAlgHom.toRingHom = I :=
    map_span_of_eigenvectors δ.toAlgHom _ fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨c ^ t, pow_ne_zero _ hc, scale_eigen_pow (δ := δ.toAlgHom) hx t⟩
  let D : W →ₗ[k] W := δ.toLinearEquiv.toLinearMap.restrict fun z hz => by
    change δ z ∈ I
    rw [← hI]
    exact Ideal.mem_map_of_mem δ.toAlgHom.toRingHom hz
  let L : W →ₗ[k] W := (LinearMap.mulLeft k x).restrict fun z hz => I.mul_mem_left x hz
  have hD : Function.Injective D := fun z w h => Subtype.ext (δ.injective (congrArg Subtype.val h))
  have hL : Function.Surjective L := by
    obtain ⟨y, hy⟩ := hstable
    intro z
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (show (z : B) ∈ I from z.property)
    refine ⟨⟨b * y * x ^ t, Ideal.mem_span_singleton'.mpr ⟨b * y, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change x * (b * y * x ^ t) = (z : B)
    rw [show x * (b * y * x ^ t) = b * (x ^ (t + 1) * y) by rw [pow_succ]; ring, hy, hb]
  let eD := LinearEquiv.ofBijective D ⟨hD, LinearMap.injective_iff_surjective.mp hD⟩
  let eL := LinearEquiv.ofBijective L ⟨LinearMap.injective_iff_surjective.mpr hL, hL⟩
  have hcomm : D.comp L = c • L.comp D := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change δ (x * (z : B)) = c • (x * δ (z : B))
    rw [map_mul, hx, Algebra.smul_mul_assoc]
  have hdetD : D.det ≠ 0 := eD.isUnit_det'.ne_zero
  have hdetL : L.det ≠ 0 := eL.isUnit_det'.ne_zero
  have hdet : (1 : k) * (L.det * D.det) = c ^ Module.finrank k W * (L.det * D.det) := by
    simpa only [LinearMap.det_comp, LinearMap.det_smul, one_mul, mul_comm D.det L.det] using
      congrArg LinearMap.det hcomm
  have hdiv : orderOf c ∣ Module.finrank k W :=
    orderOf_dvd_iff_pow_eq_one.mpr (mul_right_cancel₀ (mul_ne_zero hdetL hdetD) hdet).symm
  have hr := W.finrank_quotient_add_finrank
  change Module.finrank k (B ⧸ I) + Module.finrank k W = Module.finrank k B at hr
  change Module.finrank k B ≡ Module.finrank k (B ⧸ I) [MOD orderOf c]
  rw [← hr]
  simpa only [Nat.add_zero] using
    (Nat.ModEq.refl (Module.finrank k (B ⧸ I))).add (Nat.modEq_zero_iff_dvd.mpr hdiv)

/-- Successive quotienting by stabilized powers of the eigenvectors preserves
the rank modulo the order of their common eigenvalue. -/
private theorem modEq_finrank_quotient_boxPowers [Module.Finite k B] {σ : Type} [Finite σ]
    (δ : B ≃ₐ[k] B) {c : k} (hc : c ≠ 0) (x : σ → B) (hx : ∀ i, δ (x i) = c • x i)
    (t : ℕ) (hstable : ∀ i, ∃ y : B, x i ^ (t + 1) * y = x i ^ t) :
    Module.finrank k B ≡ Module.finrank k (B ⧸ boxPowers x t) [MOD orderOf c] := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let I (s : Finset σ) := Ideal.span ((fun i => x i ^ t) '' (↑s : Set σ))
  have step (s : Finset σ) :
      Module.finrank k B ≡ Module.finrank k (B ⧸ I s) [MOD orderOf c] := by
    induction s using Finset.induction_on with
    | empty =>
      have hI : I ∅ = ⊥ := by simp [I]
      rw [hI, (AlgEquiv.quotientBot k B).toLinearEquiv.finrank_eq]
    | insert i s hi ih =>
      let J := Ideal.span ({x i ^ t} : Set B)
      have hinsert : I (insert i s) = I s ⊔ J := by
        simp [I, J, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, sup_comm]
      have hinv : I s = (I s).map (δ : B →+* B) :=
        (map_span_of_eigenvectors δ.toAlgHom _ fun z hz => by
          obtain ⟨j, _, rfl⟩ := hz
          exact ⟨c ^ t, pow_ne_zero _ hc, scale_eigen_pow (δ := δ.toAlgHom) (hx j) t⟩).symm
      let f := Ideal.Quotient.mkₐ k (I s)
      let δ' := Ideal.quotientEquivAlg (I s) (I s) δ hinv
      have hδ : δ' (f (x i)) = c • f (x i) := by
        change δ' (Ideal.Quotient.mk (I s) (x i)) = _
        rw [Ideal.quotientEquivAlg_mk]
        change f (δ (x i)) = _
        rw [hx, map_smul]
      have hst : ∃ y : B ⧸ I s, f (x i) ^ (t + 1) * y = f (x i) ^ t := by
        obtain ⟨y, hy⟩ := hstable i
        exact ⟨f y, by simpa only [map_mul, map_pow] using congrArg f hy⟩
      have hs := modEq_finrank_quotient_power δ' hc (f (x i)) hδ t hst
      have hJ : J.map f = Ideal.span ({f (x i) ^ t} : Set (B ⧸ I s)) := by
        rw [show J = Ideal.span _ from rfl, Ideal.map_span, Set.image_singleton, map_pow]
      rw [← hJ, (DoubleQuot.quotQuotEquivQuotSupₐ k (I s) J).toLinearEquiv.finrank_eq,
        ← hinsert] at hs
      exact ih.trans hs
  have hI : I Finset.univ = boxPowers x t := by
    unfold I boxPowers
    congr 1
    ext y
    exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, Finset.mem_univ i, h⟩⟩
  exact hI ▸ step Finset.univ

private theorem exists_stable_box_width [Module.Finite k B] {σ : Type} [Finite σ]
    (x : σ → B) (n : ℕ) :
    ∃ t ≥ n, ∀ i, ∃ y : B, x i ^ (t + 1) * y = x i ^ t := by
  classical
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  let : Fintype σ := Fintype.ofFinite σ
  choose u b hb using fun i => IsArtinian.exists_pow_succ_smul_dvd (x i) (1 : B)
  let t := max n (Finset.univ.sup u)
  refine ⟨t, le_max_left _ _, fun i => ⟨b i, ?_⟩⟩
  have hu : u i ≤ t :=
    (Finset.le_sup (f := u) (Finset.mem_univ i)).trans (le_max_right _ _)
  let d := t - u i
  have ht : t = u i + d := by dsimp [d]; omega
  have h : x i ^ (u i + 1) * b i = x i ^ u i := by
    simpa [smul_eq_mul, Nat.succ_eq_add_one] using hb i
  rw [ht, show u i + d + 1 = u i + 1 + d by omega,
    pow_add (x i) (u i + 1) d, pow_add (x i) (u i) d, mul_right_comm, h]

end Determinants

section EquivariantPerturbation

variable {σ : Type} [Finite σ]

/-- Two compatible rectangular presentations of the same rank give the rank
congruence forced by simultaneous scaling of the equations and variables. -/
theorem finrank_modEq_of_equivariant_equations (F : σ → MvPolynomial σ k)
    {c : k} (hc : c ≠ 0) (hF : ∀ i, scale c (F i) = c • F i)
    {n m L D : ℕ} (hn : 0 < n) (hm : 2 * n ≤ m) (hL : m ≤ L)
    (hdeg : ∀ i, (F i).totalDegree < L) (hcL : c ^ L = c)
    (hrn : Module.finrank k (truncAlg k σ n ⧸
      Ideal.span (Set.range fun i => truncProj k σ n (F i))) = D)
    (hrm : Module.finrank k (truncAlg k σ m ⧸
      Ideal.span (Set.range fun i => truncProj k σ m (F i))) = D) :
    L ^ Nat.card σ ≡ D [MOD orderOf c] := by
  let G : σ → MvPolynomial σ k := fun i => X i ^ L + F i
  let I := Ideal.span (Set.range G)
  let B := MvPolynomial σ k ⧸ I
  let f := Ideal.Quotient.mkₐ k I
  let x : σ → B := fun i => f (X i)
  let E := AlgEquiv.ofAlgHom (scale (σ := σ) c) (scale c⁻¹)
    (by rw [scale_comp, inv_mul_cancel₀ hc, scale_one])
    (by rw [scale_comp, mul_inv_cancel₀ hc, scale_one])
  have hG (i : σ) : scale c (G i) = c • G i := by
    change scale c (X i ^ L + F i) = c • (X i ^ L + F i)
    rw [map_add, scale_eigen_pow (scale_X c i) L, hcL, hF, smul_add]
  have hI : I = I.map (E : MvPolynomial σ k →+* MvPolynomial σ k) :=
    (map_span_of_eigenvectors (scale c) (Set.range G) fun z hz => by
      obtain ⟨i, rfl⟩ := hz
      exact ⟨c, hc, hG i⟩).symm
  let δ := Ideal.quotientEquivAlg I I E hI
  have hδ (i : σ) : δ (x i) = c • x i := by
    change δ (Ideal.Quotient.mk I (X i)) = _
    rw [Ideal.quotientEquivAlg_mk]
    change f (scale c (X i)) = _
    rw [scale_X, map_smul]
  obtain ⟨hfin, hrB⟩ := finite_perturbation F (show 0 < L by omega) hdeg
  let : Module.Finite k B := hfin
  have hnD : Module.finrank k (B ⧸ boxPowers x n) = D :=
    (perturbation_box_finrank F (show n ≤ L by omega)).trans hrn
  have hmD : Module.finrank k (B ⧸ boxPowers x m) = D :=
    (perturbation_box_finrank F hL).trans hrm
  obtain ⟨t, ht, hstable⟩ := exists_stable_box_width (k := k) x n
  have htD : Module.finrank k (B ⧸ boxPowers x t) = D := by
    rw [boxPowers_eq_of_finrank x hn hm (hnD.trans hmD.symm) ht, hnD]
  have h := modEq_finrank_quotient_boxPowers δ hc x hδ t hstable
  rw [show Module.finrank k B = _ from hrB, htD] at h
  exact h

end EquivariantPerturbation

end Langlands.FormalGroup.ModuleLaw.RationalHeightRankCongruence
