import Langlands.GroupScheme.Trigonalizable.RelativeTower
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCategory
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisFullFaithfulnessProof
import Langlands.GroupScheme.Torus.EndomorphismDichotomy
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! # The prime-to-`p` quotient of a character group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit.PrimeToPart

section Lattice

variable (p : ℕ) [hp : Fact p.Prime] (Λ : Type u) [AddCommGroup Λ]

/-- The torsion elements of `Λ` killed by an integer prime to `p`. -/
def primeToTorsion : AddSubgroup Λ where
  carrier := {x | ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ m • x = 0}
  zero_mem' := ⟨1, one_pos, hp.out.not_dvd_one, smul_zero _⟩
  add_mem' := by
    rintro x y ⟨m, hm, hpm, hx⟩ ⟨m', hm', hpm', hy⟩
    refine ⟨m * m', mul_pos hm hm', fun h => (hp.out.dvd_mul.mp h).elim hpm hpm', ?_⟩
    have h1 : (m * m') • x = 0 := by rw [mul_comm, mul_smul, hx, smul_zero]
    have h2 : (m * m') • y = 0 := by rw [mul_smul, hy, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro x ⟨m, hm, hpm, hx⟩
    exact ⟨m, hm, hpm, by rw [smul_neg, hx, neg_zero]⟩

variable {p Λ} in
theorem mem_primeToTorsion {x : Λ} :
    x ∈ primeToTorsion p Λ ↔ ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ m • x = 0 :=
  Iff.rfl

/-- A finitely generated `Λ` has an integer prime to `p` killing its prime-to-`p` torsion. -/
theorem exists_exponent [AddGroup.FG Λ] :
    ∃ e : ℕ, 0 < e ∧ ¬ p ∣ e ∧ ∀ x ∈ primeToTorsion p Λ, e • x = 0 := by
  classical
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hfg : (primeToTorsion p Λ).toIntSubmodule.FG := IsNoetherian.noetherian _
  obtain ⟨S, hS⟩ := hfg
  have hmem : ∀ s ∈ S, ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ m • s = 0 := by
    intro s hs
    have : s ∈ (primeToTorsion p Λ).toIntSubmodule := hS ▸ Submodule.subset_span hs
    exact this
  choose! m hm using hmem
  refine ⟨∏ s ∈ S, m s, Finset.prod_pos fun s hs => (hm s hs).1, ?_, ?_⟩
  · intro h
    obtain ⟨s, hs, hd⟩ := (Prime.dvd_finsetProd_iff hp.out.prime _).mp h
    exact (hm s hs).2.1 hd
  · intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set Λ) := by
      rw [hS]
      exact hx
    refine Submodule.span_induction (fun s hs => ?_) (smul_zero _) (fun y z _ _ hy hz => ?_)
      (fun c y _ hy => ?_) hx'
    · obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem m hs
      rw [ht, mul_comm, mul_smul, (hm s hs).2.2, smul_zero]
    · rw [smul_add, hy, hz, add_zero]
    · rw [smul_comm, hy, smul_zero]

/-- The `p`-saturation of `e • Λ`. -/
def saturation (e : ℕ) : AddSubgroup Λ where
  carrier := {x | ∃ a : ℕ, ∃ y : Λ, p ^ a • x = e • y}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x x' ⟨a, y, hy⟩ ⟨b, y', hy'⟩
    refine ⟨a + b, p ^ b • y + p ^ a • y', ?_⟩
    rw [smul_add, smul_add, smul_comm e (p ^ b) y, smul_comm e (p ^ a) y', ← hy, ← hy',
      ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm b a]
  neg_mem' := by
    rintro x ⟨a, y, hy⟩
    exact ⟨a, -y, by rw [smul_neg, hy, smul_neg]⟩

variable {Λ} in
omit hp in
/-- The quotient by the saturation has no `p`-torsion. -/
theorem eq_zero_of_p_smul (e : ℕ) (y : Λ ⧸ saturation p Λ e) (hy : p • y = 0) : y = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    have hy' : p • x ∈ saturation p Λ e := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul]
      exact hy
    rw [QuotientAddGroup.eq_zero_iff]
    obtain ⟨a, z, hz⟩ := hy'
    exact ⟨a + 1, z, by rw [pow_succ, mul_smul, hz]⟩

variable {Λ} in
omit hp in
/-- The quotient by the saturation is killed by `e`. -/
theorem e_smul_eq_zero (e : ℕ) (y : Λ ⧸ saturation p Λ e) : e • y = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H x =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨0, x, by rw [pow_zero, one_smul]⟩

variable {Λ} in
/-- Prime-to-`p` torsion injects into the quotient by the saturation, when `e` kills it. -/
theorem eq_zero_of_mem_saturation (e : ℕ) (he : ¬ p ∣ e)
    (hek : ∀ x ∈ primeToTorsion p Λ, e • x = 0) {w : Λ} (hw : w ∈ primeToTorsion p Λ)
    (hsat : w ∈ saturation p Λ e) : w = 0 := by
  obtain ⟨m', hm', hpm', hwm⟩ := hw
  obtain ⟨a, ν, hν⟩ := hsat
  have hν' : ν ∈ primeToTorsion p Λ := by
    refine ⟨m' * e, ?_, fun h => (hp.out.dvd_mul.mp h).elim hpm' he, ?_⟩
    · rcases Nat.eq_zero_or_pos e with h0 | h0
      · exact absurd (h0 ▸ dvd_zero p) he
      · exact mul_pos hm' h0
    · rw [mul_smul, ← hν, smul_comm, hwm, smul_zero]
  have h1 : p ^ a • w = 0 := by rw [hν, hek ν hν']
  have hcop : Nat.Coprime (p ^ a) m' :=
    Nat.Coprime.pow_left a ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
      hpm')).symm)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (p ^ a : ℕ) + v * m' = 1 := by
    refine ⟨Nat.gcdA (p ^ a) m', Nat.gcdB (p ^ a) m', ?_⟩
    have := Nat.gcd_eq_gcd_ab (p ^ a) m'
    rw [hcop.gcd_eq_one] at this
    push_cast at this ⊢
    linarith
  calc w = (u * (p ^ a : ℕ) + v * m' : ℤ) • w := by rw [huv, one_smul]
    _ = u • ((p ^ a) • w) + v • (m' • w) := by
        rw [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
    _ = 0 := by rw [h1, hwm, smul_zero, smul_zero, add_zero]

variable {p} in
/-- A finitely generated commutative group killed by a positive integer `e` with `p ∤ e` is
finite of order prime to `p`. -/
theorem finite_and_coprime_card {M : Type*} [AddCommGroup M] [AddGroup.FG M] (e : ℕ)
    (he0 : 0 < e) (he : ¬ p ∣ e) (hM : ∀ x : M, e • x = 0) :
    Finite M ∧ Nat.Coprime (Nat.card M) p := by
  have hfin : Finite M := AddCommGroup.finite_of_fg_isAddTorsion M fun x =>
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨e, he0, hM x⟩
  refine ⟨hfin, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun hdvd => ?_)⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
  exact he (hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (hM x))

end Lattice


section Characters

open DiagonalizableCharacter

variable {k : Type u} [Field k] {Λ Λ₁ : Type u} [AddCommGroup Λ] [AddCommGroup Λ₁]

theorem charValue_evalCharacter (m : Λ) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) :
    VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m) T x =
      ((Diagonalizable.characterPointsEquiv (CommRingCat.of k) Λ T x (.ofAdd m) :
        (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) := by
  rw [VectorGroup.charValue, evalCharacter_apply]

theorem charValue_evalCharacter_add (m m' : Λ) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) :
    VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ (m + m')) T x =
      VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m) T x *
        VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m') T x := by
  rw [charValue_evalCharacter, charValue_evalCharacter, charValue_evalCharacter, ofAdd_add,
    map_mul, Units.val_mul]

theorem charValue_evalCharacter_nsmul (n : ℕ) (m : Λ) (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) :
    VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ (n • m)) T x =
      VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m) T x ^ n := by
  rw [charValue_evalCharacter, charValue_evalCharacter, ofAdd_nsmul, map_pow,
    Units.val_pow_eq_pow_val]

theorem charValue_evalCharacter_zero (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) :
    VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ 0) T x = 1 := by
  rw [charValue_evalCharacter, ofAdd_zero, map_one, Units.val_one]

/-- A character of `D(Λ)` with all values `1` is the zero element of `Λ`. -/
theorem eq_zero_of_charValue_evalCharacter (m : Λ)
    (h : ∀ (T : Over (Spec (CommRingCat.of k)))
      (x : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
      VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m) T x = 1) : m = 0 := by
  apply (evalCharacterAddHom_bijective k Λ).1
  rw [map_zero]
  change evalCharacter (CommRingCat.of k) Λ m = 0
  rw [← (evalCharacterAddHom k Λ).map_zero]
  apply characterLattice.ext_points
  intro U y
  change _ = Gm.pointsEquiv _ U (y ≫ (CommGroupScheme.groupHom
    (evalCharacter (CommRingCat.of k) Λ 0)).hom.hom)
  rw [evalCharacter_apply, evalCharacter_apply, ofAdd_zero, map_one]
  apply Units.ext
  rw [Units.val_one]
  have := h U y
  rwa [charValue_evalCharacter] at this

/-- Values of characters along `D(g) : D(Λ₁) ⟶ D(Λ)`. -/
theorem charValue_restrictMap (g : Λ →+ Λ₁) (m : Λ) (T : Over (Spec (CommRingCat.of k)))
    (z : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ₁).X) :
    VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ m) T
        (z ≫ (Diagonalizable.restrictMap (CommRingCat.of k) g).hom.hom) =
      VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ₁ (g m)) T z := by
  rw [charValue_evalCharacter, charValue_evalCharacter]
  congr 1
  exact Diagonalizable.pointsEquiv_restrictMap _ g z m

end Characters


section Solvable

open DiagonalizableCharacter ClosedAdditivePolynomial Polynomial

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

/-- Over a perfect field of characteristic `p`, if `p ∤ e` and `e` kills the prime-to-`p`
torsion of `Λ`, the weights along the closed subgroup `D(Λ ⧸ K_e) ⟶ D(Λ)` induced by the
quotient map of character groups satisfy `RelativeSolvable`. (For finitely generated `Λ` this
subgroup is finite étale; that remark is not used or proved here.) -/
theorem relativeSolvable [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ)
    (he : ¬ p ∣ e) (hek : ∀ x ∈ primeToTorsion p Λ, e • x = 0)
    {K : GroupScheme (Spec (CommRingCat.of k))}
    (a : K ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
    (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
    (ha : IsClosedSubgroup a)
    (hst : ∀ (T : Over (Spec (CommRingCat.of k)))
      (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X)
      (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) 1).X),
      x ∈ (SubgroupFunctor.range a).carrier T →
        (VectorGroup.weightAction (n := 1) χ).act d x ∈ (SubgroupFunctor.range a).carrier T) :
    RelativeSolvable (Diagonalizable.restrictMap (CommRingCat.of k)
      (QuotientAddGroup.mk' (saturation p Λ e))) a χ := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨l, rfl⟩ := (evalCharacterAddHom_bijective k Λ).2 χ
  change RelativeSolvable _ a (evalCharacter (CommRingCat.of k) Λ l)
  set g := QuotientAddGroup.mk' (saturation p Λ e)
  -- The degree of the closed polynomial is a power of `p`.
  have hdeg : closedPolynomial a ≠ 0 → ∃ s : ℕ, (closedPolynomial a).natDegree = p ^ s := by
    intro hf
    have hmonic := closedPolynomial_monic a hf
    have hpos := natDegree_pos a ha hf
    have htaylor := RelativeRoot.AdditivePolynomial.taylor_eq_of_mem_span hmonic hpos
      (taylor_mem_span a ha)
    have hNc : (closedPolynomial a).coeff (closedPolynomial a).natDegree ≠ 0 := by
      rw [hmonic.coeff_natDegree]
      exact one_ne_zero
    rcases PerfectCorrection.eq_zero_or_eq_pow_of_coeff_ne_zero p htaylor hNc with h | h
    · omega
    · exact h
  have hgpow : ∀ (s : ℕ) (y : Λ ⧸ saturation p Λ e), p ^ s • y = 0 → y = 0 := by
    intro s
    induction s with
    | zero => intro y hy; simpa using hy
    | succ s ih =>
      intro y hy
      apply ih
      apply eq_zero_of_p_smul p e
      rw [← mul_smul, ← pow_succ']
      exact hy
  refine ⟨fun hf hN T z => ?_, fun hf h1 => ?_⟩
  · obtain ⟨s, hs⟩ := hdeg hf
    have hgl : g l = 0 := by
      apply hgpow s
      apply eq_zero_of_charValue_evalCharacter (k := k)
      intro T' z'
      rw [charValue_evalCharacter_nsmul, ← charValue_restrictMap, ← hs]
      exact hN T' z'
    rw [charValue_restrictMap, hgl, charValue_evalCharacter_zero]
  · obtain ⟨s, hs⟩ := hdeg hf
    have hgl : g l = 0 := by
      apply eq_zero_of_charValue_evalCharacter (k := k)
      intro T' z'
      rw [← charValue_restrictMap]
      exact h1 T' z'
    set f := closedPolynomial a with hfdef
    have hmonic : f.Monic := closedPolynomial_monic a hf
    have hpos := natDegree_pos a ha hf
    have htaylor := RelativeRoot.AdditivePolynomial.taylor_eq_of_mem_span hmonic hpos
      (taylor_mem_span a ha)
    have h0 : f.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero]
      exact eval_zero a ha
    by_cases hall : ∀ i < f.natDegree, f.coeff i = 0
    · left
      have hfX : f = X ^ f.natDegree := by
        ext i
        rw [coeff_X_pow]
        rcases lt_trichotomy i f.natDegree with hi | hi | hi
        · rw [hall i hi]
          simp [hi.ne]
        · rw [hi, hmonic.coeff_natDegree]
          simp
        · rw [coeff_eq_zero_of_natDegree_lt hi]
          simp [hi.ne']
      intro m
      refine ⟨(iterateFrobeniusEquiv k p s).symm m, ?_⟩
      rw [hfX, eval_pow, eval_X, hs, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
    · right
      push Not at hall
      obtain ⟨i, hiN, hi⟩ := hall
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact hi h0
      obtain ⟨v, hv⟩ :=
        (PerfectCorrection.eq_zero_or_eq_pow_of_coeff_ne_zero p htaylor hi).resolve_left hi0
      have hvs : v < s := by
        have h2 : p ^ v < p ^ s := by
          rw [← hv, ← hs]
          exact hiN
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h2
      -- `w = p^v l` is prime-to-`p` torsion.
      set m' := p ^ (s - v) - 1 with hm'
      have hm1 : m' + 1 = p ^ (s - v) := by
        have := Nat.one_le_pow (s - v) p hp.pos
        omega
      have hwm : m' • (p ^ v • l) = 0 := by
        apply eq_zero_of_charValue_evalCharacter (k := k)
        intro T' d
        have hsc := PerfectCorrection.charValue_pow_eq_of_coeff_ne_zero a
          (evalCharacter (CommRingCat.of k) Λ l) ha hf hst hi d
        rw [hv, hs, ← charValue_evalCharacter_nsmul, ← charValue_evalCharacter_nsmul] at hsc
        have hsum : p ^ s • l = m' • (p ^ v • l) + p ^ v • l := by
          rw [← succ_nsmul, hm1, ← mul_smul, ← pow_add, Nat.sub_add_cancel hvs.le]
        rw [hsum, charValue_evalCharacter_add] at hsc
        have hu : IsUnit (VectorGroup.charValue (evalCharacter (CommRingCat.of k) Λ
            (p ^ v • l)) T' d) := by
          rw [charValue_evalCharacter]
          exact Units.isUnit _
        have := hu.mul_right_cancel (hsc.symm.trans (one_mul _).symm)
        exact this
      have hpm' : ¬ p ∣ m' := by
        intro hd
        have hd2 : p ∣ p ^ (s - v) := dvd_pow_self p (Nat.sub_ne_zero_of_lt hvs)
        have : p ∣ p ^ (s - v) - m' := Nat.dvd_sub hd2 hd
        rw [show p ^ (s - v) - m' = 1 by omega] at this
        exact hp.not_dvd_one this
      have hm'pos : 0 < m' := by
        have : 2 ≤ p ^ (s - v) :=
          le_trans hp.two_le (Nat.le_self_pow (Nat.sub_ne_zero_of_lt hvs) p)
        omega
      have hw0 : p ^ v • l = 0 := by
        apply eq_zero_of_mem_saturation p e he hek ⟨m', hm'pos, hpm', hwm⟩
        rw [← QuotientAddGroup.eq_zero_iff]
        change g (p ^ v • l) = 0
        rw [map_nsmul, hgl, smul_zero]
      intro T' d
      rw [← charValue_evalCharacter_nsmul, hs, ← Nat.sub_add_cancel hvs.le, pow_add, mul_smul,
        hw0, smul_zero, charValue_evalCharacter_zero]

end Solvable

end Langlands.GroupScheme.TrigonalizableExtensionSplit.PrimeToPart
