import Langlands.Representation.Archimedean.ComplexNoncompactPicture
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder

/-!
# Leading monomials of the moment symbols

Polynomials in the coordinates `v_p` and the dual coordinates `ξ_p` (`p` strictly below the
diagonal) of the lower unipotent group. With `nb = 1 + lowMat v`, `Ξ = lowMat ξ` and
`U = (nb Ξᵀ)_{strictly upper}`, let `Φ = nb⁻¹ U nb`. For a lexicographic monomial order with
the dual coordinates first, we compute the leading monomials of `2N` entries of `Φ`
(`N` the number of positions): `Φ_{jk}` (`j < k`) has leading monomial `ξ_{kj}`, and
`Φ_{a, c+1}` (`c < a`) has leading monomial `ξ_{c+1, c} v_{a c}`. Hence the products of these
entries are linearly independent (`linearIndependent_prod_symbols`).
-/

noncomputable section

open scoped Matrix MonomialOrder

set_option autoImplicit false

namespace Langlands.Archimedean.MomentSymbols

open MvPolynomial Langlands.Archimedean.NoncompactPicture

variable {n : ℕ}

/-! ## Variables and the monomial order -/

/-- The variables: `Sum.inl p` is the coordinate `v_p`, `Sum.inr p` the dual coordinate `ξ_p`. -/
def MVar (n : ℕ) := Lw n ⊕ Lw n

instance : DecidableEq (MVar n) := inferInstanceAs (DecidableEq (Lw n ⊕ Lw n))
instance : Fintype (MVar n) := inferInstanceAs (Fintype (Lw n ⊕ Lw n))

/-- The coordinate `v_p`. -/
def vV (p : Lw n) : MVar n := Sum.inl p

/-- The dual coordinate `ξ_p`. -/
def xV (p : Lw n) : MVar n := Sum.inr p

/-- The sort key: dual coordinates first, by row ascending, then column descending; then the
coordinates, by jump `a - c` descending, then row. -/
def key : MVar n → ℕ ×ₗ ℕ ×ₗ ℕ
  | Sum.inr p => toLex (0, toLex ((p.1.1 : ℕ), n - 1 - (p.1.2 : ℕ)))
  | Sum.inl p => toLex (1, toLex (n - ((p.1.1 : ℕ) - (p.1.2 : ℕ)), (p.1.1 : ℕ)))

theorem key_injective : Function.Injective (key (n := n)) := by
  rintro (⟨⟨a, b⟩, hab⟩ | ⟨⟨a, b⟩, hab⟩) (⟨⟨a', b'⟩, hab'⟩ | ⟨⟨a', b'⟩, hab'⟩) h <;>
    simp only [key, toLex_inj, Prod.mk.injEq] at h
  · obtain ⟨-, h1, h2⟩ := h
    have ha := a.2; have hb := b.2; have ha' := a'.2; have hb' := b'.2
    have : b = b' := Fin.ext (by have := hab; have := hab'; simp only [Fin.lt_def] at *; omega)
    have : a = a' := Fin.ext h2
    subst_vars; rfl
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · obtain ⟨-, h1, h2⟩ := h
    have ha := a.2; have hb := b.2; have ha' := a'.2; have hb' := b'.2
    have : a = a' := Fin.ext h1
    have : b = b' := Fin.ext (by simp only [Fin.lt_def] at *; omega)
    subst_vars; rfl

instance : LinearOrder (MVar n) := LinearOrder.lift' key key_injective

instance : WellFoundedGT (MVar n) := Finite.to_wellFoundedGT

theorem lt_iff_key (x y : MVar n) : x < y ↔ key x < key y := Iff.rfl

theorem xV_lt_vV (q p : Lw n) : xV q < vV p := by
  rw [lt_iff_key]
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl Nat.zero_lt_one)

theorem xV_lt_xV {l k l' k' : Fin n} (h : k < l) (h' : k' < l') (hlt : l < l' ∨ (l = l' ∧ k' < k)) :
    xV ⟨(l, k), h⟩ < xV ⟨(l', k'), h'⟩ := by
  rw [lt_iff_key]
  simp only [key, xV]
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 ?_⟩)
  rcases hlt with hlt | ⟨rfl, hk⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨rfl, ?_⟩
    have := k.2; have := k'.2; simp only [Fin.lt_def] at hk; omega

theorem vV_lt_vV {a c a' c' : Fin n} (h : c < a) (h' : c' < a')
    (hj : (a' : ℕ) - c' < (a : ℕ) - c) : vV ⟨(a, c), h⟩ < vV ⟨(a', c'), h'⟩ := by
  rw [lt_iff_key]
  simp only [key, vV]
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl ?_)⟩)
  have := a.2; have := a'.2; simp only [Fin.lt_def] at h h'; omega

/-! ## Polynomials and leading monomials -/

/-- The polynomial ring in the coordinates and dual coordinates. -/
abbrev Pol (n : ℕ) := MvPolynomial (MVar n) ℂ

/-- The lexicographic monomial order. -/
abbrev ord (n : ℕ) : MonomialOrder (MVar n) := MonomialOrder.lex

/-- `f` involves only the coordinates `v`. -/
def VOnly (f : Pol n) : Prop := ∀ s ∈ f.support, ∀ q : Lw n, s (xV q) = 0

theorem vOnly_C (c : ℂ) : VOnly (C c : Pol n) := by
  classical
  intro s hs q
  rw [mem_support_iff, coeff_C] at hs
  have : s = 0 := by
    by_contra h
    exact hs (ite_eq_right (Ne.symm h))
  rw [this]; rfl

theorem vOnly_X (p : Lw n) : VOnly (X (vV p) : Pol n) := by
  intro s hs q
  rw [support_X, Finset.mem_singleton] at hs
  rw [hs, Finsupp.single_apply, ite_eq_right]
  intro h; exact absurd h (by simp [vV, xV])

theorem VOnly.add {f g : Pol n} (hf : VOnly f) (hg : VOnly g) : VOnly (f + g) := by
  intro s hs q
  rcases Finset.mem_union.1 (support_add hs) with h | h
  · exact hf s h q
  · exact hg s h q

theorem VOnly.mul {f g : Pol n} (hf : VOnly f) (hg : VOnly g) : VOnly (f * g) := by
  intro s hs q
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  rw [Finsupp.add_apply, hf a ha q, hg b hb q]

theorem VOnly.neg {f : Pol n} (hf : VOnly f) : VOnly (-f) := by
  intro s hs q
  rw [support_neg] at hs
  exact hf s hs q

theorem VOnly.sub {f g : Pol n} (hf : VOnly f) (hg : VOnly g) : VOnly (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem vOnly_zero : VOnly (0 : Pol n) := by
  simpa using vOnly_C (n := n) 0

theorem vOnly_one : VOnly (1 : Pol n) := by
  simpa using vOnly_C (n := n) 1

theorem vOnly_sum {ι : Type*} (s : Finset ι) (f : ι → Pol n) (hf : ∀ i ∈ s, VOnly (f i)) :
    VOnly (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vOnly_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Monomials of `X (xV q) * f`, `f` in the coordinates only. -/
theorem support_X_mul_apply {f : Pol n} (hf : VOnly f) (q : Lw n) {s : MVar n →₀ ℕ}
    (hs : s ∈ (X (xV q) * f).support) (q' : Lw n) :
    s (xV q') = if q' = q then 1 else 0 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hs)
  rw [support_X, Finset.mem_singleton] at ha
  rw [Finsupp.add_apply, ha, hf b hb q', add_zero, Finsupp.single_apply]
  by_cases h : q' = q
  · subst h; simp
  · have h1 : ¬ (xV q = xV q') := fun h' => h (Sum.inr_injective h').symm
    rw [ite_eq_right h1, ite_eq_right h]

/-- A monomial with a less significant dual coordinate is smaller. -/
theorem lt_of_xV_lt {q q₀ : Lw n} (hq : xV q₀ < xV q) {s D : MVar n →₀ ℕ}
    (hs : ∀ q', s (xV q') = if q' = q then 1 else 0)
    (hD : ∀ q', D (xV q') = if q' = q₀ then 1 else 0) : s ≺[ord n] D := by
  rw [MonomialOrder.lex_lt_iff]
  refine Finsupp.Lex.lt_iff.2 ⟨xV q₀, fun j hj => ?_, ?_⟩
  · rcases j with p | q'
    · exact absurd (hj.trans (xV_lt_vV q₀ p)) (lt_irrefl _)
    · change s (xV q') = D (xV q')
      rw [hs, hD, ite_eq_right, ite_eq_right]
      · rintro rfl; exact lt_irrefl _ hj
      · rintro rfl; exact lt_irrefl _ (hj.trans hq)
  · change s (xV q₀) < D (xV q₀)
    rw [hs, hD, ite_eq_left rfl, ite_eq_right]
    · exact Nat.zero_lt_one
    · rintro rfl; exact lt_irrefl _ hq

theorem degree_add_of_support_lt {f g : Pol n}
    (hg : ∀ s ∈ g.support, s ≺[ord n] (ord n).degree f) :
    (ord n).degree (f + g) = (ord n).degree f ∧
      (ord n).leadingCoeff (f + g) = (ord n).leadingCoeff f := by
  by_cases hg0 : g = 0
  · simp [hg0]
  have h := hg _ ((ord n).degree_mem_support hg0)
  exact ⟨(ord n).degree_add_of_lt h, (ord n).leadingCoeff_add_of_lt h⟩

theorem support_sum_lt {ι : Type*} (s : Finset ι) (g : ι → Pol n) {D : MVar n →₀ ℕ}
    (h : ∀ i ∈ s, ∀ t ∈ (g i).support, t ≺[ord n] D) :
    ∀ t ∈ (∑ i ∈ s, g i).support, t ≺[ord n] D := by
  classical
  intro t ht
  obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.1 (support_sum ht)
  exact h i hi t hti

theorem support_lt_of_degree_lt {f : Pol n} {D : MVar n →₀ ℕ}
    (h : (ord n).degree f ≺[ord n] D) : ∀ t ∈ f.support, t ≺[ord n] D :=
  fun _ ht => lt_of_le_of_lt ((ord n).le_degree ht) h

/-! ## The matrices -/

/-- The strictly lower triangular matrix with entries `w`. -/
def lowMatG {S : Type*} [Zero S] (w : Lw n → S) : Matrix (Fin n) (Fin n) S :=
  Matrix.of fun a b => if h : b < a then w ⟨(a, b), h⟩ else 0

/-- The strictly upper triangular part. -/
def upPart {S : Type*} [Zero S] (M : Matrix (Fin n) (Fin n) S) : Matrix (Fin n) (Fin n) S :=
  Matrix.of fun i j => if i < j then M i j else 0

/-- The generic lower unipotent matrix. -/
def nbF : Matrix (Fin n) (Fin n) (Pol n) := 1 + lowMatG fun p => X (vV p)

/-- The generic strictly lower matrix of dual coordinates. -/
def xiMat : Matrix (Fin n) (Fin n) (Pol n) := lowMatG fun p => X (xV p)

theorem nbF_apply (a b : Fin n) :
    nbF a b = (if a = b then 1 else 0) + if h : b < a then X (vV ⟨(a, b), h⟩) else 0 := by
  simp [nbF, lowMatG, Matrix.one_apply]

theorem nbF_apply_self (a : Fin n) : nbF a a = 1 := by
  simp [nbF_apply]

theorem nbF_apply_of_lt {a b : Fin n} (h : a < b) : nbF a b = 0 := by
  rw [nbF_apply, ite_eq_right (ne_of_lt h), dite_eq_right (fun h' => absurd h' (not_lt.2 h.le)),
    add_zero]

theorem nbF_det : (nbF (n := n)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · exact Finset.prod_eq_one fun a _ => nbF_apply_self a
  · intro a b hab
    exact nbF_apply_of_lt hab

/-- The inverse of `nbF`. -/
def nbInvF : Matrix (Fin n) (Fin n) (Pol n) := (nbF (n := n)).adjugate

theorem nbF_mul_nbInvF : nbF (n := n) * nbInvF = 1 := by
  rw [nbInvF, Matrix.mul_adjugate, nbF_det, one_smul]

theorem nbInvF_mul_nbF : nbInvF (n := n) * nbF = 1 := by
  rw [nbInvF, Matrix.adjugate_mul, nbF_det, one_smul]

theorem nbInvF_eq (a c : Fin n) :
    nbInvF a c = (if a = c then 1 else 0) -
      ∑ k, (if h : k < a then X (vV ⟨(a, k), h⟩) else 0) * nbInvF k c := by
  have h := congrFun (congrFun (nbF_mul_nbInvF (n := n)) a) c
  rw [Matrix.mul_apply] at h
  simp only [nbF_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.one_apply] at h
  linear_combination h

theorem nbInvF_of_le : ∀ (a c : Fin n), a ≤ c → nbInvF a c = if a = c then 1 else 0 := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    intro c hac
    rw [nbInvF_eq]
    have hs : ∑ k, (if h : k < a then X (vV ⟨(a, k), h⟩) else 0) * nbInvF k c = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k < a
      · rw [ih k hk c (hk.le.trans hac), ite_eq_right (ne_of_lt (lt_of_lt_of_le hk hac)), mul_zero]
      · rw [dite_eq_right hk, zero_mul]
    rw [hs, sub_zero]

theorem nbInvF_apply_self (a : Fin n) : nbInvF a a = 1 := by
  rw [nbInvF_of_le a a le_rfl, ite_eq_left rfl]

theorem nbInvF_apply_of_lt {a c : Fin n} (h : a < c) : nbInvF a c = 0 := by
  rw [nbInvF_of_le a c h.le, ite_eq_right (ne_of_lt h)]

theorem vOnly_nbF (a b : Fin n) : VOnly (nbF a b) := by
  rw [nbF_apply]
  refine VOnly.add ?_ ?_
  · split_ifs
    · exact vOnly_one
    · exact vOnly_zero
  · split_ifs
    · exact vOnly_X _
    · exact vOnly_zero

theorem vOnly_nbInvF : ∀ (a c : Fin n), VOnly (nbInvF a c) := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    intro c
    rw [nbInvF_eq]
    refine VOnly.sub ?_ (vOnly_sum _ _ fun k _ => ?_)
    · split_ifs
      · exact vOnly_one
      · exact vOnly_zero
    · by_cases hk : k < a
      · rw [dite_eq_left hk]
        exact (vOnly_X _).mul (ih k hk c)
      · rw [dite_eq_right hk, zero_mul]
        exact vOnly_zero

/-- **The leading monomial of `nb⁻¹_{a c}`** (`c < a`) is `-v_{a c}`. -/
theorem degree_nbInvF : ∀ (a c : Fin n) (h : c < a),
    (ord n).degree (nbInvF a c) = Finsupp.single (vV ⟨(a, c), h⟩) 1 ∧
      (ord n).leadingCoeff (nbInvF a c) = -1 := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    intro c hca
    classical
    set e : MVar n →₀ ℕ := Finsupp.single (vV ⟨(a, c), hca⟩) 1
    have hsplit : nbInvF a c = -X (vV ⟨(a, c), hca⟩) +
        -∑ k ∈ Finset.univ.erase c,
          (if h : k < a then X (vV ⟨(a, k), h⟩) else 0) * nbInvF k c := by
      rw [nbInvF_eq, ite_eq_right (ne_of_gt hca), zero_sub,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ c), dite_eq_left hca, nbInvF_apply_self,
        mul_one, neg_add]
    have hlead : (ord n).degree (-X (vV ⟨(a, c), hca⟩) : Pol n) = e := by
      rw [MonomialOrder.degree_neg, MonomialOrder.degree_X]
    have hrest : ∀ t ∈ (-∑ k ∈ Finset.univ.erase c,
        (if h : k < a then X (vV ⟨(a, k), h⟩) else 0) * nbInvF k c : Pol n).support,
          t ≺[ord n] (ord n).degree (-X (vV ⟨(a, c), hca⟩) : Pol n) := by
      rw [support_neg, hlead]
      refine support_sum_lt _ _ fun k hk t ht => ?_
      have hkc := Finset.ne_of_mem_erase hk
      by_cases hka : k < a
      · rw [dite_eq_left hka] at ht
        by_cases hck : c < k
        · obtain ⟨hdeg, -⟩ := ih k hka c hck
          have h1 := (ord n).le_degree ht
          have h2 := (ord n).degree_mul_le (f := (X (vV ⟨(a, k), hka⟩) : Pol n))
            (g := nbInvF k c)
          rw [MonomialOrder.degree_X, hdeg] at h2
          refine lt_of_le_of_lt (h1.trans h2) ?_
          rw [MonomialOrder.lex_lt_iff]
          refine Finsupp.Lex.lt_iff.2 ⟨vV ⟨(a, c), hca⟩, fun j hj => ?_, ?_⟩
          · have h3 : vV ⟨(a, c), hca⟩ < vV ⟨(a, k), hka⟩ :=
              vV_lt_vV hca hka (by simp only [Fin.lt_def] at hck hka; omega)
            have h4 : vV ⟨(a, c), hca⟩ < vV ⟨(k, c), hck⟩ :=
              vV_lt_vV hca hck (by simp only [Fin.lt_def] at hck hka; omega)
            have e1 : ¬ vV ⟨(a, k), hka⟩ = j := fun h' => lt_irrefl _ (hj.trans (h' ▸ h3))
            have e2 : ¬ vV ⟨(k, c), hck⟩ = j := fun h' => lt_irrefl _ (hj.trans (h' ▸ h4))
            have e3 : ¬ vV ⟨(a, c), hca⟩ = j := fun h' => lt_irrefl _ (h' ▸ hj)
            change (Finsupp.single _ 1 + Finsupp.single _ 1 : MVar n →₀ ℕ) j =
              (Finsupp.single _ 1 : MVar n →₀ ℕ) j
            rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
              Finsupp.single_apply, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]
            rfl
          · have e1 : ¬ vV ⟨(a, k), hka⟩ = vV ⟨(a, c), hca⟩ := by
              intro h5
              have := congrArg (fun x : MVar n => match x with
                | Sum.inl p => (p.1.2 : ℕ) | Sum.inr _ => 0) h5
              simp only [vV] at this
              exact hkc (Fin.ext this)
            have e2 : ¬ vV ⟨(k, c), hck⟩ = vV ⟨(a, c), hca⟩ := by
              intro h5
              have := congrArg (fun x : MVar n => match x with
                | Sum.inl p => (p.1.1 : ℕ) | Sum.inr _ => 0) h5
              simp only [vV] at this
              simp only [Fin.lt_def] at hka; omega
            change (Finsupp.single _ 1 + Finsupp.single _ 1 : MVar n →₀ ℕ) _ <
              (Finsupp.single _ 1 : MVar n →₀ ℕ) _
            rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
              Finsupp.single_apply, ite_eq_left rfl, ite_eq_right e1, ite_eq_right e2]
            exact Nat.zero_lt_one
        · have hkc' : k < c := lt_of_le_of_ne (not_lt.1 hck) hkc
          rw [nbInvF_apply_of_lt hkc', mul_zero] at ht
          simp at ht
      · rw [dite_eq_right hka, zero_mul] at ht
        simp at ht
    obtain ⟨h1, h2⟩ := degree_add_of_support_lt hrest
    rw [hsplit, h1, h2, hlead]
    refine ⟨rfl, ?_⟩
    rw [MonomialOrder.leadingCoeff_neg, MonomialOrder.leadingCoeff_X]

/-! ## The entries of `Φ` -/

/-- `U = (nb Ξᵀ)_{strictly upper}`. -/
def UF : Matrix (Fin n) (Fin n) (Pol n) := upPart (nbF * xiMatᵀ)

/-- `Φ = nb⁻¹ U nb`. -/
def PhiF : Matrix (Fin n) (Fin n) (Pol n) := nbInvF * UF * nbF

/-- The terms of `Φ_{ab}`. -/
def phiTerm (a b l i k : Fin n) : Pol n :=
  if i < l then
    (if h : k < l then nbInvF a i * nbF i k * nbF l b * X (xV ⟨(l, k), h⟩) else 0)
  else 0

theorem PhiF_apply (a b : Fin n) : PhiF a b = ∑ l, ∑ i, ∑ k, phiTerm a b l i k := by
  rw [PhiF, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [UF, upPart, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, xiMat,
    lowMatG, phiTerm]
  by_cases hil : i < l
  · simp only [hil, ↓reduceIte, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hkl : k < l
    · simp only [hkl, ↓reduceDIte]; ring
    · simp only [hkl, ↓reduceDIte]; ring
  · simp [hil]

theorem single_xV_apply (q₀ q' : Lw n) :
    (Finsupp.single (xV q₀) 1 : MVar n →₀ ℕ) (xV q') = if q' = q₀ then 1 else 0 := by
  rw [Finsupp.single_apply]
  by_cases h : q' = q₀
  · subst h; simp
  · have h1 : ¬ (xV q₀ = xV q') := fun h' => h (Sum.inr_injective h').symm
    rw [ite_eq_right h1, ite_eq_right h]

theorem single_vV_apply_xV (p q' : Lw n) :
    (Finsupp.single (vV p) 1 : MVar n →₀ ℕ) (xV q') = 0 := by
  rw [Finsupp.single_apply, ite_eq_right]
  intro h; exact absurd h (by simp [vV, xV])

theorem term_support_lt {f : Pol n} (hf : VOnly f) {q q₀ : Lw n} (hq : xV q₀ < xV q)
    {D : MVar n →₀ ℕ} (hD : ∀ q', D (xV q') = if q' = q₀ then 1 else 0) :
    ∀ t ∈ (f * X (xV q)).support, t ≺[ord n] D := fun t ht =>
  lt_of_xV_lt hq (support_X_mul_apply hf q (by rwa [mul_comm] at ht)) hD

/-- The non-leading terms of an entry: either zero or with a less significant dual
coordinate. -/
theorem phiTerm_support_lt (a b l i k : Fin n) {q₀ : Lw n} {D : MVar n →₀ ℕ}
    (hD : ∀ q', D (xV q') = if q' = q₀ then 1 else 0)
    (hlt : ∀ (h : k < l), i < l → i ≤ a → k ≤ i → b ≤ l → xV q₀ < xV ⟨(l, k), h⟩) :
    ∀ t ∈ (phiTerm a b l i k).support, t ≺[ord n] D := by
  intro t ht
  unfold phiTerm at ht
  by_cases hil : i < l
  · rw [ite_eq_left hil] at ht
    by_cases hkl : k < l
    · rw [dite_eq_left hkl] at ht
      by_cases hai : a < i
      · rw [nbInvF_apply_of_lt hai] at ht; simp at ht
      by_cases hik : i < k
      · rw [nbF_apply_of_lt hik] at ht; simp at ht
      by_cases hlb : l < b
      · rw [nbF_apply_of_lt hlb] at ht; simp at ht
      exact term_support_lt (((vOnly_nbInvF a i).mul (vOnly_nbF i k)).mul (vOnly_nbF l b))
        (hlt hkl hil (not_lt.1 hai) (not_lt.1 hik) (not_lt.1 hlb)) hD t ht
    · rw [dite_eq_right hkl] at ht; simp at ht
  · rw [ite_eq_right hil] at ht; simp at ht

theorem sum_triple_eq {M : Type*} [AddCommMonoid M] (f : Fin n → Fin n → Fin n → M) :
    ∑ l, ∑ i, ∑ k, f l i k = ∑ x : Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_prod_type]

/-- **Upper entries.** For `a < b`, `Φ_{ab}` has leading monomial `ξ_{ba}`. -/
theorem PhiF_upper (a b : Fin n) (hab : a < b) :
    (ord n).degree (PhiF a b) = Finsupp.single (xV ⟨(b, a), hab⟩) 1 ∧
      (ord n).leadingCoeff (PhiF a b) = 1 := by
  classical
  set x₀ : Fin n × Fin n × Fin n := (b, a, a)
  have hx₀ : phiTerm a b b a a = X (xV ⟨(b, a), hab⟩) := by
    rw [phiTerm, ite_eq_left hab, dite_eq_left hab, nbInvF_apply_self, nbF_apply_self,
      nbF_apply_self, one_mul, one_mul, one_mul]
  have hdeg : (ord n).degree (X (xV ⟨(b, a), hab⟩) : Pol n) =
      Finsupp.single (xV ⟨(b, a), hab⟩) 1 := MonomialOrder.degree_X
  rw [PhiF_apply, sum_triple_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)]
  simp only [x₀, hx₀]
  have hrest : ∀ t ∈ (∑ x ∈ Finset.univ.erase (b, a, a),
      phiTerm a b x.1 x.2.1 x.2.2).support,
        t ≺[ord n] (ord n).degree (X (xV ⟨(b, a), hab⟩) : Pol n) := by
    rw [hdeg]
    refine support_sum_lt _ _ fun x hx => ?_
    refine phiTerm_support_lt a b x.1 x.2.1 x.2.2 (single_xV_apply _)
      fun hkl hil hia hki hbl => ?_
    rcases lt_or_eq_of_le hbl with hbl | rfl
    · exact xV_lt_xV hab hkl (Or.inl hbl)
    · rcases lt_or_eq_of_le (hki.trans hia) with hka | hka
      · exact xV_lt_xV hab hkl (Or.inr ⟨rfl, hka⟩)
      · exfalso
        have hi : x.2.1 = a := le_antisymm hia (hka ▸ hki)
        exact Finset.ne_of_mem_erase hx (Prod.ext rfl (Prod.ext hi hka))
  obtain ⟨h1, h2⟩ := degree_add_of_support_lt hrest
  rw [h1, h2, hdeg, MonomialOrder.leadingCoeff_X]
  exact ⟨rfl, rfl⟩

/-- **Lower entries.** For `c < a` and `c₁ = c + 1`, `Φ_{a c₁}` has leading monomial
`ξ_{c₁ c} v_{a c}`. -/
theorem PhiF_lower (a c c₁ : Fin n) (hca : c < a) (hc₁ : (c₁ : ℕ) = c + 1) :
    (ord n).degree (PhiF a c₁) =
        Finsupp.single (xV ⟨(c₁, c), by simp [Fin.lt_def, hc₁]⟩) 1 +
          Finsupp.single (vV ⟨(a, c), hca⟩) 1 ∧
      (ord n).leadingCoeff (PhiF a c₁) = -1 := by
  classical
  have hcc : c < c₁ := by simp [Fin.lt_def, hc₁]
  set q₀ : Lw n := ⟨(c₁, c), hcc⟩
  obtain ⟨hdi, hli⟩ := degree_nbInvF a c hca
  have hne : nbInvF a c ≠ 0 := by
    intro h0; rw [h0, MonomialOrder.leadingCoeff_zero] at hli; norm_num at hli
  have hx₀ : phiTerm a c₁ c₁ c c = nbInvF a c * X (xV q₀) := by
    rw [phiTerm, ite_eq_left hcc, dite_eq_left hcc, nbF_apply_self, nbF_apply_self, mul_one,
      mul_one]
  have hdeg : (ord n).degree (nbInvF a c * X (xV q₀)) =
      Finsupp.single (xV q₀) 1 + Finsupp.single (vV ⟨(a, c), hca⟩) 1 := by
    rw [MonomialOrder.degree_mul hne (X_ne_zero _), hdi, MonomialOrder.degree_X, add_comm]
  have hD : ∀ q', (Finsupp.single (xV q₀) 1 + Finsupp.single (vV ⟨(a, c), hca⟩) 1 :
      MVar n →₀ ℕ) (xV q') = if q' = q₀ then 1 else 0 := by
    intro q'
    rw [Finsupp.add_apply, single_xV_apply, single_vV_apply_xV, add_zero]
  rw [PhiF_apply, sum_triple_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (c₁, c, c))]
  simp only [hx₀]
  have hrest : ∀ t ∈ (∑ x ∈ Finset.univ.erase (c₁, c, c),
      phiTerm a c₁ x.1 x.2.1 x.2.2).support,
        t ≺[ord n] (ord n).degree (nbInvF a c * X (xV q₀)) := by
    rw [hdeg]
    refine support_sum_lt _ _ fun x hx => ?_
    obtain ⟨l, i, k⟩ := x
    refine phiTerm_support_lt a c₁ l i k hD fun hkl hil hia hki hbl => ?_
    rcases lt_or_eq_of_le hbl with hbl | rfl
    · exact xV_lt_xV hcc hkl (Or.inl hbl)
    · have hkc : k ≤ c := by
        simp only [Fin.lt_def, Fin.le_def, hc₁] at hkl ⊢; omega
      rcases lt_or_eq_of_le hkc with hkc | rfl
      · exact xV_lt_xV hcc hkl (Or.inr ⟨rfl, hkc⟩)
      · exfalso
        have hi : i = k := by
          apply le_antisymm
          · simp only [Fin.lt_def, Fin.le_def, hc₁] at hil ⊢; omega
          · exact hki
        exact Finset.ne_of_mem_erase hx (by rw [hi])
  obtain ⟨h1, h2⟩ := degree_add_of_support_lt hrest
  rw [h1, h2, hdeg, MonomialOrder.leadingCoeff_mul, hli, MonomialOrder.leadingCoeff_X, mul_one]
  exact ⟨rfl, rfl⟩

/-! ## The `2N` symbols and their products -/

/-- The successor of the column of a position (still at most its row). -/
def succCol (p : Lw n) : Fin n :=
  ⟨p.1.2 + 1, by have h1 := p.1.1.2; have h2 := p.2; simp only [Fin.lt_def] at h2; omega⟩

theorem col_lt_succCol (p : Lw n) : p.1.2 < succCol p := by
  simp [succCol, Fin.lt_def]

/-- The chosen entries of `Φ`: `Φ_{jk}` for the position `(k, j)` (`inr`), and `Φ_{a, c+1}` for
the position `(a, c)` (`inl`). -/
def symb : Lw n ⊕ Lw n → Pol n
  | Sum.inr p => PhiF p.1.2 p.1.1
  | Sum.inl p => PhiF p.1.1 (succCol p)

/-- Their leading monomials. -/
def symbDeg : Lw n ⊕ Lw n → MVar n →₀ ℕ
  | Sum.inr p => Finsupp.single (xV p) 1
  | Sum.inl p => Finsupp.single (xV ⟨(succCol p, p.1.2), col_lt_succCol p⟩) 1 +
      Finsupp.single (vV p) 1

theorem degree_symb (i : Lw n ⊕ Lw n) :
    (ord n).degree (symb i) = symbDeg i ∧ (ord n).leadingCoeff (symb i) ≠ 0 := by
  rcases i with ⟨⟨a, c⟩, h⟩ | ⟨⟨k, j⟩, h⟩
  · obtain ⟨h1, h2⟩ := PhiF_lower a c (succCol ⟨(a, c), h⟩) h rfl
    refine ⟨h1, ?_⟩
    rw [symb, h2]; norm_num
  · obtain ⟨h1, h2⟩ := PhiF_upper j k h
    refine ⟨h1, ?_⟩
    rw [symb, h2]; norm_num

theorem symb_ne_zero (i : Lw n ⊕ Lw n) : symb i ≠ 0 := fun h => (degree_symb i).2 (by
  rw [h, MonomialOrder.leadingCoeff_zero])

/-- The products of powers of the symbols. -/
def prodSymb (α : Lw n ⊕ Lw n → ℕ) : Pol n := ∏ i, symb i ^ α i

theorem degree_prodSymb (α : Lw n ⊕ Lw n → ℕ) :
    (ord n).degree (prodSymb α) = ∑ i, α i • symbDeg i := by
  rw [prodSymb, MonomialOrder.degree_prod fun i _ => pow_ne_zero _ (symb_ne_zero i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MonomialOrder.degree_pow, (degree_symb i).1]

theorem symbDeg_apply_vV (i : Lw n ⊕ Lw n) (q : Lw n) :
    symbDeg i (vV q) = if i = Sum.inl q then 1 else 0 := by
  classical
  rcases i with p | p
  · rw [symbDeg, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      ite_eq_right (by simp [vV, xV]), zero_add]
    by_cases h : p = q
    · subst h; simp
    · have h1 : ¬ vV p = vV q := fun h' => h (Sum.inl_injective h')
      have h2 : ¬ (Sum.inl p : Lw n ⊕ Lw n) = Sum.inl q := fun h' => h (Sum.inl_injective h')
      simp only [h1, h2, ↓reduceIte]
  · rw [symbDeg, Finsupp.single_apply, ite_eq_right (by simp [vV, xV]),
      ite_eq_right (by simp)]

theorem degSum_apply_vV (α : Lw n ⊕ Lw n → ℕ) (q : Lw n) :
    (∑ i, α i • symbDeg i) (vV q) = α (Sum.inl q) := by
  classical
  rw [Finsupp.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_single (Sum.inl q)]
  · rw [Finsupp.smul_apply, symbDeg_apply_vV, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro i _ hi
    rw [Finsupp.smul_apply, symbDeg_apply_vV, ite_eq_right hi, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem degSum_injective :
    Function.Injective fun α : Lw n ⊕ Lw n → ℕ => ∑ i, α i • symbDeg i := by
  classical
  intro α β h
  simp only at h
  have hl : ∀ q, α (Sum.inl q) = β (Sum.inl q) := fun q => by
    rw [← degSum_apply_vV α q, ← degSum_apply_vV β q, h]
  have hsplit : ∀ γ : Lw n ⊕ Lw n → ℕ, ∑ i, γ i • symbDeg i =
      (∑ q, γ (Sum.inl q) • symbDeg (Sum.inl q)) +
        ∑ q, γ (Sum.inr q) • Finsupp.single (xV q) 1 := fun γ => by
    rw [Fintype.sum_sum_type]; rfl
  have h2 := h
  rw [hsplit α, hsplit β] at h2
  simp only [hl] at h2
  have h3 := add_left_cancel h2
  funext i
  rcases i with q | q
  · exact hl q
  · have := congrArg (fun f : MVar n →₀ ℕ => f (xV q)) h3
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      single_xV_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] at this
    simpa [Finset.sum_ite_eq] using this

/-- **Polynomials with distinct leading monomials are linearly independent.** -/
theorem linearIndependent_of_degree_injective {ι : Type*} (f : ι → Pol n) (hf : ∀ i, f i ≠ 0)
    (hinj : Function.Injective fun i => (ord n).degree (f i)) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  set s' := s.filter (fun j => g j ≠ 0)
  have hne : s'.Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hmax⟩ := s'.exists_max_image (fun j => (ord n).toSyn ((ord n).degree (f j))) hne
  have hjs := (Finset.mem_filter.1 hj).1
  have hcoeff := congrArg (fun p : Pol n => p.coeff ((ord n).degree (f j))) hg
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  rw [coeff_sum, Finset.sum_eq_single j] at hcoeff
  · rw [coeff_smul, smul_eq_mul] at hcoeff
    exact mul_ne_zero (Finset.mem_filter.1 hj).2 ((ord n).coeff_degree_ne_zero_iff.2 (hf j)) hcoeff
  · intro k hk hkj
    rw [coeff_smul]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hmax k (Finset.mem_filter.2 ⟨hk, hgk⟩)
      have hlt : (ord n).degree (f k) ≺[ord n] (ord n).degree (f j) :=
        lt_of_le_of_ne hle fun h => hkj (hinj ((ord n).toSyn.injective h))
      rw [(ord n).coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'; exact absurd hjs hj'

/-- **The products of the symbols are linearly independent.** -/
theorem linearIndependent_prodSymb : LinearIndependent ℂ (prodSymb (n := n)) := by
  refine linearIndependent_of_degree_injective _ (fun α => ?_) ?_
  · exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (symb_ne_zero i)
  · intro α β h
    simp only [degree_prodSymb] at h
    exact degSum_injective h

end Langlands.Archimedean.MomentSymbols
