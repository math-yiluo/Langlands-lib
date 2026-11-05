import Langlands.GroupScheme.SplitExistence.OrderedProduct
import Langlands.GroupScheme.SplitExistence.TitsFinal
import Langlands.GroupScheme.GeneralLinearDualNumber

/-! # Recovering the coordinates of an ordered product

Over any commutative algebra `R` over a field `F`, the coefficients `c γ` of an ordered product
`∏_{γ ∈ posList} x_γ(c γ)` are polynomial functions of its matrix entries: going along the list,
`c γ` is the `(p_γ, q_γ)` entry of the remaining product divided by the entry of `e γ 1`, for a
fixed position where `e γ 1` is nonzero in `F`. Only the term of degree one in `x_γ` can reach
that position, because the remaining roots are not smaller than `γ` for `ℓ` and `γ` is not a
positive combination of them. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section Ring

variable {R : Type*} [CommRing R]

/-- The root exponential `x_j(s)` as a matrix over `R`. -/
def xm (j : J) (s : R) : Matrix (Fin D.n) (Fin D.n) R := divExp (D.e j) s

/-- The ordered product along a list of roots, as a matrix over `R`. -/
def opm (l : List J) (c : J → R) : Matrix (Fin D.n) (Fin D.n) R :=
  (l.map fun j => D.xm j (c j)).prod

theorem opm_cons (j : J) (l : List J) (c : J → R) :
    D.opm (j :: l) c = D.xm j (c j) * D.opm l c := by
  simp [opm]

/-- Unipotence with weight differences in `S`: diagonal entries `1`, and nonzero off-diagonal
entries `(e, q)` have `wt e - wt q ∈ S`. -/
def IsSUnip (S : Set X) (M : Matrix (Fin D.n) (Fin D.n) R) : Prop :=
  (∀ e, M e e = 1) ∧ ∀ e q, e ≠ q → M e q ≠ 0 → D.wt e - D.wt q ∈ S

variable {D}

theorem IsSUnip.mul {S : Set X} (hadd : ∀ σ ∈ S, ∀ τ ∈ S, σ + τ ∈ S)
    (hpos : ∀ σ ∈ S, 0 < D.ℓ σ) {M N : Matrix (Fin D.n) (Fin D.n) R} (hM : D.IsSUnip S M)
    (hN : D.IsSUnip S N) : D.IsSUnip S (M * N) := by
  refine ⟨fun e => ?_, fun e q heq h => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single e]
    · rw [hM.1, hN.1, mul_one]
    · intro f _ hfe
      by_contra hne
      have h1 := hM.2 e f (Ne.symm hfe) (left_ne_zero_of_mul hne)
      have h2 := hN.2 f e hfe (right_ne_zero_of_mul hne)
      have := hpos _ (hadd _ h1 _ h2)
      simp at this
    · simp
  · rw [Matrix.mul_apply] at h
    obtain ⟨f, -, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases hef : e = f
    · subst hef
      exact hN.2 e q heq (right_ne_zero_of_mul hf)
    · by_cases hfq : f = q
      · subst hfq
        exact hM.2 e f hef (left_ne_zero_of_mul hf)
      · have h1 := hM.2 e f hef (left_ne_zero_of_mul hf)
        have h2 := hN.2 f q hfq (right_ne_zero_of_mul hf)
        have := hadd _ h1 _ h2
        rwa [sub_add_sub_cancel] at this

variable (D)

theorem isSUnip_xm {S : Set X} {δ : J} (hδ : 0 < D.ℓ (P.root δ))
    (hS : ∀ a : ℕ, 1 ≤ a → a • P.root δ ∈ S) (s : R) : D.IsSUnip S (D.xm δ s) := by
  refine ⟨fun e => ?_, fun e q heq h => ?_⟩
  · simp only [xm, divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [Finset.sum_eq_single 0]
    · simp [D.e_zero]
    · intro a _ ha
      have : D.e δ a e e = 0 := by
        by_contra hne
        have hw := D.e_weight δ a e e hne
        have hℓ := congrArg D.ℓ hw
        rw [map_add, map_nsmul, nsmul_eq_mul] at hℓ
        have : (a : ℤ) * D.ℓ (P.root δ) = 0 := by linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact ha (by exact_mod_cast h0)
        · exact hδ.ne' h0
      simp [this]
    · simp
  · simp only [xm, divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul] at h
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have he : D.e δ a e q ≠ 0 := by
      intro h0
      simp [h0] at ha
    have hw := D.e_weight δ a e q he
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rw [D.e_zero, one_apply_ne heq] at he
      exact absurd rfl he
    · rw [hw, add_sub_cancel_left]
      exact hS a hapos

/-- The positive combinations of the roots of `l` with positive `ℓ`. -/
def sSet (l : List J) : Set X :=
  {σ | σ ∈ AddSubmonoid.closure (P.root '' {δ | δ ∈ l}) ∧ 0 < D.ℓ σ}

theorem sSet_add (l : List J) : ∀ σ ∈ D.sSet l, ∀ τ ∈ D.sSet l, σ + τ ∈ D.sSet l :=
  fun _ hσ _ hτ => ⟨AddSubmonoid.add_mem _ hσ.1 hτ.1, by rw [map_add]; linarith [hσ.2, hτ.2]⟩

theorem sSet_pos (l : List J) : ∀ σ ∈ D.sSet l, 0 < D.ℓ σ := fun _ h => h.2

theorem isSUnip_one (S : Set X) : D.IsSUnip S (1 : Matrix (Fin D.n) (Fin D.n) R) :=
  ⟨fun e => one_apply_eq e, fun _ _ heq h => absurd (one_apply_ne heq) h⟩

theorem isSUnip_opm (l : List J) (hl : ∀ δ ∈ l, 0 < D.ℓ (P.root δ)) :
    ∀ (l' : List J), (∀ δ ∈ l', δ ∈ l) → ∀ c : J → R, D.IsSUnip (D.sSet l) (D.opm l' c)
  | [], _, c => by simpa [opm] using D.isSUnip_one (D.sSet l)
  | δ :: l', h, c => by
    rw [opm_cons]
    have hδ := h δ (List.mem_cons_self ..)
    refine IsSUnip.mul (D.sSet_add l) (D.sSet_pos l) (D.isSUnip_xm (hl δ hδ) (fun a ha => ?_) _)
      (isSUnip_opm l hl l' (fun d hd => h d (List.mem_cons_of_mem _ hd)) c)
    refine ⟨AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure
      (show P.root δ ∈ P.root '' {δ | δ ∈ l} from ⟨δ, hδ, rfl⟩)) a, ?_⟩
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_pos (by exact_mod_cast ha) (hl δ hδ)

/-- A root `γ` is not a positive combination of roots of a list not containing it whose levels
are at least that of `γ`. -/
theorem root_not_mem_sSet {γ : J} {l : List J} (hγ : 0 < D.ℓ (P.root γ))
    (hl : ∀ δ ∈ l, D.ℓ (P.root γ) ≤ D.ℓ (P.root δ)) (hγl : γ ∉ l) :
    P.root γ ∉ D.sSet l := by
  rintro ⟨hmem, -⟩
  have key : ∀ σ ∈ AddSubmonoid.closure (P.root '' {δ | δ ∈ l}),
      σ = 0 ∨ (∃ δ ∈ l, σ = P.root δ) ∨ 2 * D.ℓ (P.root γ) ≤ D.ℓ σ := by
    intro σ hσ
    induction hσ using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨δ, hδ, rfl⟩ := hx
      exact Or.inr (Or.inl ⟨δ, hδ, rfl⟩)
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      have bx : x = 0 ∨ D.ℓ (P.root γ) ≤ D.ℓ x := by
        rcases hx with h | ⟨δ, hδ, rfl⟩ | h
        · exact Or.inl h
        · exact Or.inr (hl δ hδ)
        · exact Or.inr (by linarith)
      have by' : y = 0 ∨ D.ℓ (P.root γ) ≤ D.ℓ y := by
        rcases hy with h | ⟨δ, hδ, rfl⟩ | h
        · exact Or.inl h
        · exact Or.inr (hl δ hδ)
        · exact Or.inr (by linarith)
      rcases bx with rfl | bx
      · rw [zero_add]; exact hy
      · rcases by' with rfl | by'
        · rw [add_zero]; exact hx
        · exact Or.inr (Or.inr (by rw [map_add]; linarith))
  rcases key _ hmem with h | ⟨δ, hδ, h⟩ | h
  · rw [h, map_zero] at hγ
    exact lt_irrefl _ hγ
  · exact hγl (P.root.injective h ▸ hδ)
  · linarith

/-- **The entry formula.** For `γ` before a list `l` of not-smaller roots, the entry of
`x_γ(s) ∏_{l} x(c)` at a position of weight difference `root γ` is `s (e γ 1)`. -/
theorem xm_mul_opm_apply {γ : J} {l : List J} (hγ : 0 < D.ℓ (P.root γ))
    (hlpos : ∀ δ ∈ l, 0 < D.ℓ (P.root δ))
    (hl : ∀ δ ∈ l, D.ℓ (P.root γ) ≤ D.ℓ (P.root δ)) (hγl : γ ∉ l) (s : R) (c : J → R)
    {p q : Fin D.n} (hpq : D.wt p = D.wt q + P.root γ) :
    (D.xm γ s * D.opm l c) p q = s * (D.e γ 1 p q : R) := by
  have hQ := D.isSUnip_opm l hlpos l (fun _ h => h) c
  have hnot := D.root_not_mem_sSet hγ hl hγl
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [hQ.1, mul_one]
    simp only [xm, divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      eq_intCast]
    rw [Finset.sum_eq_single 1]
    · rw [pow_one]
    · intro a _ ha
      have : D.e γ a p q = 0 := by
        by_contra hne
        have hw := D.e_weight γ a p q hne
        rw [hpq] at hw
        have hℓ := congrArg D.ℓ hw
        rw [map_add, map_add, map_nsmul, nsmul_eq_mul] at hℓ
        have : ((a : ℤ) - 1) * D.ℓ (P.root γ) = 0 := by linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact ha (by omega)
        · exact hγ.ne' h0
      simp [this]
    · intro h1
      exfalso
      simp only [Finset.mem_range, not_lt] at h1
      have := q.2
      omega
  · intro f _ hfq
    by_contra hne
    have hQf := hQ.2 f q hfq (right_ne_zero_of_mul hne)
    have hx := left_ne_zero_of_mul hne
    simp only [xm, divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul] at hx
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have he : D.e γ a p f ≠ 0 := by
      intro h0
      simp [h0] at ha
    have hw := D.e_weight γ a p f he
    have hdiff : D.wt f - D.wt q = P.root γ - a • P.root γ := by
      rw [hpq] at hw
      have : D.wt f = D.wt q + P.root γ - a • P.root γ := by rw [hw]; abel
      rw [this]; abel
    have hℓ := hQf.2
    rw [hdiff, map_sub, map_nsmul, nsmul_eq_mul] at hℓ
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rw [zero_smul, sub_zero] at hdiff
      exact hnot (hdiff ▸ hQf)
    · have : (1 : ℤ) ≤ a := by exact_mod_cast hapos
      nlinarith
  · simp

end Ring

theorem xm_zero {R : Type*} [CommRing R] (j : J) : D.xm j (0 : R) = 1 :=
  divExp_zero (D.isDividedPowerFamily j)

theorem xm_mul {R : Type*} [CommRing R] (j : J) (s t : R) :
    D.xm j s * D.xm j t = D.xm j (s + t) :=
  divExp_mul (D.isDividedPowerFamily j) s t

section Field

variable (F : Type u) [Field F]

theorem exists_entry_ne_zero_e (j : J) : ∃ pq : Fin D.n × Fin D.n, (D.e j 1 pq.1 pq.2 : F) ≠ 0 := by
  by_contra h
  push Not at h
  apply D.e_one_map_ne_zero_field (K := F) j
  ext p q
  simpa using h (p, q)

/-- A position where `e j 1` is nonzero in `F`. -/
def posEntry (j : J) : Fin D.n × Fin D.n := (D.exists_entry_ne_zero_e F j).choose

theorem posEntry_spec (j : J) : (D.e j 1 (D.posEntry F j).1 (D.posEntry F j).2 : F) ≠ 0 :=
  (D.exists_entry_ne_zero_e F j).choose_spec

theorem posEntry_weight (j : J) :
    D.wt (D.posEntry F j).1 = D.wt (D.posEntry F j).2 + P.root j := by
  have h := D.e_weight j 1 _ _ (fun h0 => D.posEntry_spec F j (by rw [h0]; simp))
  rwa [one_smul] at h

variable {F} {R : Type*} [CommRing R] [Algebra F R]

/-- The scalar `1 / (e j 1)(p, q)` in `R`. -/
def κ (j : J) : R := algebraMap F R ((D.e j 1 (D.posEntry F j).1 (D.posEntry F j).2 : F))⁻¹

theorem κ_mul (j : J) :
    D.κ (F := F) (R := R) j * (D.e j 1 (D.posEntry F j).1 (D.posEntry F j).2 : R) = 1 := by
  rw [κ, ← map_intCast (algebraMap F R), ← map_mul, inv_mul_cancel₀ (D.posEntry_spec F j),
    map_one]

variable (F) [DecidableEq J]

/-- Reading off the coefficients along a list of roots. -/
def retrAux : List J → Matrix (Fin D.n) (Fin D.n) R → (J → R) → (J → R)
  | [], _, acc => acc
  | γ :: l, h, acc =>
    retrAux l (D.xm γ (-(D.κ (F := F) γ * h (D.posEntry F γ).1 (D.posEntry F γ).2)) * h)
      (Function.update acc γ (D.κ (F := F) γ * h (D.posEntry F γ).1 (D.posEntry F γ).2))

theorem retrAux_opm :
    ∀ (l : List J), l.Nodup → l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)) →
    (∀ δ ∈ l, 0 < D.ℓ (P.root δ)) → ∀ (c acc : J → R),
      D.retrAux F l (D.opm l c) acc = fun j => if j ∈ l then c j else acc j
  | [], _, _, _, c, acc => by funext j; simp [retrAux]
  | γ :: l, hnd, hsort, hpos, c, acc => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hsort
    have hγ := hpos γ (List.mem_cons_self ..)
    have hlpos : ∀ δ ∈ l, 0 < D.ℓ (P.root δ) := fun δ hδ => hpos δ (List.mem_cons_of_mem _ hδ)
    have hentry : D.opm (γ :: l) c (D.posEntry F γ).1 (D.posEntry F γ).2 =
        c γ * (D.e γ 1 (D.posEntry F γ).1 (D.posEntry F γ).2 : R) := by
      rw [opm_cons]
      exact D.xm_mul_opm_apply hγ hlpos hsort.1 hnd.1 (c γ) c (D.posEntry_weight F γ)
    have ha : D.κ (F := F) γ * D.opm (γ :: l) c (D.posEntry F γ).1 (D.posEntry F γ).2 = c γ := by
      rw [hentry, mul_comm (c γ), ← mul_assoc, D.κ_mul, one_mul]
    rw [retrAux, ha, opm_cons, ← mul_assoc, D.xm_mul, neg_add_cancel, D.xm_zero, one_mul,
      retrAux_opm l hnd.2 hsort.2 hlpos c]
    funext j
    by_cases hj : j ∈ l
    · simp [hj]
    · by_cases hjγ : j = γ
      · subst hjγ; simp [hj]
      · simp [hj, hjγ]

theorem retrAux_map {R' : Type*} [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') :
    ∀ (l : List J) (h : Matrix (Fin D.n) (Fin D.n) R) (acc : J → R),
      D.retrAux F l (h.map f) (f ∘ acc) = f ∘ D.retrAux F l h acc
  | [], _, _ => rfl
  | γ :: l, h, acc => by
    have hκ : f (D.κ (F := F) (R := R) γ) = D.κ (F := F) (R := R') γ := by
      rw [κ, κ, AlgHom.commutes]
    have hmap : (D.xm γ (-(D.κ (F := F) γ * h (D.posEntry F γ).1 (D.posEntry F γ).2)) * h).map f =
        D.xm γ (-(D.κ (F := F) γ * (h.map f) (D.posEntry F γ).1 (D.posEntry F γ).2)) * h.map f := by
      rw [Matrix.map_mul, xm, xm]
      congr 1
      refine (divExp_map (f : R →+* R') _).trans ?_
      congr 1
      change f (-(D.κ γ * h _ _)) = _
      rw [map_neg, map_mul, hκ]
      rfl
    simp only [retrAux]
    rw [← retrAux_map f l, hmap, Function.comp_update, map_mul, hκ, Matrix.map_apply]

section PosList

variable [Fintype J]

/-- The coefficients of an ordered product along `posList`. -/
def retr (g : Matrix (Fin D.n) (Fin D.n) R) : J → R := D.retrAux F D.posList g 0

theorem retr_opm (c : J → R) :
    D.retr F (D.opm D.posList c) = fun j => if j ∈ D.posList then c j else 0 :=
  D.retrAux_opm F _ D.posList_nodup D.posList_sorted
    (fun _ hδ => D.ℓ_root_pos (D.mem_posList.1 hδ)) c 0

omit [DecidableEq J] [Fintype J] in
theorem opm_zero (l : List J) : D.opm l (0 : J → R) = 1 := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [opm_cons, Pi.zero_apply, xm_zero, one_mul, ih]

theorem retr_one : D.retr F (1 : Matrix (Fin D.n) (Fin D.n) R) = 0 := by
  rw [← D.opm_zero D.posList, retr_opm]
  funext j
  simp

theorem retr_map {R' : Type*} [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (g : Matrix (Fin D.n) (Fin D.n) R) : D.retr F (g.map f) = f ∘ D.retr F g := by
  rw [retr, retr, ← retrAux_map]
  congr 1
  funext j
  simp

end PosList

end Field

section DualNumber

variable {F : Type u} [Field F]

open TrivSqZeroExt Langlands.GroupScheme.GeneralLinear.DualNumber

/-- The root operator `e j 1` over `F`. -/
def eF (j : J) : Matrix (Fin D.n) (Fin D.n) F := (D.e j 1).map (Int.castRingHom F)

theorem xm_inr (j : J) (c : F) :
    D.xm j (inr c : DualNumber F) = 1 + epsilonMatrix (c • D.eF j) := by
  by_cases hn : D.n = 0
  · have : IsEmpty (Fin D.n) := by rw [hn]; infer_instance
    exact Matrix.ext fun p _ => isEmptyElim p
  refine Matrix.ext fun p q => ?_
  simp only [xm, divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.add_apply, epsilonMatrix_apply, eF]
  rw [Finset.sum_eq_add (0 : ℕ) 1 (by norm_num)]
  · rw [pow_zero, one_mul, pow_one, D.e_zero]
    by_cases hpq : p = q
    · subst hpq
      simp only [Matrix.one_apply_eq]
      ext <;> simp [mul_comm]
    · simp only [Matrix.one_apply_ne hpq]
      ext <;> simp [mul_comm]
  · intro k hk h01
    have hk2 : 2 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [pow_add, sq, TrivSqZeroExt.inr_mul_inr, mul_zero, zero_mul]
  · intro h; simp at h
  · intro h; simp at h; omega

theorem opm_inr (l : List J) (c : J → F) :
    D.opm l (fun j => (inr (c j) : DualNumber F)) =
      1 + epsilonMatrix ((l.map fun j => c j • D.eF j).sum) := by
  induction l with
  | nil => simp [opm]
  | cons j l ih =>
    rw [opm_cons, ih, D.xm_inr, one_add_epsilonMatrix_mul, List.map_cons, List.sum_cons]

theorem epsilonMatrix_injective :
    Function.Injective (epsilonMatrix : Matrix (Fin D.n) (Fin D.n) F → _) := by
  intro X Y h
  ext p q
  have := congrArg (fun M => (M p q).snd) h
  simpa using this

variable [Fintype J] [DecidableEq J]

/-- **First-order part of an ordered product.** If `1 + εX` is the ordered product of its own
recovered coefficients, then `X` is a linear combination of the `e γ 1` for positive roots `γ`. -/
theorem mem_span_of_opm_retr (X : Matrix (Fin D.n) (Fin D.n) F)
    (h : D.opm D.posList (D.retr F (1 + epsilonMatrix X)) = 1 + epsilonMatrix X) :
    X ∈ Submodule.span F (Set.range fun j : {j : J // b.IsPos j} => D.eF (F := F) j) := by
  set r := D.retr F (1 + epsilonMatrix X) with hr
  have hfst : ∀ j, (r j).fst = 0 := by
    intro j
    have h1 := congrFun (D.retr_map (F := F) (fstHom F F F) (1 + epsilonMatrix X)) j
    have h2 : (1 + epsilonMatrix X).map (fstHom F F F) = 1 := by
      ext p q
      by_cases hpq : p = q
      · subst hpq; simp
      · simp [Matrix.one_apply_ne hpq]
    rw [h2, retr_one] at h1
    exact h1.symm
  have hrj : r = fun j => (inr (r j).snd : DualNumber F) := by
    funext j
    ext
    · rw [hfst j]; rfl
    · rfl
  rw [hrj, opm_inr] at h
  have hX := D.epsilonMatrix_injective (add_left_cancel h)
  rw [← hX]
  refine list_sum_mem fun M hM => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, D.mem_posList.1 hj⟩, rfl⟩)

end DualNumber


end ChevalleyData

end Langlands.GroupScheme.SplitExistence
