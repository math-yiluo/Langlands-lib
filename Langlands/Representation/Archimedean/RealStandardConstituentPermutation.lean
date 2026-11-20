import Langlands.Global.Factors.IsobaricAutomorphicRepresentation
import Langlands.Representation.Archimedean.CompactConstituentSpecialization
import Langlands.Representation.Archimedean.RealCompactExponentFamily
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof

/-!
# Constituents of reordered real standard modules

Moving the exponent of one block in an adjacent swap produces intertwining
isomorphisms at infinitely many parameters. The affine specialization theorem
then transfers each irreducible constituent of the original standard module
across the swap, and a succession of swaps treats every permutation.
-/

noncomputable section

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean ConstituentCompression RealExponentDeformation

/-- The compact and real infinitesimal generators of a real standard module. -/
def realStandardOperators (n : ℕ) (ds : List RealBlock) :
    Matrix.unitaryGroup (Fin n) ℝ ⊕ Matrix (Fin n) (Fin n) ℝ → Module.End ℂ (KF n ds) :=
  Sum.elim (fun k => realStandardRep n ds k) (fun X => realStandardLie n ds (1 ⊗ₜ X))

private theorem blockExponent_shift (z : ℂ) (b : RealBlock) :
    Langlands.LocalFactor.Archimedean.RealBlock.exponent (shiftBlock z b) = Langlands.LocalFactor.Archimedean.RealBlock.exponent b + z := by
  cases b <;> rfl

private def moeglinExponent : MoeglinDatum → ℂ
  | .character _ t => t
  | .discrete _ t => t

private theorem moeglinExponent_eq_of_mem {b : RealBlock} {a : MoeglinDatum}
    (ha : a ∈ realBlockMoeglinData b) : moeglinExponent a = Langlands.LocalFactor.Archimedean.RealBlock.exponent b := by
  cases b with
  | character d =>
    simp only [realBlockMoeglinData, List.mem_singleton] at ha
    subst a
    rfl
  | induced d =>
    by_cases h : d.weight = 0
    · simp [realBlockMoeglinData, h] at ha
      rcases ha with rfl | rfl <;> rfl
    · simp only [realBlockMoeglinData, ite_eq_right h, List.mem_singleton] at ha
      subst a
      rfl

private theorem im_eq_of_sub {s t c : ℂ} (hc : c.im = 0) (he : s - t = c) : s.im = t.im :=
  sub_eq_zero.mp (by simpa only [Complex.sub_im, hc] using congrArg Complex.im he)

private theorem moeglinIsLinked_im_eq {a b : MoeglinDatum} (h : a.IsLinked b) :
    (moeglinExponent a).im = (moeglinExponent b).im := by
  cases a <;> cases b
  · obtain ⟨k, _, he, _⟩ := h
    exact im_eq_of_sub (by simp) he
  all_goals
    obtain ⟨k, _, he | he⟩ := h <;>
      first
      | exact im_eq_of_sub (by simp) he
      | exact (im_eq_of_sub (by simp) he).symm

private theorem realBlocksUnlinked_of_im_ne {x y : RealBlock}
    (h : (Langlands.LocalFactor.Archimedean.RealBlock.exponent x).im ≠ (Langlands.LocalFactor.Archimedean.RealBlock.exponent y).im) : AreRealBlocksUnlinked x y := by
  intro a ha b hb hlink
  have he := moeglinIsLinked_im_eq hlink
  rw [moeglinExponent_eq_of_mem ha, moeglinExponent_eq_of_mem hb] at he
  exact h he

variable {n : ℕ}

private theorem exists_ordered_swap_equiv (pre post : List RealBlock) (x y : RealBlock)
    (hr : realRank (pre ++ x :: y :: post) = n)
    (hle : realBlockExponent y ≤ realBlockExponent x) (hun : AreRealBlocksUnlinked x y) :
    ∃ e : KF n (pre ++ x :: y :: post) ≃ₗ[ℂ] KF n (pre ++ y :: x :: post),
      ∀ i f, e (realStandardOperators n (pre ++ x :: y :: post) i f) =
        realStandardOperators n (pre ++ y :: x :: post) i (e f) := by
  obtain ⟨T, hinj, hT⟩ := realUnlinkedSwap n pre post x y hr hle hun
  let e := LinearEquiv.ofBijective T
    ⟨hinj, realSwapInjectiveIntertwinerSurjective n pre post x y T hr hinj hT⟩
  refine ⟨e, fun i f => ?_⟩
  cases i with
  | inl k => exact hT.map_realStandardRep k f
  | inr X => exact hT.map_realStandardLie (1 ⊗ₜ X) f

private theorem exists_swap_equiv_of_im_ne (pre post : List RealBlock) (x y : RealBlock)
    (hr : realRank (pre ++ x :: y :: post) = n)
    (h : (Langlands.LocalFactor.Archimedean.RealBlock.exponent x).im ≠ (Langlands.LocalFactor.Archimedean.RealBlock.exponent y).im) :
    ∃ e : KF n (pre ++ x :: y :: post) ≃ₗ[ℂ] KF n (pre ++ y :: x :: post),
      ∀ i f, e (realStandardOperators n (pre ++ x :: y :: post) i f) =
        realStandardOperators n (pre ++ y :: x :: post) i (e f) := by
  by_cases hle : realBlockExponent y ≤ realBlockExponent x
  · exact exists_ordered_swap_equiv pre post x y hr hle (realBlocksUnlinked_of_im_ne h)
  · have hr' : realRank (pre ++ y :: x :: post) = n :=
      (realRank_perm ((List.Perm.swap x y post).append_left pre)).trans hr
    obtain ⟨e, he⟩ := exists_ordered_swap_equiv pre post y x hr' (le_of_lt (lt_of_not_ge hle))
      (realBlocksUnlinked_of_im_ne h.symm)
    refine ⟨e.symm, fun i f => e.injective ?_⟩
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

private theorem compactEquiv_map_affine {ds es et : List RealBlock}
    {a : Fin n → ℂ} {z : ℂ} (h : IsExponentShift n ds es a z)
    (h₁ : IsExponentShift n ds et a 1) (X : Matrix (Fin n) (Fin n) ℝ) (f : KF n ds) :
    h.compactEquiv ((realStandardLie n ds (1 ⊗ₜ X) + z • lieIncrement h₁ X) f) =
      realStandardLie n es (1 ⊗ₜ X) (h.compactEquiv f) := by
  rw [← transportedLie_eq_affine h h₁ X]
  exact h.compactEquiv.apply_symm_apply _

private theorem conjugate_intertwines
    {M M' N N' : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N']
    [Module ℂ M] [Module ℂ M'] [Module ℂ N] [Module ℂ N']
    (eL : M ≃ₗ[ℂ] M') (eR : N ≃ₗ[ℂ] N') (T : M' ≃ₗ[ℂ] N')
    {A : Module.End ℂ M} {A' : Module.End ℂ M'} {B : Module.End ℂ N} {B' : Module.End ℂ N'}
    (hL : ∀ f, eL (A f) = A' (eL f)) (hR : ∀ f, eR (B f) = B' (eR f))
    (hT : ∀ f, T (A' f) = B' (T f)) (f : M) :
    eR.symm (T (eL (A f))) = B (eR.symm (T (eL f))) := by
  apply eR.injective
  rw [LinearEquiv.apply_symm_apply, hL, hT, hR, LinearEquiv.apply_symm_apply]

variable {J : Type*} [AddCommGroup J] [Module ℂ J] [Nontrivial J]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) J)
  (L : Matrix (Fin n) (Fin n) ℝ → Module.End ℂ J)

private theorem realStandardConstituent_swap (pre post : List RealBlock) (x y : RealBlock)
    (hr : realRank (pre ++ x :: y :: post) = n)
    (hirr : ∀ U : Submodule ℂ J, (∀ k f, f ∈ U → ρ k f ∈ U) →
      (∀ X f, f ∈ U → L X f ∈ U) → U = ⊥ ∨ U = ⊤)
    (h : IsOperatorConstituent (realStandardOperators n (pre ++ x :: y :: post))
      (Sum.elim (fun k => ρ k) L)) :
    IsOperatorConstituent (realStandardOperators n (pre ++ y :: x :: post))
      (Sum.elim (fun k => ρ k) L) := by
  have hr' : realRank (pre ++ y :: x :: post) = n :=
    (realRank_perm ((List.Perm.swap x y post).append_left pre)).trans hr
  let hleft (z : ℂ) := isExponentShift_shiftBlock pre (y :: post) x hr z
  have hright (z : ℂ) : IsExponentShift n (pre ++ y :: x :: post) (pre ++ y :: shiftBlock z x :: post)
      (fun i => if realRank (pre ++ [y]) ≤ (i : ℕ) ∧ (i : ℕ) < realRank (pre ++ [y]) + x.rank
        then 1 else 0) z := by
    simpa only [List.append_assoc, List.singleton_append] using
      isExponentShift_shiftBlock (pre ++ [y]) post x
        (by simpa only [List.append_assoc, List.singleton_append] using hr') z
  let param (m : ℕ) : ℂ :=
    (((m : ℝ) + 1 + (Langlands.LocalFactor.Archimedean.RealBlock.exponent y).im - (Langlands.LocalFactor.Archimedean.RealBlock.exponent x).im : ℝ) : ℂ) * Complex.I
  have him (m : ℕ) : (param m).im = (m : ℝ) + 1 + (Langlands.LocalFactor.Archimedean.RealBlock.exponent y).im - (Langlands.LocalFactor.Archimedean.RealBlock.exponent x).im := by
    simp [param, Complex.mul_im]
  have hS : (Set.range param).Infinite := Set.infinite_range_of_injective (by
    intro m m' he
    have hcast : (m : ℝ) = (m' : ℝ) := by
      have he' := congrArg Complex.im he
      rw [him, him] at he'
      linarith
    exact_mod_cast hcast)
  have hgk := isRealGKModule_realStandardModule n (pre ++ x :: y :: post)
  refine isOperatorConstituent_of_compact_affine_isomorphisms
    (realStandardRep n (pre ++ x :: y :: post)) (realStandardRep n (pre ++ y :: x :: post)) ρ
    hgk.1 hgk.2.1 (realStandardAdmissible n _) (fun X => realStandardLie n _ (1 ⊗ₜ X))
    (lieIncrement (hleft 1)) (fun X => realStandardLie n _ (1 ⊗ₜ X)) (lieIncrement (hright 1))
    L hS ?_ hirr h
  rintro z ⟨m, rfl⟩
  have hne : (Langlands.LocalFactor.Archimedean.RealBlock.exponent (shiftBlock (param m) x)).im ≠ (Langlands.LocalFactor.Archimedean.RealBlock.exponent y).im := by
    rw [blockExponent_shift, Complex.add_im, him]
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨T, hT⟩ := exists_swap_equiv_of_im_ne pre post (shiftBlock (param m) x) y
    (hleft (param m)).rank' hne
  let eL := (hleft (param m)).compactEquiv
  let eR := (hright (param m)).compactEquiv
  refine ⟨(eL.trans T).trans eR.symm, fun k f => ?_, fun X f => ?_⟩
  · exact conjugate_intertwines eL eR T
      ((hleft (param m)).compactEquiv_map_rep k) ((hright (param m)).compactEquiv_map_rep k)
      (hT (Sum.inl k)) f
  · exact conjugate_intertwines eL eR T (compactEquiv_map_affine (hleft (param m)) (hleft 1) X)
      (compactEquiv_map_affine (hright (param m)) (hright 1) X) (hT (Sum.inr X)) f

/-- An irreducible constituent of the real standard module of a list of blocks
occurs in the real standard module of every permutation of that list. -/
theorem realStandardConstituent_perm {ds es : List RealBlock} (hperm : ds.Perm es)
    (hr : realRank ds = n)
    (hirr : ∀ U : Submodule ℂ J, (∀ k f, f ∈ U → ρ k f ∈ U) →
      (∀ X f, f ∈ U → L X f ∈ U) → U = ⊥ ∨ U = ⊤)
    (h : IsOperatorConstituent (realStandardOperators n ds) (Sum.elim (fun k => ρ k) L)) :
    IsOperatorConstituent (realStandardOperators n es) (Sum.elim (fun k => ρ k) L) := by
  suffices haux : ∀ pre : List RealBlock, realRank (pre ++ ds) = n →
      IsOperatorConstituent (realStandardOperators n (pre ++ ds)) (Sum.elim (fun k => ρ k) L) →
      IsOperatorConstituent (realStandardOperators n (pre ++ es)) (Sum.elim (fun k => ρ k) L) from
    haux [] hr h
  clear hr h
  induction hperm with
  | nil => exact fun _ _ h => h
  | @cons b ds es hp ih =>
    intro pre hr h
    let P (bs : List RealBlock) := IsOperatorConstituent (realStandardOperators n bs)
      (Sum.elim (fun k => ρ k) L)
    have hleft : (pre ++ [b]) ++ ds = pre ++ b :: ds := by
      rw [List.append_assoc, List.singleton_append]
    have hright : (pre ++ [b]) ++ es = pre ++ b :: es := by
      rw [List.append_assoc, List.singleton_append]
    have hr' : realRank ((pre ++ [b]) ++ ds) = n := by rw [hleft]; exact hr
    have h' : P ((pre ++ [b]) ++ ds) := hleft.symm ▸ h
    exact hright ▸ (ih (pre ++ [b]) hr' h' : P ((pre ++ [b]) ++ es))
  | swap x y post => exact fun pre hr h => realStandardConstituent_swap ρ L pre post y x hr hirr h
  | trans hp hq ih₁ ih₂ =>
    intro pre hr h
    exact ih₂ pre ((realRank_perm (hp.append_left pre)).symm.trans hr) (ih₁ pre hr h)

end Langlands.Archimedean
