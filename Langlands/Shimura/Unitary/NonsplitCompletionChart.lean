import Langlands.Global.AdelicFunctoriality.UniquePlaceCompletion
import Langlands.Shimura.Unitary.SplitCompletionChart
import Langlands.Shimura.Unitary.ComplexMatrixInvolution

/-! # The field chart at a nonsplit finite CM place -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped TensorProduct FiniteExtension

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  (p : Langlands.Global.FinitePlace E)

local notation "F" => FiniteCompletion E p
local notation "Q" => FinitePlacesAbove K p

private theorem completedCenterCoordinate (z : LocalCenter E K p) (q : Q) :
    finiteTensorMap (L := K) p z q = completedCenterMap E K p q.val z := by
  induction z using TensorProduct.inductionOn with
  | tmul s k => rw [finiteTensorMap_tmul, completedCenterMap_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- At a finite place the completed CM conjugation acts nontrivially on the center. -/
theorem exists_localConjugation_ne : ∃ z : LocalCenter E K p, localConjugation E K p z ≠ z := by
  obtain ⟨k, hk⟩ : ∃ k : K, cmConjugation E K k ≠ k := by
    by_contra! h
    exact cmConjugation_ne_one E K (AlgEquiv.ext h)
  let q := placeAbove K p
  refine ⟨1 ⊗ₜ[E] k, fun h => hk ((algebraMap K (FiniteCompletion K q.val)).injective ?_)⟩
  have he := congrArg (completedCenterMap E K p q.val) h
  simpa only [localConjugation_tmul, completedCenterMap_tmul, map_one, one_mul] using he

private theorem prodInvolution_eq_swap {R : Type*} [Field R]
    (f : AlgebraInvolution R (R × R)) (hf : ∃ z, f z ≠ z) (z : R × R) :
    f z = z.swap := by
  let a : R × R := (1, 0)
  have ha : a * a = a := by simp [a]
  have hfa : f a * f a = f a := by rw [← f.apply_mul, ha]
  have h₁ : (f a).1 = 0 ∨ (f a).1 = 1 := by
    have h : (f a).1 * (f a).1 = (f a).1 := congrArg Prod.fst hfa
    exact (mul_eq_zero.mp (by rw [mul_sub, h, mul_one, sub_self] :
      (f a).1 * ((f a).1 - 1) = 0)).imp_right sub_eq_zero.mp
  have h₂ : (f a).2 = 0 ∨ (f a).2 = 1 := by
    have h : (f a).2 * (f a).2 = (f a).2 := congrArg Prod.snd hfa
    exact (mul_eq_zero.mp (by rw [mul_sub, h, mul_one, sub_self] :
      (f a).2 * ((f a).2 - 1) = 0)).imp_right sub_eq_zero.mp
  have hcases : f a = a ∨ f a = (0, 1) := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · have h : f a = f 0 := by rw [f.apply_zero]; exact Prod.ext h₁ h₂
      exact False.elim (one_ne_zero (congrArg Prod.fst (f.involutive.injective h)))
    · exact Or.inr (Prod.ext h₁ h₂)
    · exact Or.inl (Prod.ext h₁ h₂)
    · have h : f a = f 1 := by rw [f.apply_one]; exact Prod.ext h₁ h₂
      exact False.elim (zero_ne_one (congrArg Prod.snd (f.involutive.injective h)))
  have hcoord (x : R × R) : x = x.1 • a + x.2 • (1 - a) := by
    ext <;> simp [a]
  have hformula (x : R × R) : f x = x.1 • f a + x.2 • (1 - f a) := by
    conv_lhs => rw [hcoord x]
    simp only [f.apply_add, f.apply_smul]
    change x.1 • f a + x.2 • f.linear (1 - a) = _
    rw [map_sub, f.apply_one]
  rcases hcases with ha' | ha'
  · obtain ⟨x, hx⟩ := hf
    exact False.elim (hx (by rw [hformula, ha', ← hcoord]))
  · rw [hformula, ha']
    ext <;> simp

private theorem isSplitPlace_of_two_places (q r : Q) (hqr : q ≠ r) :
    IsSplitPlace E K p := by
  classical
  let d (w : Q) := Module.finrank F (FiniteCompletion K w.val)
  have hd (w : Q) : 1 ≤ d w := Module.finrank_pos
  have hsum : ∑ w, d w ≤ 2 :=
    (IsQuadraticExtension.finrank_eq_two E K) ▸ finiteLocalDegree_sum_le (L := K) p
  have hcard : Fintype.card Q ≤ 2 := calc
    Fintype.card Q = ∑ _w : Q, 1 := by simp
    _ ≤ ∑ w, d w := Finset.sum_le_sum (fun w _ => hd w)
    _ ≤ 2 := hsum
  have hcard' : Fintype.card Q = 2 := by
    have hle : ({q, r} : Finset Q).card ≤ Fintype.card Q := Finset.card_le_univ _
    rw [Finset.card_pair hqr] at hle
    exact le_antisymm hcard hle
  let i := Fintype.equivFinOfCardEq hcard'
  have hd' (w : Q) : d w = 1 := by
    let w' := i.symm ((i w).rev)
    have hn : w ≠ w' := by
      intro h
      have he : i w = (i w).rev := by simpa [w'] using congrArg i h
      have hv := congrArg Fin.val he
      simp only [Fin.val_rev] at hv
      have := (i w).isLt
      omega
    have hpair : d w + d w' ≤ 2 := calc
      _ = ∑ t ∈ ({w, w'} : Finset Q), d t := (Finset.sum_pair hn).symm
      _ ≤ ∑ t, d t := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 := hsum
    have hpos := hd w
    have hpos' := hd w'
    omega
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := K) p)
    ((completedTensorComparison E K).1 p)
  let f (w : Q) : FiniteCompletion K w.val ≃ₐ[F] F :=
    (AlgEquiv.ofBijective (Algebra.ofId F (FiniteCompletion K w.val))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (hd' w))).symm
  let g := AlgEquiv.piCongrLeft' F (fun _ : Q => F) i
  let h : (Fin 2 → F) ≃ₐ[F] F × F :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo (fun _ => F)) (fun _ => rfl)
  let P := e.trans ((AlgEquiv.piCongrRight f).trans (g.trans h))
  let c := (localConjugation E K p).transport P
  have hc : ∃ z, c z ≠ z := by
    obtain ⟨z, hz⟩ := exists_localConjugation_ne (K := K) p
    exact ⟨P z, fun he => hz (P.injective (by simpa [c] using he))⟩
  exact ⟨⟨P, fun z => by simpa only [c, AlgebraInvolution.transport_equiv] using
    prodInvolution_eq_swap c hc (P z)⟩⟩

/-- The nonsplit finite place has exactly one actual upper place. -/
theorem eq_placeAbove_of_nonsplit (hp : ¬ IsSplitPlace E K p) (q : Q) : q = placeAbove K p := by
  by_contra hn
  exact hp (isSplitPlace_of_two_places p q _ hn)

/-- Evaluation at the unique upper place is the quadratic field chart for the
actual completed center. -/
def nonsplitCompletionCenterEquiv (hp : ¬ IsSplitPlace E K p) :
    LocalCenter E K p ≃ₐ[F] FiniteCompletion K (placeAbove K p).val := by
  let q := placeAbove K p
  let : Unique Q := ⟨⟨q⟩, eq_placeAbove_of_nonsplit p hp⟩
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := K) p)
    ((completedTensorComparison E K).1 p)
  let f : (∀ r : Q, FiniteCompletion K r.val) ≃ₐ[F] FiniteCompletion K q.val :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piUnique fun r : Q => FiniteCompletion K r.val)
      (fun _ => rfl)
  exact e.trans f

@[simp] theorem nonsplitCompletionCenterEquiv_apply (hp : ¬ IsSplitPlace E K p)
    (z : LocalCenter E K p) : nonsplitCompletionCenterEquiv p hp z =
      completedCenterMap E K p (placeAbove K p).val z := completedCenterCoordinate p z _

/-- The actual upper completion at a nonsplit finite place is quadratic. -/
theorem nonsplitCompletion_finrank (hp : ¬ IsSplitPlace E K p) :
    Module.finrank F (FiniteCompletion K (placeAbove K p).val) = 2 :=
  (localDegree_eq_global_of_unique (placeAbove K p) (eq_placeAbove_of_nonsplit p hp)).trans
    (IsQuadraticExtension.finrank_eq_two E K)

/-- The center chart carries the original conjugation to the extension of CM
conjugation at the unique upper place. -/
theorem nonsplitCompletionCenterEquiv_conjugation (hp : ¬ IsSplitPlace E K p)
    (z : LocalCenter E K p) :
    nonsplitCompletionCenterEquiv p hp (localConjugation E K p z) =
      uniquePlaceCompletionAutEquiv (placeAbove K p) (eq_placeAbove_of_nonsplit p hp)
        (cmConjugation E K) (nonsplitCompletionCenterEquiv p hp z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s k =>
    simp only [localConjugation_tmul, nonsplitCompletionCenterEquiv_apply,
      completedCenterMap_tmul, map_mul, uniquePlaceCompletionAutEquiv_algebraMap]
    congr 1
    exact (uniquePlaceCompletionAutEquiv (placeAbove K p) (eq_placeAbove_of_nonsplit p hp)
      (cmConjugation E K)).commutes s |>.symm

end Langlands.Shimura.FiniteUnitary
