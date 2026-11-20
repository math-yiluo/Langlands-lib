import Langlands.Representation.Archimedean.RealDiscreteFrame
import Langlands.Representation.Archimedean.RealDiscreteTightness
import Langlands.Representation.Archimedean.RealTiedScalarAssembly

/-!
# Shifted spherical lists and sorting by unlinked swaps

Two tools for the scalar step with discrete-series blocks.

* **Shifts.** For a list `ds` of characters and bottom row sets `R_j`, let `h_i` be the number
  of `j` with `i ∈ R_j`. If the sign of the `i`-th character of `ds` is `(-1)^{h_i}`, then `ds`
  is the twist of the even list `|·|^{e_i - h_i}` by the product of the minors with rows `R_j`
  (`isMinorShift_shiftList`).
* **Sorting.** If every pair of characters of a list that is out of Langlands order is unlinked,
  the insertion sort of the list by decreasing real exponent maps onto the list by a surjective
  `(𝔤, K)`-intertwiner (`hasGKSurjection_insertionSort`). Lie cyclicity of an `O(n)`-fixed vector
  passes along such surjections.
-/

noncomputable section

open Matrix Finset

open scoped TensorProduct

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealDiscreteShift

open RealTemperedCommutantReduction RealTiedMinorScalar RealTiedMinorProduct
  RealDiscreteMinorCyclic RealDiscreteTightness RealStrictCharacterLanglandsQuotient
  GramFormula PrincipalSeriesExtension

variable {n N : ℕ}

/-! ## Shifted lists -/

/-- The number of row sets `R_j` that contain the row `i`. -/
def hits (R : Fin N → Finset (Fin n)) (i : Fin n) : ℕ := (colSet R i).card

/-- The even list `|·|^{e_i - h_i}`. -/
def shiftList (n : ℕ) (ds : List RealBlock) (R : Fin N → Finset (Fin n)) :
    List RealCharacterData :=
  List.ofFn fun i : Fin n =>
    RealJacquetFrobenius.charData 0 (realPositionExponent ds i - (hits R i : ℂ))

theorem shiftList_length (ds : List RealBlock) (R : Fin N → Finset (Fin n)) :
    (shiftList n ds R).length = n :=
  List.length_ofFn

theorem shiftList_parity (ds : List RealBlock) (R : Fin N → Finset (Fin n)) :
    ∀ d ∈ shiftList n ds R, d.parity = 0 := by
  intro d hd
  rw [shiftList, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  rfl

theorem shiftChar_apply (ds : List RealBlock) (R : Fin N → Finset (Fin n)) (i : Fin n)
    (x : ℝˣ) :
    realPositionCharacter ((shiftList n ds R).map RealBlock.character) i x =
      ((|(x : ℝ)| : ℝ) : ℂ) ^ (realPositionExponent ds i - (hits R i : ℂ)) := by
  rw [RealJacquetFrobenius.realPositionCharacter_map_character _ i
    (by rw [shiftList_length]; exact i.2) x]
  simp [shiftList, RealJacquetFrobenius.charData_character_apply, RealJacquetFrobenius.charFun]

/-- The character of `ds` at `i` is the shifted character times `x^{h_i}`. -/
theorem posChar_shift {ds : List RealBlock} {R : Fin N → Finset (Fin n)}
    (hpar : ∀ i : Fin n, realPositionCharacter ds i (-1) = (-1) ^ hits R i) (i : Fin n)
    (x : ℝˣ) :
    realPositionCharacter ds i x =
      realPositionCharacter ((shiftList n ds R).map RealBlock.character) i x *
        ((x : ℝ) : ℂ) ^ hits R i := by
  rw [(isSignedPower ds).eq i x, shiftChar_apply]
  have hx0 : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr x.ne_zero)
  have hs : realPositionCharacter ds i (signUnit x) =
      ((signReal (x : ℝ) : ℝ) : ℂ) ^ hits R i := by
    unfold signUnit signReal
    split_ifs
    · rw [(isSignedPower ds).one]
      simp
    · rw [hpar]
      simp
  rw [hs, Complex.cpow_sub _ _ hx0, Complex.cpow_natCast]
  have hx : ((x : ℝ) : ℂ) = ((signReal (x : ℝ) : ℝ) : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, signReal_mul_abs]
  rw [hx, mul_pow]
  field_simp

theorem rowWeight_eq (R : Fin N → Finset (Fin n)) (a : Fin n → ℝˣ) :
    rowWeight R a = ∏ i, ((a i : ℝ) : ℂ) ^ hits R i := by
  have h1 : ∀ j, ∏ i ∈ R j, ((a i : ℝ) : ℂ) = ∏ i, if i ∈ R j then ((a i : ℝ) : ℂ) else 1 := by
    intro j
    rw [← Finset.prod_filter]
    congr 1
    ext i
    simp
  have h2 : ∀ i, ∏ j, (if i ∈ R j then ((a i : ℝ) : ℂ) else 1) = ((a i : ℝ) : ℂ) ^ hits R i := by
    intro i
    rw [← Finset.prod_filter, Finset.prod_const]
    rfl
  unfold rowWeight
  simp only [h1]
  rw [Finset.prod_comm]
  simp only [h2]

/-- **The shift.** If the sign of the `i`-th character of `ds` is `(-1)^{h_i}`, then `ds` is the
twist of the shifted even list by the product of the minors with rows `R_j`. -/
theorem isMinorShift_shiftList {ds : List RealBlock} (hds : IsPrincipal ds)
    {R : Fin N → Finset (Fin n)} (hR : ∀ j, IsBottom (R j))
    (hpar : ∀ i : Fin n, realPositionCharacter ds i (-1) = (-1) ^ hits R i) :
    IsMinorShift n ((shiftList n ds R).map RealBlock.character) ds R where
  principal_left := isPrincipal_map_character _
  principal_right := hds
  bottom := hR
  char a := by
    rw [rowWeight_eq]
    unfold principalSeriesCharacter
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [posChar_shift hpar i (a i)]
    ring

end RealDiscreteShift

namespace RealDiscreteSort

open RealTemperedCommutantReduction RealDiscretePresentation

variable {n : ℕ}

/-! ## Transport of cyclic fixed vectors -/

theorem isGKMap_iff {ds es : List RealBlock} {q : RealDiscretePresentation.KF n ds →ₗ[ℂ]
    RealDiscretePresentation.KF n es} (hq : IsGKMap n ds es q) :
    (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) v,
      q (realStandardRep n ds k v) = realStandardRep n es k (q v)) ∧
    ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) v,
      q (realStandardLie n ds Z v) = realStandardLie n es Z (q v) := by
  unfold IsGKMap at hq
  rw [InductionStages.isRealStandardIntertwiner_iff] at hq
  refine ⟨fun k u => hq.1 ⟨Unitary.toUnits k, k.2⟩ u, fun Z v => ?_⟩
  induction Z with
  | tmul z X =>
    have h1 : ∀ fs : List RealBlock, realStandardLie n fs (z ⊗ₜ X) =
        z • realStandardLie n fs (1 ⊗ₜ X) := fun fs => by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, h1, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    exact congrArg (z • ·) (hq.2 X v)
  | add Z₁ Z₂ h₁ h₂ =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]

/-- The image of a Lie-cyclic `O(n)`-fixed vector under a surjective `(𝔤, K)`-intertwiner is
Lie-cyclic and `O(n)`-fixed. -/
theorem cyclic_map {ds es : List RealBlock}
    {q : RealDiscretePresentation.KF n ds →ₗ[ℂ] RealDiscretePresentation.KF n es}
    (hs : Function.Surjective q) (hq : IsGKMap n ds es q) {T : RealDiscretePresentation.KF n ds}
    (hT : ∀ k, realStandardRep n ds k T = T)
    (hcyc : ∀ W : Submodule ℂ (RealDiscretePresentation.KF n ds), T ∈ W →
      (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W, realStandardLie n ds Z w ∈ W) → W = ⊤) :
    (∀ k, realStandardRep n es k (q T) = q T) ∧
      ∀ W : Submodule ℂ (RealDiscretePresentation.KF n es), q T ∈ W →
        (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ w ∈ W, realStandardLie n es Z w ∈ W) →
          W = ⊤ := by
  obtain ⟨hK, hL⟩ := isGKMap_iff hq
  refine ⟨fun k => by rw [← hK, hT], fun W hW hWL => ?_⟩
  have htop : W.comap q = ⊤ := hcyc _ hW fun Z w hw => by
    change q (realStandardLie n ds Z w) ∈ W
    rw [hL]
    exact hWL Z _ hw
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, rfl⟩ := hs v
  have hu : u ∈ W.comap q := htop ▸ Submodule.mem_top
  exact hu

/-! ## Insertion sort by decreasing real exponent -/

/-- `a` may precede `b` in Langlands order: `Re b ≤ Re a`. -/
def LangRel (a b : RealCharacterData) : Prop := b.exponent.re ≤ a.exponent.re

instance : DecidableRel LangRel := fun a b =>
  inferInstanceAs (Decidable (b.exponent.re ≤ a.exponent.re))

instance : Std.Total LangRel := ⟨fun a b => le_total b.exponent.re a.exponent.re⟩

instance : IsTrans RealCharacterData LangRel := ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

theorem realRank_pre_map_post (pre post : List RealBlock) (L : List RealCharacterData) :
    realRank (pre ++ L.map RealBlock.character ++ post) =
      realRank pre + L.length + realRank post := by
  rw [realRank_append, realRank_append, realRank_map_character]

/-- Inserting `c` into `S` and moving it back to the front. -/
theorem hasGKSurjection_orderedInsert (c : RealCharacterData) :
    ∀ (S : List RealCharacterData) (pre post : List RealBlock),
      realRank (pre ++ (c :: S).map RealBlock.character ++ post) = n →
      (∀ b ∈ S, c.exponent.re < b.exponent.re →
        AreRealBlocksUnlinked (.character c) (.character b)) →
      HasGKSurjection n (pre ++ (S.orderedInsert LangRel c).map RealBlock.character ++ post)
        (pre ++ (c :: S).map RealBlock.character ++ post)
  | [], _, _, _, _ => HasGKSurjection.refl _
  | b :: S, pre, post, hn, hu => by
    by_cases h : LangRel c b
    · rw [List.orderedInsert_cons_of_le _ _ h]
      exact HasGKSurjection.refl _
    · rw [List.orderedInsert_of_not_le _ _ h]
      have hlt : c.exponent.re < b.exponent.re := lt_of_not_ge h
      have hn' : realRank ((pre ++ [.character b]) ++ (c :: S).map RealBlock.character ++ post) =
          n := by
        rw [← hn, realRank_pre_map_post, realRank_pre_map_post, realRank_append]
        simp only [List.length_cons, realRank_cons, realRank_nil, RealBlock.rank]
        omega
      have h1 := hasGKSurjection_orderedInsert c S (pre ++ [.character b]) post hn'
        fun b' hb' => hu b' (List.mem_cons_of_mem _ hb')
      have hn'' : realRank (pre ++ RealBlock.character b :: RealBlock.character c ::
          (S.map RealBlock.character ++ post)) = n := by
        rw [← hn]
        simp only [realRank_append, realRank_cons, List.map_cons]
        omega
      have h2 := hasGKSurjection_swap hn'' (hu b List.mem_cons_self hlt).symm
      have e1 : pre ++ (b :: S.orderedInsert LangRel c).map RealBlock.character ++ post =
          (pre ++ [.character b]) ++ (S.orderedInsert LangRel c).map RealBlock.character ++
            post := by simp
      have e2 : (pre ++ [.character b]) ++ (c :: S).map RealBlock.character ++ post =
          pre ++ RealBlock.character b :: RealBlock.character c ::
            (S.map RealBlock.character ++ post) := by simp
      have e3 : pre ++ (c :: b :: S).map RealBlock.character ++ post =
          pre ++ RealBlock.character c :: RealBlock.character b ::
            (S.map RealBlock.character ++ post) := by simp
      rw [e1, e3]
      rw [e2] at h1
      exact h1.trans h2

/-- **Sorting.** If every pair of characters of `L` that is out of Langlands order is unlinked,
the insertion sort of `L` maps onto `L`. -/
theorem hasGKSurjection_insertionSort :
    ∀ (L : List RealCharacterData) (pre post : List RealBlock),
      realRank (pre ++ L.map RealBlock.character ++ post) = n →
      L.Pairwise (fun c b => c.exponent.re < b.exponent.re →
        AreRealBlocksUnlinked (.character c) (.character b)) →
      HasGKSurjection n (pre ++ (L.insertionSort LangRel).map RealBlock.character ++ post)
        (pre ++ L.map RealBlock.character ++ post)
  | [], _, _, _, _ => HasGKSurjection.refl _
  | c :: L, pre, post, hn, hP => by
    rw [List.insertionSort_cons]
    have hP' := List.pairwise_cons.mp hP
    have hn1 : realRank (pre ++ (c :: L.insertionSort LangRel).map RealBlock.character ++ post) =
        n := by
      rw [← hn, realRank_pre_map_post, realRank_pre_map_post, List.length_cons,
        List.length_cons, List.length_insertionSort]
    have h1 := hasGKSurjection_orderedInsert c (L.insertionSort LangRel) pre post hn1
      fun b hb => hP'.1 b ((List.mem_insertionSort _).mp hb)
    have hn2 : realRank ((pre ++ [.character c]) ++ L.map RealBlock.character ++ post) = n := by
      rw [← hn]
      simp
    have h2 := hasGKSurjection_insertionSort L (pre ++ [.character c]) post hn2 hP'.2
    have e1 : (pre ++ [.character c]) ++ (L.insertionSort LangRel).map RealBlock.character ++
        post = pre ++ (c :: L.insertionSort LangRel).map RealBlock.character ++ post := by simp
    have e2 : (pre ++ [.character c]) ++ L.map RealBlock.character ++ post =
        pre ++ (c :: L).map RealBlock.character ++ post := by simp
    rw [e1, e2] at h2
    exact h1.trans h2

theorem isRealLanglandsOrdered_insertionSort (L : List RealCharacterData) :
    IsRealLanglandsOrdered ((L.insertionSort LangRel).map RealBlock.character) := by
  unfold IsRealLanglandsOrdered
  rw [List.pairwise_map]
  exact List.pairwise_insertionSort LangRel L

/-! ## Unlinked characters -/

theorem datumExponent_im_of_linked {a b : MoeglinDatum} (h : a.IsLinked b) :
    (RealTiedScalarAssembly.datumExponent a).im = (RealTiedScalarAssembly.datumExponent b).im := by
  rcases a with ⟨ε, s⟩ | ⟨p, s⟩ <;> rcases b with ⟨ε', s'⟩ | ⟨p', s'⟩ <;>
    simp only [RealTiedScalarAssembly.datumExponent] <;>
    simp only [MoeglinDatum.IsLinked] at h
  · obtain ⟨k, -, hs, -⟩ := h
    have h1 := congrArg Complex.im hs
    simp only [Complex.sub_im, Complex.intCast_im] at h1
    linarith
  · obtain ⟨k, -, hs | hs⟩ := h <;> have h1 := congrArg Complex.im hs <;>
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im] at h1 <;>
      linarith
  · obtain ⟨k, -, hs | hs⟩ := h <;> have h1 := congrArg Complex.im hs <;>
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im] at h1 <;>
      linarith
  · obtain ⟨k, -, hs | hs⟩ := h <;> have h1 := congrArg Complex.im hs <;>
      simp only [Complex.sub_im, Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im] at h1 <;>
      linarith

/-- Two characters whose exponents have different imaginary parts are unlinked. -/
theorem unlinked_of_im_ne {c b : RealCharacterData} (h : c.exponent.im ≠ b.exponent.im) :
    AreRealBlocksUnlinked (.character c) (.character b) := by
  intro x hx y hy hxy
  simp only [realBlockMoeglinData, List.mem_singleton] at hx hy
  subst hx
  subst hy
  exact h (datumExponent_im_of_linked hxy)

/-- Two blocks whose exponents have different imaginary parts are unlinked. -/
theorem unlinked_of_block_im_ne {x y : RealBlock}
    (h : ∀ a ∈ realBlockMoeglinData x, ∀ b ∈ realBlockMoeglinData y,
      (RealTiedScalarAssembly.datumExponent a).im ≠ (RealTiedScalarAssembly.datumExponent b).im) :
    AreRealBlocksUnlinked x y :=
  fun a ha b hb hab => h a ha b hb (datumExponent_im_of_linked hab)

end RealDiscreteSort

end Langlands.Archimedean
