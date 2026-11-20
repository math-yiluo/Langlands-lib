import Langlands.Automorphic.StandardBlockConstantTermFamily

/-! # Block constant terms in the ordered block matrix model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped BigOperators CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.GeneralLinear Langlands.Global

variable {n : ℕ} (B : BlockShape n)

private theorem cuts_before_card (x : Fin n) :
    (B.cuts.filter fun cut => cut.val < x.val).card = (B.toComposition.index x).val := by
  let c := B.toComposition
  let b := c.index x
  have hboundary (j : Fin (c.length + 1)) : (c.boundary j).val ≤ x.val ↔ j.val ≤ b.val := by
    change c.sizeUpTo j.val ≤ x.val ↔ j.val ≤ b.val
    constructor
    · intro h
      by_contra! hbj
      exact ((c.lt_sizeUpTo_index_succ x).trans_le
        (c.monotone_sizeUpTo (Nat.succ_le_of_lt hbj))).not_ge h
    · intro h
      exact (c.monotone_sizeUpTo h).trans (c.sizeUpTo_index_le x)
  let j (i : Fin b.val) : Fin (c.length + 1) := ⟨i.val + 1, by
    have := i.isLt
    have := b.isLt
    omega⟩
  have hpos (i : Fin b.val) : 0 < (c.boundary (j i)).val := by
    have h : (0 : Fin (c.length + 1)) < j i := Fin.val_fin_lt.mpr (Nat.succ_pos _)
    have hh := c.boundary.strictMono h
    rw [c.boundary_zero] at hh
    exact Fin.val_fin_lt.mp hh
  have hle (i : Fin b.val) : (c.boundary (j i)).val ≤ x.val :=
    (hboundary (j i)).mpr (Nat.succ_le_of_lt i.isLt)
  let cut (i : Fin b.val) : Fin (n - 1) := ⟨(c.boundary (j i)).val - 1, by
    have := hle i
    have := x.isLt
    have := hpos i
    omega⟩
  have hcutval (i : Fin b.val) : (cut i).val + 1 = (c.boundary (j i)).val :=
    Nat.sub_add_cancel (hpos i)
  have hcard :
      (Finset.univ : Finset (Fin b.val)).card = (B.cuts.filter fun t => t.val < x.val).card := by
    refine Finset.card_bij (fun i _ => cut i) ?_ ?_ ?_
    · intro i _
      refine Finset.mem_filter.mpr ⟨(B.mem_cuts_iff (cut i)).mpr ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨j i, Finset.mem_univ _, Fin.ext (hcutval i).symm⟩
      · have := hle i
        have := hcutval i
        omega
    · intro i _ i' _ he
      have hb : (c.boundary (j i)).val = (c.boundary (j i')).val := by
        rw [← hcutval i, ← hcutval i', he]
      have hj := congrArg Fin.val (c.boundary.injective (Fin.ext hb))
      apply Fin.ext
      change i.val + 1 = i'.val + 1 at hj
      omega
    · intro t ht
      obtain ⟨htB, htx⟩ := Finset.mem_filter.mp ht
      obtain ⟨k, _, hk⟩ := Finset.mem_map.mp ((B.mem_cuts_iff t).mp htB)
      have hkv : (c.boundary k).val = t.val + 1 := congrArg Fin.val hk
      have hk0 : 0 < k.val := by
        by_contra! hzero
        have hzero' : k = 0 := Fin.ext (Nat.eq_zero_of_le_zero hzero)
        rw [hzero', c.boundary_zero, Fin.val_zero] at hkv
        omega
      have hkb : k.val ≤ b.val := (hboundary k).mp (by omega)
      let i : Fin b.val := ⟨k.val - 1, by omega⟩
      have hji : j i = k := Fin.ext (Nat.sub_add_cancel hk0)
      refine ⟨i, Finset.mem_univ _, Fin.ext ?_⟩
      have hi := hcutval i
      rw [hji, hkv] at hi
      omega
  simpa only [Finset.card_univ, Fintype.card_fin, b, c] using hcard.symm

private theorem composition_index_blockIndex (j : Fin B.length) (a : Fin (B.size j)) :
    ((B.toComposition.index (B.index j a)) : ℕ) = j.val := by
  let c := B.toComposition
  have hlen : c.length = B.length := by
    simp [c, BlockShape.toComposition, Composition.length]
  let j' : Fin c.length := j.cast hlen.symm
  let a' : Fin (c.blocksFun j') := ⟨a.val, by
    change a.val < (List.ofFn B.size).get ⟨j.val, by
      simpa only [List.length_ofFn] using j.isLt⟩
    rw [List.get_ofFn]
    exact a.isLt⟩
  have hprefix :
      c.sizeUpTo j'.val = ∑ i : Fin j.val, B.size (Fin.castLE j.isLt.le i) := by
    change ((List.ofFn B.size).take j.val).sum = _
    rw [List.sum_take_ofFn]
    have hset : (Finset.univ : Finset (Fin j.val)).map (Fin.castLEEmb j.isLt.le) =
        Finset.univ.filter fun i : Fin B.length => i.val < j.val := by
      ext i
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, rfl⟩
        exact b.isLt
      · intro hi
        exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    rw [← hset, Finset.sum_map]
    rfl
  have hindex : B.index j a = c.embedding j' a' := by
    apply Fin.ext
    rw [Composition.coe_embedding, hprefix]
    change (Fin.cast B.sum_eq (finSigmaFinEquiv ⟨j, a⟩)).val = _
    rw [Fin.val_cast, finSigmaFinEquiv_apply]
  rw [hindex, Composition.index_embedding]
  rfl

/-- The cut-count weight is the negative of the usual block index. -/
theorem standardBlockWeight_on_index (i : Fin B.length) (a : Fin (B.size i)) :
    standardBlockWeight B.cuts (B.index i a) = -(i.val : ℤ) := by
  rw [standardBlockWeight, cuts_before_card, composition_index_blockIndex]

/-- Block-unipotent membership for the cut-count weights is membership in
the ambient radical of the original ordered block parabolic. -/
theorem blockUnipotentSubgroup_eq_shape (A : Type u) [CommRing A] :
    GroupScheme.GeneralLinear.blockUnipotentSubgroup A (standardBlockWeight B.cuts) =
      B.unipotentSubgroup A := by
  apply Subgroup.ext
  intro g
  rw [GroupScheme.GeneralLinear.mem_blockUnipotentSubgroup, B.mem_unipotentSubgroup_iff,
    B.mem_parabolic_iff]
  have hindex (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j))
      (he : B.index i a = B.index j b) : i = j :=
    congrArg Sigma.fst (B.indexEquiv.injective he)
  have hdiag (i : Fin B.length) (a b : Fin (B.size i)) :
      (1 : Matrix (Fin n) (Fin n) A) (B.index i a) (B.index i b) =
        if a = b then 1 else 0 := by
    simp only [Matrix.one_apply, (B.index i).injective.eq_iff]
  constructor
  · intro h
    constructor
    · intro i j a b hji
      have he : B.index i a ≠ B.index j b := fun he => hji.ne (hindex i j a b he).symm
      have hv := h (B.index i a) (B.index j b) (by
        rw [standardBlockWeight_on_index, standardBlockWeight_on_index, neg_le_neg_iff, Int.ofNat_le]
        exact hji.le)
      simpa only [Matrix.one_apply_ne he] using hv
    · intro i a b
      simpa only [hdiag] using h (B.index i a) (B.index i b) (by
        simp only [standardBlockWeight_on_index, le_refl])
  · rintro ⟨hp, hd⟩ x y hxy
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    change standardBlockWeight B.cuts (B.index i a) ≤ standardBlockWeight B.cuts (B.index j b) at hxy
    rw [standardBlockWeight_on_index, standardBlockWeight_on_index, neg_le_neg_iff, Int.ofNat_le] at hxy
    rcases (show j ≤ i from hxy).lt_or_eq with hji | hji
    · change g (B.index i a) (B.index j b) = _
      rw [hp i j a b hji]
      exact (Matrix.one_apply_ne (fun he => hji.ne (hindex i j a b he).symm)).symm
    · subst j
      exact (hd i a b).trans (hdiag i a b).symm

variable (F : Type u) [Field F] [NumberField F]

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The actual normalized constant term for an ordered block shape, evaluated
on the original adelic matrix group. -/
def blockShapeConstantTerm (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n) : ℂ :=
  finiteSmoothBlockConstantTerm F (standardBlockWeight B.cuts) f
    ((GeneralLinearGroupPoints.adelicEquiv F n).symm g)

theorem blockShapeConstantTerm_rightAction (f : FiniteSmoothRationalFunctions F n)
    (h g : AdelicGL F n) :
    blockShapeConstantTerm B F (finiteSmoothRightAction F n h f) g =
      blockShapeConstantTerm B F f (g * h) := by
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  simpa only [blockShapeConstantTerm, map_mul, e, MulEquiv.apply_symm_apply] using
    finiteSmoothBlockConstantTerm_rightAction F (standardBlockWeight B.cuts) f (e.symm h) (e.symm g)

theorem blockShapeConstantTerm_unipotent_mul (f : FiniteSmoothRationalFunctions F n)
    {x : AdelicGL F n} (hx : x ∈ B.unipotentSubgroup (Adeles F)) (g : AdelicGL F n) :
    blockShapeConstantTerm B F f (x * g) = blockShapeConstantTerm B F f g := by
  let e := GeneralLinearGroupPoints.adelicEquiv F n
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let w := standardBlockWeight B.cuts
  let U := GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) w
  let H := GroupScheme.GeneralLinear.blockUnipotentSubgroup (Adeles F) w
  have hx' : x ∈ H :=
    (congrArg (fun P : Subgroup (AdelicGL F n) => x ∈ P)
      (blockUnipotentSubgroup_eq_shape B (Adeles F))).mpr hx
  have hv : e (e.symm x) ∈ H :=
    (congrArg (fun y : AdelicGL F n => y ∈ H) (e.apply_symm_apply x)).mpr hx'
  have hU : e.symm x ∈ AdelicSubgroupPoints.adelicPoints F G U := by
    exact (GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff (n := n)
      (CommRingCat.of F) (CommAlgCat.of F (Adeles F)) w (e.symm x)).mpr hv
  simp only [blockShapeConstantTerm, finiteSmoothBlockConstantTerm_apply, map_mul]
  exact GroupSchemeFunctions.normalizedBlockConstantTerm_unipotent_mul F w _
    ⟨e.symm x, hU⟩ (e.symm g)

end Langlands.Automorphic
