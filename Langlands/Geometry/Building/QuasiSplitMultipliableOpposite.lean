import Langlands.Geometry.Building.QuasiSplitMultipliableFactorization
import Langlands.Geometry.Building.ChamberRankOne

/-! # The opposite-pair axiom at multipliable roots for the descended quasi-split family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

section Orthogonal

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N] [Finite J]
  (P : RootDatum J M N)

/-- If two orthogonal roots do not sum to a root, no strictly positive combination of them is
a root, and none is zero. -/
theorem nsmul_add_nsmul_notMem_of_pairing_eq_zero {i i' : J} (h0 : P.pairing i i' = 0)
    (h0' : P.pairing i' i = 0) (hsum : P.root i + P.root i' ∉ Set.range P.root) :
    ∀ n l : ℕ, 0 < n → 0 < l →
      n • P.root i + l • P.root i' ≠ 0 ∧ n • P.root i + l • P.root i' ∉ Set.range P.root := by
  intro n l hn hl
  constructor
  · intro hz
    have h := congrArg (fun x => P.toLinearMap x (P.coroot i')) hz
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
      P.root_coroot_eq_pairing, h0, P.pairing_same, map_zero, LinearMap.zero_apply,
      nsmul_eq_mul] at h
    omega
  · -- descend first in `n`, then in `l`
    induction n, hn using Nat.le_induction with
    | base =>
      induction l, hl using Nat.le_induction with
      | base => simpa using hsum
      | succ l hl ih =>
        rintro ⟨β, hβ⟩
        apply ih
        have hpos : 0 < P.pairingIn ℤ β i' := by
          have : P.pairing β i' = 2 * (l + 1 : ℤ) := by
            rw [← P.root_coroot_eq_pairing, hβ]
            simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
              P.root_coroot_eq_pairing, h0, P.pairing_same, nsmul_eq_mul]
            push_cast; ring
          rw [← P.algebraMap_pairingIn ℤ, Algebra.algebraMap_self, RingHom.id_apply] at this
          rw [this]; positivity
        have hne : β ≠ i' := by
          intro h
          rw [h] at hβ
          have := congrArg (fun x => P.toLinearMap x (P.coroot i)) hβ
          simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
            P.root_coroot_eq_pairing, h0', P.pairing_same, nsmul_eq_mul] at this
          omega
        obtain ⟨γ', hγ'⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos hne
        refine ⟨γ', ?_⟩
        rw [hγ', hβ]
        simp only [succ_nsmul]
        abel
    | succ n hn ih =>
      rintro ⟨β, hβ⟩
      apply ih
      have hpos : 0 < P.pairingIn ℤ β i := by
        have : P.pairing β i = 2 * (n + 1 : ℤ) := by
          rw [← P.root_coroot_eq_pairing, hβ]
          simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
            P.root_coroot_eq_pairing, h0', P.pairing_same, nsmul_eq_mul]
          push_cast; ring
        rw [← P.algebraMap_pairingIn ℤ, Algebra.algebraMap_self, RingHom.id_apply] at this
        rw [this]; positivity
      have hne : β ≠ i := by
        intro h
        rw [h] at hβ
        have := congrArg (fun x => P.toLinearMap x (P.coroot i')) hβ
        simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
          P.root_coroot_eq_pairing, h0, P.pairing_same, nsmul_eq_mul] at this
        omega
      obtain ⟨γ', hγ'⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos hne
      refine ⟨γ', ?_⟩
      rw [hγ', hβ, succ_nsmul]
      abel

end Orthogonal

section Cross

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hP : IsRootDatumOf j P)
  {f : S ⟶ T} {a : characterLattice S} (hline : RestrictsToMultipliableLine f P a)

omit [Smooth G.X.hom] [Mono j.hom.hom.left] in
include hP hline in
/-- Two orthogonal roots on the line of `a` have no strictly positive combination that is zero
or a root. -/
theorem noStrictRootCombinations_of_orthogonal {i i' : J} (h0 : P.pairing i i' = 0)
    (h0' : P.pairing i' i = 0) {c c' : ℤ} (hc : f ≫ P.root i = c • a)
    (hc' : f ≫ P.root i' = c' • a) (hcc : c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2)
    (hcc' : c' = 1 ∨ c' = 2 ∨ c' = -1 ∨ c' = -2) :
    NoStrictRootCombinations j (P.root i) (P.root i') := by
  have hsum : P.root i + P.root i' ∉ Set.range P.root := by
    rintro ⟨β, hβ⟩
    have h1 := hline β (c + c') (by rw [hβ, Preadditive.comp_add, hc, hc', add_smul])
    have hpb : P.pairing β i' = 2 := by
      rw [pairing_eq_of_root_eq P hβ, map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
        P.root_coroot_eq_pairing, h0, P.pairing_same, zero_add]
    have h2 := hline (P.reflectionPerm i' β) (c - c') (by
      rw [comp_root_reflectionPerm, hpb, hβ, Preadditive.comp_add, hc, hc', sub_smul]
      simp only [two_smul]
      abel)
    omega
  intro n l hn hl
  obtain ⟨hz, hr⟩ := nsmul_add_nsmul_notMem_of_pairing_eq_zero P h0 h0' hsum n l hn hl
  refine ⟨hz, fun h => hr ?_⟩
  rw [hP.2.1]
  exact h

/-- The roots of a piece and their negatives. -/
def pieceRoots (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (lp lq lm : J) :
    Set (characterLattice T) :=
  {P.root lp, P.root lq, P.root lm, -P.root lp, -P.root lq, -P.root lm}

/-- The subgroup of rational points generated by the root groups of a piece and their
negatives. -/
def pieceGroup (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (lp lq lm : J) :
    Subgroup (rationalPoints G) :=
  Subgroup.closure (⋃ χ ∈ pieceRoots P lp lq lm, (rootGroupPoints j χ : Set (rationalPoints G)))

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
theorem rootGroupPoints_le_pieceGroup {lp lq lm : J} {χ : characterLattice T}
    (hχ : χ ∈ pieceRoots P lp lq lm) : rootGroupPoints j χ ≤ pieceGroup j P lp lq lm := by
  intro x hx
  exact Subgroup.subset_closure (Set.mem_biUnion hχ hx)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
/-- If the root groups of two pieces commute pairwise, so do the piece groups. -/
theorem commute_of_mem_pieceGroup {lp lq lm lp' lq' lm' : J}
    (h : ∀ χ ∈ pieceRoots P lp lq lm, ∀ χ' ∈ pieceRoots P lp' lq' lm',
      ∀ x ∈ rootGroupPoints j χ, ∀ y ∈ rootGroupPoints j χ', Commute x y)
    {x y : rationalPoints G} (hx : x ∈ pieceGroup j P lp lq lm)
    (hy : y ∈ pieceGroup j P lp' lq' lm') : Commute x y := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨χ, hχ, hx⟩ := Set.mem_iUnion₂.mp hx
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨χ', hχ', hy⟩ := Set.mem_iUnion₂.mp hy
      exact h χ hχ χ' hχ' x hx y hy
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  | one => exact Commute.one_left y
  | mul x z _ _ hx hz => exact hx.mul_left hz
  | inv x _ hx => exact hx.inv_left

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] in
include hline in
/-- Roots of two different pieces over `a` (with disjoint index sets over `a`) are orthogonal:
`⟨b, b'^∨⟩ = 0` for `b` in the first piece and `b'` in the second. -/
theorem piece_cross_pairing {lp lq lm lp' lq' lm' : J}
    (hpc : IsMultipliablePiece f P a lp lq lm) (hpc' : IsMultipliablePiece f P a lp' lq' lm')
    (hd : lp' ≠ lp ∧ lp' ≠ lq ∧ lq' ≠ lp ∧ lq' ≠ lq) :
    ∀ b ∈ ({lp, lq, lm} : Set J), ∀ b' ∈ ({lp', lq', lm'} : Set J), P.pairing b b' = 0 := by
  obtain ⟨hp, hq, hpq, hm⟩ := hpc
  obtain ⟨hp', hq', hpq', hm'⟩ := hpc'
  have hpqm := piece_pairing_pq hline hp hq hpq hm
  have hqpm := piece_pairing_qp hline hp hq hpq hm
  -- the four pairings between roots over `a`
  have base : ∀ {b b' : J}, (b = lp ∨ b = lq) → (b' = lp' ∨ b' = lq') → P.pairing b b' = 0 := by
    intro b b' hb hb'
    have hfb : f ≫ P.root b = a := by rcases hb with rfl | rfl <;> assumption
    have hfb' : f ≫ P.root b' = a := by rcases hb' with rfl | rfl <;> assumption
    have hne : b ≠ b' := by
      rintro rfl
      rcases hb with rfl | rfl <;> rcases hb' with h | h <;> tauto
    rcases pairing_eq_zero_or_neg_one hline hne hfb hfb' with h0 | h1
    · exact h0
    · exfalso
      rcases hb with rfl | rfl
      · have := partner_unique hline hp hq hfb' hpq hpqm h1
        rcases hb' with rfl | rfl <;> tauto
      · have := partner_unique hline hq hp hfb' (Ne.symm hpq) hqpm h1
        rcases hb' with rfl | rfl <;> tauto
  have hcm' := piece_coroot_m hline hp' hq' hpq' hm'
  have pm' : ∀ {b : J}, (b = lp ∨ b = lq) → P.pairing b lm' = 0 := by
    intro b hb
    rw [← P.root_coroot_eq_pairing, hcm', map_add, P.root_coroot_eq_pairing,
      P.root_coroot_eq_pairing, base hb (Or.inl rfl), base hb (Or.inr rfl), add_zero]
  intro b hb b' hb'
  rcases hb with rfl | rfl | rfl
  · rcases hb' with rfl | rfl | rfl
    · exact base (Or.inl rfl) (Or.inl rfl)
    · exact base (Or.inl rfl) (Or.inr rfl)
    · exact pm' (Or.inl rfl)
  · rcases hb' with rfl | rfl | rfl
    · exact base (Or.inr rfl) (Or.inl rfl)
    · exact base (Or.inr rfl) (Or.inr rfl)
    · exact pm' (Or.inr rfl)
  · have hlin : ∀ b'' : J, P.pairing b b'' = P.pairing lp b'' + P.pairing lq b'' := by
      intro b''
      rw [pairing_eq_of_root_eq P hm, map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
        P.root_coroot_eq_pairing]
    rcases hb' with rfl | rfl | rfl
    · rw [hlin, base (Or.inl rfl) (Or.inl rfl), base (Or.inr rfl) (Or.inl rfl), add_zero]
    · rw [hlin, base (Or.inl rfl) (Or.inr rfl), base (Or.inr rfl) (Or.inr rfl), add_zero]
    · rw [hlin, pm' (Or.inl rfl), pm' (Or.inr rfl), add_zero]

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
/-- Each root of a piece or its negative is the root of a base index or of its negation, with
restriction coefficient `±1` or `±2`. -/
theorem pieceRoots_signed_index {lp lq lm : J} (hpc : IsMultipliablePiece f P a lp lq lm)
    {χ : characterLattice T} (hχ : χ ∈ pieceRoots P lp lq lm) :
    ∃ b ∈ ({lp, lq, lm} : Set J), ∃ i : J, (i = b ∨ i = P.reflectionPerm b b) ∧
      P.root i = χ ∧ ∃ c : ℤ, f ≫ P.root i = c • a ∧ (c = 1 ∨ c = 2 ∨ c = -1 ∨ c = -2) := by
  obtain ⟨hp, hq, -, hm⟩ := hpc
  have hneg : ∀ b : J, P.root (P.reflectionPerm b b) = -P.root b := fun b => by
    rw [P.root_reflectionPerm, P.reflection_apply_self]
  have hmr : f ≫ P.root lm = (2 : ℤ) • a := by rw [hm, Preadditive.comp_add, hp, hq, two_zsmul]
  rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨lp, by simp, lp, Or.inl rfl, rfl, 1, by rw [hp, one_smul], by norm_num⟩
  · exact ⟨lq, by simp, lq, Or.inl rfl, rfl, 1, by rw [hq, one_smul], by norm_num⟩
  · exact ⟨lm, by simp, lm, Or.inl rfl, rfl, 2, hmr, by norm_num⟩
  · exact ⟨lp, by simp, _, Or.inr rfl, hneg lp, -1,
      by rw [hneg, Preadditive.comp_neg, hp, neg_smul, one_smul], by norm_num⟩
  · exact ⟨lq, by simp, _, Or.inr rfl, hneg lq, -1,
      by rw [hneg, Preadditive.comp_neg, hq, neg_smul, one_smul], by norm_num⟩
  · exact ⟨lm, by simp, _, Or.inr rfl, hneg lm, -2,
      by rw [hneg, Preadditive.comp_neg, hmr, neg_smul], by norm_num⟩

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
theorem pairing_signed_eq_zero {b b' i i' : J} (h : P.pairing b b' = 0)
    (hi : i = b ∨ i = P.reflectionPerm b b) (hi' : i' = b' ∨ i' = P.reflectionPerm b' b') :
    P.pairing i i' = 0 := by
  rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl <;> simp [h]

omit [Mono j.hom.hom.left] in
include hT hP hline in
/-- **Different pieces commute.** All root groups of two pieces with disjoint indices over `a`
commute with each other. -/
theorem pieces_commute {lp lq lm lp' lq' lm' : J}
    (hpc : IsMultipliablePiece f P a lp lq lm) (hpc' : IsMultipliablePiece f P a lp' lq' lm')
    (hd : lp' ≠ lp ∧ lp' ≠ lq ∧ lq' ≠ lp ∧ lq' ≠ lq) :
    ∀ χ ∈ pieceRoots P lp lq lm, ∀ χ' ∈ pieceRoots P lp' lq' lm',
      ∀ x ∈ rootGroupPoints j χ, ∀ y ∈ rootGroupPoints j χ', Commute x y := by
  intro χ hχ χ' hχ' x hx y hy
  obtain ⟨b, hb, i, hi, hiχ, c, hc, hcc⟩ := pieceRoots_signed_index hpc hχ
  obtain ⟨b', hb', i', hi', hiχ', c', hc', hcc'⟩ := pieceRoots_signed_index hpc' hχ'
  have hd' : lp ≠ lp' ∧ lp ≠ lq' ∧ lq ≠ lp' ∧ lq ≠ lq' :=
    ⟨Ne.symm hd.1, Ne.symm hd.2.2.1, Ne.symm hd.2.1, Ne.symm hd.2.2.2⟩
  have h0 := pairing_signed_eq_zero (piece_cross_pairing hline hpc hpc' hd b hb b' hb') hi hi'
  have h0' := pairing_signed_eq_zero (piece_cross_pairing hline hpc' hpc hd' b' hb' b hb) hi' hi
  rw [← hiχ] at hx
  rw [← hiχ'] at hy
  exact commute_of_no_strict_root_combinations j hT (P.root i) (P.root i')
    (root_mem_relativeRoots j hP i).1 (root_mem_relativeRoots j hP i').1
    (noStrictRootCombinations_of_orthogonal j hP hline h0 h0' hc hc' hcc hcc') hx hy

end Cross

section Families

/-- An ordered product over `Fin (r * 3)` is the product over `Fin r` of the consecutive
triples. -/
theorem list_ofFn_prod_finProd {M : Type*} [Monoid M] {r : ℕ} (F : Fin (r * 3) → M) :
    (List.ofFn F).prod = (List.ofFn fun l : Fin r =>
      F (finProdFinEquiv (l, 0)) * F (finProdFinEquiv (l, 1)) * F (finProdFinEquiv (l, 2))).prod := by
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  simp only [Function.comp_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]
  have h : ∀ c : Fin 3, (⟨l * 3 + c, by omega⟩ : Fin (r * 3)) = finProdFinEquiv (l, c) := by
    intro c
    ext
    simp [finProdFinEquiv]
    ring
  rw [h 0, h (Fin.succ 0), h ((Fin.succ 0).succ)]
  rfl

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  (f : S ⟶ T) {J : Type*} [Finite J]
  (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (a : characterLattice S)

/-- An enumeration of the roots over a multipliable character `a` by pieces: piece `l` has
roots `lp l`, `lq l` over `a` and `lm l` over `2a`; the pieces are disjoint and exhaust the
roots over `a` and `2a`. -/
structure PieceFamily where
  /-- The number of pieces. -/
  r : ℕ
  /-- The first root over `a` of each piece. -/
  lp : Fin r → J
  /-- The second root over `a` of each piece. -/
  lq : Fin r → J
  /-- The root over `2a` of each piece. -/
  lm : Fin r → J
  piece : ∀ l, IsMultipliablePiece f P a (lp l) (lq l) (lm l)
  disjoint : ∀ l l', l ≠ l' → lp l' ≠ lp l ∧ lp l' ≠ lq l ∧ lq l' ≠ lp l ∧ lq l' ≠ lq l
  lm_injective : Function.Injective lm
  cover_a : ∀ i, f ≫ P.root i = a → ∃ l, i = lp l ∨ i = lq l
  cover_two : ∀ i, f ≫ P.root i = (2 : ℤ) • a → ∃ l, i = lm l

namespace PieceFamily

variable {f P a} (F : PieceFamily f P a)

/-- The roots of the pieces, in the order `q, m, p` inside each piece. -/
def root (l : Fin F.r) (c : Fin 3) : characterLattice T :=
  ![P.root (F.lq l), P.root (F.lm l), P.root (F.lp l)] c

/-- The multiplicities `1, 2, 1` of the restrictions. -/
def mult (c : Fin 3) : ℕ := ![1, 2, 1] c

/-- The enumeration of all roots over `a` and `2a`. -/
def enum (k' : Fin (F.r * 3)) : characterLattice T :=
  F.root (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2

/-- The multiplicities along the enumeration. -/
def enumMult (k' : Fin (F.r * 3)) : ℕ := mult (finProdFinEquiv.symm k').2

omit [Finite J] in
theorem restrict_root (l : Fin F.r) (c : Fin 3) : f ≫ F.root l c = mult c • a := by
  obtain ⟨hp, hq, -, hm⟩ := F.piece l
  fin_cases c
  · simp [root, mult, hq]
  · simp [root, mult, hm, Preadditive.comp_add, hp, hq, two_nsmul]
  · simp [root, mult, hp]

omit [Finite J] in
theorem restrict_enum (k' : Fin (F.r * 3)) : f ≫ F.enum k' = F.enumMult k' • a :=
  F.restrict_root _ _

/-- The root indices of the pieces, in the order `q, m, p`. -/
def idx (l : Fin F.r) (c : Fin 3) : J := ![F.lq l, F.lm l, F.lp l] c

omit [Finite J] in
theorem root_eq_idx (l : Fin F.r) (c : Fin 3) : F.root l c = P.root (F.idx l c) := by
  fin_cases c <;> rfl

omit [Finite J] in
/-- Distinct positions of the piece enumeration carry distinct roots. -/
theorem root_injective (ha : ∀ n m : ℕ, n • a = m • a → n = m) {l₁ l₂ : Fin F.r}
    {c₁ c₂ : Fin 3} (h : F.root l₁ c₁ = F.root l₂ c₂) : l₁ = l₂ ∧ c₁ = c₂ := by
  have hmult : mult c₁ = mult c₂ := by
    apply ha
    rw [← F.restrict_root l₁ c₁, ← F.restrict_root l₂ c₂, h]
  have hidx : F.idx l₁ c₁ = F.idx l₂ c₂ := by
    apply P.root.injective
    rw [← F.root_eq_idx, ← F.root_eq_idx, h]
  have hp₁ := (F.piece l₁).2.2.1
  by_cases hl : l₁ = l₂
  · subst hl
    refine ⟨rfl, ?_⟩
    fin_cases c₁ <;> fin_cases c₂ <;>
      simp only [idx, mult, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hidx hmult <;>
      first | rfl | omega | exact absurd hidx hp₁ | exact absurd hidx.symm hp₁
  · exfalso
    obtain ⟨d1, d2, d3, d4⟩ := F.disjoint l₁ l₂ hl
    have hm := F.lm_injective.ne hl
    fin_cases c₁ <;> fin_cases c₂ <;>
      simp only [idx, mult, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hidx hmult <;>
      first | omega | exact d1 hidx.symm | exact d2 hidx.symm | exact d3 hidx.symm |
        exact d4 hidx.symm | exact hm hidx

omit [Finite J] in
theorem enum_injective (ha : ∀ n m : ℕ, n • a = m • a → n = m) :
    Function.Injective F.enum := by
  intro k₁ k₂ h
  obtain ⟨hl, hc⟩ := F.root_injective ha h
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hl hc

omit [Finite J] in
theorem enum_finProd (l : Fin F.r) (c : Fin 3) : F.enum (finProdFinEquiv (l, c)) = F.root l c := by
  simp [enum]

omit [Finite J] in
/-- **The piece enumeration enumerates the indivisible roots over the positive multiples of
`a`.** -/
theorem range_enum {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G) (hP : IsRootDatumOf j P) [P.IsReduced]
    [IsAddTorsionFree (characterLattice T)] (hline : RestrictsToMultipliableLine f P a)
    (ha : ∀ n m : ℕ, n • a = m • a → n = m) :
    Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)) := by
  ext χ
  constructor
  · rintro ⟨k', rfl⟩
    obtain ⟨⟨l, c⟩, rfl⟩ := finProdFinEquiv.surjective k'
    rw [F.enum_finProd, F.root_eq_idx]
    have hmc : 1 ≤ mult c ∧ mult c ≤ 2 := by fin_cases c <;> simp [mult]
    refine ⟨root_mem_relativeRoots j hP _, ⟨mult c, hmc.1, by omega, ?_⟩, ?_⟩
    · change mult c • a = f ≫ P.root (F.idx l c)
      rw [← F.root_eq_idx, F.restrict_root]
    · rintro b hb ⟨n, -, hn, hnb⟩ m hm hmb
      change n • a = f ≫ b at hnb
      have hrel : (m * n) • a = mult c • a := by
        rw [← F.restrict_root l c, F.root_eq_idx, ← hmb, Preadditive.comp_nsmul, ← hnb,
          smul_smul]
      have hmn := ha _ _ hrel
      have hm2 : m = 2 := by
        have : m * n ≤ 2 := hmn ▸ hmc.2
        nlinarith
      subst hm2
      obtain ⟨ib, hib⟩ := mem_range_root_of_mem_relativeRoots j hP hb
      apply P.nsmul_notMem_range_root (n := 2) (i := ib)
      exact ⟨F.idx l c, by rw [← hmb, hib]⟩
  · rintro ⟨hχ, ⟨n, -, hn, hnχ⟩, -⟩
    change n • a = f ≫ χ at hnχ
    obtain ⟨i, rfl⟩ := mem_range_root_of_mem_relativeRoots j hP hχ
    have hcases := hline i n (by rw [← hnχ, natCast_zsmul])
    rcases hcases with h1 | h2 | h3 | h4
    · have hn1 : n = 1 := by exact_mod_cast h1
      subst hn1
      obtain ⟨l, rfl | rfl⟩ := F.cover_a i (by rw [← hnχ, one_smul])
      · exact ⟨finProdFinEquiv (l, 2), by rw [F.enum_finProd]; rfl⟩
      · exact ⟨finProdFinEquiv (l, 0), by rw [F.enum_finProd]; rfl⟩
    · have hn2 : n = 2 := by exact_mod_cast h2
      subst hn2
      obtain ⟨l, rfl⟩ := F.cover_two i (by rw [← hnχ, two_zsmul, two_nsmul])
      exact ⟨finProdFinEquiv (l, 1), by rw [F.enum_finProd]; rfl⟩
    · omega
    · omega

end PieceFamily

section Coordinates

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {f : S ⟶ T} {J : Type*}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {a : characterLattice S}
  (F : PieceFamily f P a)

namespace PieceFamily

/-- The ordered product of piece triples. -/
def tripleProd (x z y : Fin F.r → rationalPoints G) : rationalPoints G :=
  (List.ofFn fun l => x l * z l * y l).prod

/-- Coordinates along the enumeration, assembled from piece triples. -/
def coords (x z y : Fin F.r → rationalPoints G)
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) :
    ∀ k' : Fin (F.r * 3), (RelativeRoot.subgroup j (F.enum k')).carrier (Over.mk (𝟙 _)) :=
  fun k' => ⟨![x (finProdFinEquiv.symm k').1, z (finProdFinEquiv.symm k').1,
      y (finProdFinEquiv.symm k').1] (finProdFinEquiv.symm k').2, by
    change _ ∈ rootGroupPoints j (F.root _ _)
    generalize (finProdFinEquiv.symm k').2 = c
    fin_cases c
    · exact hx _
    · exact hz _
    · exact hy _⟩

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] in
theorem rootPointsProduct_coords (x z y : Fin F.r → rationalPoints G)
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) :
    RelativeRoot.rootPointsProduct j F.enum (Over.mk (𝟙 _)) (F.coords j x z y hx hz hy) =
      F.tripleProd x z y := by
  unfold RelativeRoot.rootPointsProduct tripleProd
  rw [list_ofFn_prod_finProd]
  simp [coords]

/-- **Piece coordinates.** Every point of the restricted root group of `a` is an ordered
product of piece triples, and the triples are unique. -/
theorem existsUnique_triples (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (ha0 : a ≠ 0)
    (hinj : Function.Injective F.enum)
    (hrange : Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)))
    {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) :
    ∃ x z y : Fin F.r → rationalPoints G, (∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l))) ∧
      (∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l))) ∧
      (∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) ∧ F.tripleProd x z y = g := by
  obtain ⟨X, hX, -⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct hS hT f j hE a
      ha0 F.enum hinj hrange (Over.mk (𝟙 _)) g).mp hg
  have key : ∀ (l : Fin F.r) (c : Fin 3) (x : rationalPoints G),
      x ∈ rootGroupPoints j (F.enum (finProdFinEquiv (l, c))) →
        x ∈ rootGroupPoints j (F.root l c) := fun l c x hx => by rwa [F.enum_finProd] at hx
  refine ⟨fun l => (X (finProdFinEquiv (l, 0))).val, fun l => (X (finProdFinEquiv (l, 1))).val,
    fun l => (X (finProdFinEquiv (l, 2))).val, fun l => key l 0 _ (X _).prop,
    fun l => key l 1 _ (X _).prop, fun l => key l 2 _ (X _).prop, ?_⟩
  · rw [← hX]
    unfold RelativeRoot.rootPointsProduct tripleProd
    rw [list_ofFn_prod_finProd]

/-- Uniqueness of piece triples. -/
theorem triples_eq_of_tripleProd_eq (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (ha0 : a ≠ 0)
    (hinj : Function.Injective F.enum)
    (hrange : Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)))
    {x z y x' z' y' : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l)))
    (hx' : ∀ l, x' l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz' : ∀ l, z' l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy' : ∀ l, y' l ∈ rootGroupPoints j (P.root (F.lp l)))
    (hg : F.tripleProd x z y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (h : F.tripleProd x z y = F.tripleProd x' z' y') : x = x' ∧ z = z' ∧ y = y' := by
  obtain ⟨X, -, huniq⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct hS hT f j hE a
      ha0 F.enum hinj hrange (Over.mk (𝟙 _)) _).mp hg
  have h1 := huniq _ (F.rootPointsProduct_coords j x z y hx hz hy)
  have h2 := huniq _ ((F.rootPointsProduct_coords j x' z' y' hx' hz' hy').trans h.symm)
  have hc := h1.trans h2.symm
  refine ⟨funext fun l => ?_, funext fun l => ?_, funext fun l => ?_⟩
  · have := congrArg (fun C => (C (finProdFinEquiv (l, 0))).val) hc
    simpa [coords] using this
  · have := congrArg (fun C => (C (finProdFinEquiv (l, 1))).val) hc
    simpa [coords] using this
  · have := congrArg (fun C => (C (finProdFinEquiv (l, 2))).val) hc
    simpa [coords] using this

/-- **The restricted value of a product of piece triples.** If every `m`-coordinate has value
`2c` and every `p`- and `q`-coordinate has value at least `c`, the restricted value at `a` is
`c`. -/
theorem tripleProd_value (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) {φ : RootFunctionFamily T G}
    (hφ : IsRootDatumValuation j φ)
    (hα : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hinj : Function.Injective F.enum)
    (hrange : Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)))
    (hr : 0 < F.r) {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) (c : ℝ)
    (hzc : ∀ l, φ (P.root (F.lm l)) (z l) = ((2 * c : ℝ) : WithTop ℝ))
    (hxc : ∀ l, ((c : ℝ) : WithTop ℝ) ≤ φ (P.root (F.lq l)) (x l))
    (hyc : ∀ l, ((c : ℝ) : WithTop ℝ) ≤ φ (P.root (F.lp l)) (y l)) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f a (F.tripleProd x z y) = c := by
  have hα0 : a ≠ 0 := hα.1
  have hprod := F.rootPointsProduct_coords j x z y hx hz hy
  have hbounds := fun r => mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    hS hT hE hφ f a hα0 r F.enum F.enumMult hinj hrange F.restrict_enum
    (F.coords j x z y hx hz hy) _ hprod
  -- the coordinate bounds, piece by piece
  have hpiece : ∀ r : ℝ, (∀ k', ((F.enumMult k' * r : ℝ) : WithTop ℝ) ≤
      φ (F.enum k') (F.coords j x z y hx hz hy k').val) ↔
        ∀ l, ((r : ℝ) : WithTop ℝ) ≤ φ (P.root (F.lq l)) (x l) ∧
          ((2 * r : ℝ) : WithTop ℝ) ≤ φ (P.root (F.lm l)) (z l) ∧
          ((r : ℝ) : WithTop ℝ) ≤ φ (P.root (F.lp l)) (y l) := by
    intro r
    constructor
    · intro h l
      refine ⟨?_, ?_, ?_⟩
      · have := h (finProdFinEquiv (l, 0))
        simpa [enumMult, mult, coords, enum, root] using this
      · have := h (finProdFinEquiv (l, 1))
        simpa [enumMult, mult, coords, enum, root] using this
      · have := h (finProdFinEquiv (l, 2))
        simpa [enumMult, mult, coords, enum, root] using this
    · intro h k'
      obtain ⟨⟨l, c'⟩, rfl⟩ := finProdFinEquiv.surjective k'
      obtain ⟨h0, h1, h2⟩ := h l
      fin_cases c' <;> simpa [enumMult, mult, coords, enum, root] using ‹_›
  have hmem : F.tripleProd x z y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a := by
    apply torusRestrictedRootDepthSubgroup_le_rootGroupPoints hS hT hφ f a hα0 c
    rw [hbounds c, hpiece c]
    intro l
    exact ⟨hxc l, (hzc l).ge, hyc l⟩
  have hiff : ∀ r : ℝ, (r : WithTop ℝ) ≤
      torusRestrictedRootFunctionFamily hS hT hE hφ f a (F.tripleProd x z y) ↔ r ≤ c := by
    intro r
    rw [le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f a hα _ hmem r, hbounds r, hpiece r]
    constructor
    · intro h
      have := (h ⟨0, hr⟩).2.1
      rw [hzc] at this
      have := WithTop.coe_le_coe.mp this
      linarith
    · intro hrc l
      refine ⟨le_trans (WithTop.coe_le_coe.mpr hrc) (hxc l), ?_,
        le_trans (WithTop.coe_le_coe.mpr hrc) (hyc l)⟩
      rw [hzc]
      exact WithTop.coe_le_coe.mpr (by linarith)
  generalize torusRestrictedRootFunctionFamily hS hT hE hφ f a (F.tripleProd x z y) = v at hiff ⊢
  induction v using WithTop.recTopCoe with
  | top =>
    have h := (hiff (c + 1)).mp le_top
    linarith
  | coe t =>
    have h1 : t ≤ c := (hiff t).mp le_rfl
    have h2 : (c : WithTop ℝ) ≤ t := (hiff c).mpr le_rfl
    rw [WithTop.coe_le_coe] at h2
    rw [le_antisymm h1 h2]

end PieceFamily

end Coordinates

section Negation

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {f : S ⟶ T} {J : Type*}
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {a : characterLattice S}

theorem root_reflectionPerm_self (i : J) : P.root (P.reflectionPerm i i) = -P.root i := by
  rw [P.root_reflectionPerm, P.reflection_apply_self]

theorem reflectionPerm_self_eq_iff {i i' : J} :
    P.reflectionPerm i i = P.reflectionPerm i' i' ↔ i = i' := by
  constructor
  · intro h
    apply P.root.injective
    have := congrArg P.root h
    rw [root_reflectionPerm_self, root_reflectionPerm_self] at this
    exact neg_injective this
  · rintro rfl
    rfl

theorem eq_reflectionPerm_self_of_root_eq_neg {i i' : J} (h : P.root i = -P.root i') :
    i = P.reflectionPerm i' i' := by
  apply P.root.injective
  rw [h, root_reflectionPerm_self]

/-- The negative of a piece family: the negated roots form a piece family over `-a`, in the
order `-q, -m, -p` inside each piece. -/
def PieceFamily.neg (F : PieceFamily f P a) : PieceFamily f P (-a) where
  r := F.r
  lp l := P.reflectionPerm (F.lp l) (F.lp l)
  lq l := P.reflectionPerm (F.lq l) (F.lq l)
  lm l := P.reflectionPerm (F.lm l) (F.lm l)
  piece l := by
    obtain ⟨hp, hq, hpq, hm⟩ := F.piece l
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [root_reflectionPerm_self, Preadditive.comp_neg, hp]
    · rw [root_reflectionPerm_self, Preadditive.comp_neg, hq]
    · exact fun h => hpq (reflectionPerm_self_eq_iff.mp h)
    · rw [root_reflectionPerm_self, root_reflectionPerm_self, root_reflectionPerm_self, hm,
        neg_add]
  disjoint l l' hl := by
    obtain ⟨d1, d2, d3, d4⟩ := F.disjoint l l' hl
    exact ⟨fun h => d1 (reflectionPerm_self_eq_iff.mp h),
      fun h => d2 (reflectionPerm_self_eq_iff.mp h),
      fun h => d3 (reflectionPerm_self_eq_iff.mp h),
      fun h => d4 (reflectionPerm_self_eq_iff.mp h)⟩
  lm_injective l l' h := F.lm_injective (reflectionPerm_self_eq_iff.mp h)
  cover_a i hi := by
    have hi' : f ≫ P.root (P.reflectionPerm i i) = a := by
      rw [root_reflectionPerm_self, Preadditive.comp_neg, hi, neg_neg]
    obtain ⟨l, hl | hl⟩ := F.cover_a _ hi'
    · refine ⟨l, Or.inl (eq_reflectionPerm_self_of_root_eq_neg ?_)⟩
      rw [← hl, root_reflectionPerm_self, neg_neg]
    · refine ⟨l, Or.inr (eq_reflectionPerm_self_of_root_eq_neg ?_)⟩
      rw [← hl, root_reflectionPerm_self, neg_neg]
  cover_two i hi := by
    have hi' : f ≫ P.root (P.reflectionPerm i i) = (2 : ℤ) • a := by
      rw [root_reflectionPerm_self, Preadditive.comp_neg, hi, smul_neg, neg_neg]
    obtain ⟨l, hl⟩ := F.cover_two _ hi'
    refine ⟨l, eq_reflectionPerm_self_of_root_eq_neg ?_⟩
    rw [← hl, root_reflectionPerm_self, neg_neg]

theorem RestrictsToMultipliableLine.neg (hline : RestrictsToMultipliableLine f P a) :
    RestrictsToMultipliableLine f P (-a) := by
  intro l n h
  rw [smul_neg, ← neg_smul] at h
  rcases hline l (-n) h with h1 | h1 | h1 | h1 <;> omega

/-- **Uniqueness of decompositions.** If two roots over `a` sum to the root `m` of a piece,
they are the two roots of that piece over `a`. -/
theorem piece_decomposition_unique [Finite J] (hline : RestrictsToMultipliableLine f P a)
    {lp lq lm : J} (hpc : IsMultipliablePiece f P a lp lq lm) {i i' : J}
    (hi : f ≫ P.root i = a) (hi' : f ≫ P.root i' = a)
    (h : P.root i + P.root i' = P.root lm) :
    (i = lp ∧ i' = lq) ∨ (i = lq ∧ i' = lp) := by
  obtain ⟨hp, hq, hpq, hm⟩ := hpc
  have hqp := piece_pairing_qp hline hp hq hpq hm
  have hsum : P.pairing i lp + P.pairing i' lp = 1 := by
    have h1 : P.toLinearMap (P.root i + P.root i') (P.coroot lp) = 1 := by
      rw [h, hm, map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
        P.root_coroot_eq_pairing, P.pairing_same, hqp]
      norm_num
    rw [map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
      P.root_coroot_eq_pairing] at h1
    exact h1
  by_cases hip : i = lp
  · subst hip
    left
    refine ⟨rfl, P.root.injective ?_⟩
    have := h.trans hm
    exact add_left_cancel this
  by_cases hi'p : i' = lp
  · subst hi'p
    right
    refine ⟨P.root.injective ?_, rfl⟩
    have := h.trans hm
    rw [add_comm (P.root i') (P.root lq)] at this
    exact add_right_cancel this
  exfalso
  have h1 := pairing_eq_zero_or_neg_one hline hip hi hp
  have h2 := pairing_eq_zero_or_neg_one hline hi'p hi' hp
  omega

/-- **Existence of a piece family.** If every root over `a` has a partner over `a` with a root
as sum, and every root over `2a` is a sum of two roots over `a`, the roots over `a` and `2a`
are enumerated by a piece family. -/
theorem PieceFamily.nonempty_of_partners [Finite J] [P.IsReduced]
    [IsAddTorsionFree (characterLattice T)]
    (hline : RestrictsToMultipliableLine f P a)
    (hpart : ∀ i : J, f ≫ P.root i = a →
      ∃ i', f ≫ P.root i' = a ∧ P.root i + P.root i' ∈ Set.range P.root)
    (hdec : ∀ i : J, f ≫ P.root i = (2 : ℤ) • a →
      ∃ i' i'', f ≫ P.root i' = a ∧ f ≫ P.root i'' = a ∧ P.root i = P.root i' + P.root i'') :
    Nonempty (PieceFamily f P a) := by
  classical
  have hred : ∀ i : J, P.root i + P.root i ∉ Set.range P.root := fun i h => by
    rw [← two_nsmul] at h
    exact P.nsmul_notMem_range_root (n := 2) (i := i) h
  have hfin : {i : J | f ≫ P.root i = (2 : ℤ) • a}.Finite := Set.toFinite _
  obtain ⟨r, e, he⟩ := hfin.fin_embedding
  have hem : ∀ l, f ≫ P.root (e l) = (2 : ℤ) • a := fun l =>
    (show e l ∈ {i : J | f ≫ P.root i = (2 : ℤ) • a} from he ▸ Set.mem_range_self l)
  choose lp lq hlp hlq hsum using fun l => hdec (e l) (hem l)
  have hpiece : ∀ l, IsMultipliablePiece f P a (lp l) (lq l) (e l) := fun l =>
    ⟨hlp l, hlq l, fun h => hred (lp l) ⟨e l, by rw [hsum l, ← h]⟩, hsum l⟩
  -- two pieces sharing their first root have the same sum
  have hsame : ∀ {p q m p' q' m' : J}, IsMultipliablePiece f P a p q m →
      IsMultipliablePiece f P a p' q' m' → p = p' → P.root m = P.root m' := by
    intro p q m p' q' m' h h' hpp
    subst hpp
    have h1 := (exists_root_add_iff hline h.2.2.1 h.1 h.2.1).mp ⟨m, h.2.2.2⟩
    have h2 := (exists_root_add_iff hline h'.2.2.1 h'.1 h'.2.1).mp ⟨m', h'.2.2.2⟩
    have hqq := partner_unique hline h.1 h.2.1 h'.2.1 h.2.2.1 h1 h2
    rw [h.2.2.2, h'.2.2.2, hqq]
  refine ⟨⟨r, lp, lq, e, hpiece, ?_, e.injective, ?_, ?_⟩⟩
  · intro l l' hl
    refine ⟨fun h => hl ?_, fun h => hl ?_, fun h => hl ?_, fun h => hl ?_⟩
    · exact e.injective (P.root.injective (hsame (hpiece l) (hpiece l') h.symm))
    · exact e.injective (P.root.injective (hsame (hpiece l).swap (hpiece l') h.symm))
    · exact e.injective (P.root.injective (hsame (hpiece l) (hpiece l').swap h.symm))
    · exact e.injective (P.root.injective (hsame (hpiece l).swap (hpiece l').swap h.symm))
  · intro i hi
    obtain ⟨i', hi', m, hm⟩ := hpart i hi
    have hm2 : m ∈ Set.range e := by
      rw [he]
      change f ≫ P.root m = (2 : ℤ) • a
      rw [hm, Preadditive.comp_add, hi, hi', two_zsmul]
    obtain ⟨l, rfl⟩ := hm2
    refine ⟨l, ?_⟩
    rcases piece_decomposition_unique hline (hpiece l) hi hi' hm.symm with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · intro i hi
    have hm2 : i ∈ Set.range e := by
      rw [he]
      exact hi
    obtain ⟨l, rfl⟩ := hm2
    exact ⟨l, rfl⟩

end Negation

end Families

section Separation

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) (f : S ⟶ T)
  [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]

include hS in
/-- **Separation.** Let `n = g' g g''` normalize both `j` and `groupHom f ≫ j`, with `g ≠ 1` in
the restricted root group of `α` and `g', g''` in that of `-α`. If `Y g Z` normalizes `j` for
`Y, Z` in the restricted root group of `-α`, then `g' = Y` and `Y g Z = n`. -/
theorem eq_of_mul_mul_mem_normalizer {α : characterLattice S} (hα0 : α ≠ 0)
    {g g' g'' Y Z : rationalPoints G}
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) α) (hg1 : g ≠ 1)
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hN : g' * g * g'' ∈ normalizerPoints j)
    (hN' : g' * g * g'' ∈ normalizerPoints (CommGroupScheme.groupHom f ≫ j))
    (hY : Y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hZ : Z ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hNY : Y * g * Z ∈ normalizerPoints j) :
    g' = Y ∧ Y * g * Z = g' * g * g'' := by
  have hA : (g' * Y⁻¹)⁻¹ ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hY))
  have hconj := IsOppositeFactorPair.inv_conj_mem (CommGroupScheme.groupHom f ≫ j) hS hα0
    hg hg1 (p := (g', g'')) ⟨hg', hg'', hN'⟩ hA
  have hkey : (g' * g * g'')⁻¹ * (Y * g * Z) =
      ((g' * g * g'')⁻¹ * (g' * Y⁻¹)⁻¹ * (g' * g * g'')) * (g''⁻¹ * Z) := by
    group
  have hy : g''⁻¹ * Z ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg'') hZ
  have hone := normalizer_eq_one_of_mul_opposite_torusHom j hS f hα0
    ⟨(g' * g * g'')⁻¹ * (Y * g * Z), Subgroup.mul_mem _ (Subgroup.inv_mem _ hN) hNY⟩
    hconj hy hkey
  have hone' : (g' * g * g'')⁻¹ * (Y * g * Z) = 1 := by
    simpa using congrArg Subtype.val hone
  have hval : (g' * g * g'')⁻¹ * (g' * Y⁻¹)⁻¹ * (g' * g * g'') * (g''⁻¹ * Z) = 1 := by
    rw [← hkey, hone']
  have hx_eq := eq_inv_of_mul_eq_one_left hval
  have hx1 := RelativeRoot.eq_one_of_mem_subgroup_of_mem_opposite
    (CommGroupScheme.groupHom f ≫ j) hS hα0 hconj (hx_eq ▸ Subgroup.inv_mem _ hy)
  have hA1 : (g' * Y⁻¹)⁻¹ = 1 := by
    have h2 : (g' * g * g'')⁻¹ * (g' * Y⁻¹)⁻¹ = (g' * g * g'')⁻¹ * 1 := by
      rw [mul_one]
      exact mul_eq_one_iff_eq_inv.mp hx1
    exact mul_left_cancel h2
  refine ⟨mul_inv_eq_one.mp (inv_eq_one.mp hA1), ?_⟩
  have := mul_eq_one_iff_eq_inv.mp hone'
  exact (inv_injective this).symm

end Separation

section Core

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hjc : IsClosedSubgroup j) (hP : IsRootDatumOf j P)
  (hE : RelativeRoot.HasOppositeFactorPairs j)
  {f : S ⟶ T} {a : characterLattice S} (hline : RestrictsToMultipliableLine f P a)

include hT hjc hP hE hline in
/-- The piece factorization with a uniform left factor: `h = (Y⁻¹ d e) N' (f' c Y'⁻¹)` with
`N'` normalizing `j`, in both cases of `piece_factorization`. -/
theorem piece_factorization_uniform {lp lq lm : J} (hpc : IsMultipliablePiece f P a lp lq lm)
    {Xq Xm Xp : rationalPoints G}
    (hXq : Xq ∈ rootGroupPoints j (P.root lq)) (hXm : Xm ∈ rootGroupPoints j (P.root lm))
    (hXm1 : Xm ≠ 1) (hXp : Xp ∈ rootGroupPoints j (P.root lp))
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root lm) Xm pr) :
    ∃ e ∈ rootGroupPoints j (-P.root lq), ∃ N' : normalizerPoints j,
      ∃ f' ∈ rootGroupPoints j (-P.root lp), ∃ c ∈ rootGroupPoints j (-P.root lq),
        Xq * Xm * Xp = (pr.1⁻¹ * (pr.1 * Xq * pr.1⁻¹ * Xq⁻¹) * e) * (N' : rationalPoints G) *
          (f' * c * pr.2⁻¹) := by
  obtain ⟨hp, hq, hpq, hm⟩ := hpc
  rcases piece_factorization j hT hjc hP hE hline hp hq hpq hm hXq hXm hXm1 hXp hpr with
    ⟨e, he, τ, f', hf', c, hc, h⟩ | ⟨e, he, ν, c, hc, h, -⟩
  · exact ⟨e, he, ⟨pr.1 * Xm * pr.2, hpr.2.2⟩ * τ, f', hf', c, hc, by rw [h]; rfl⟩
  · exact ⟨e, he, ν, 1, Subgroup.one_mem _, c, hc, by rw [h, one_mul]⟩

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom] [Mono j.hom.hom.left]
  [Finite J] in
theorem mem_pieceGroup_of_mem {lp lq lm : J} {χ : characterLattice T}
    (hχ : χ ∈ pieceRoots P lp lq lm) {x : rationalPoints G} (hx : x ∈ rootGroupPoints j χ) :
    x ∈ pieceGroup j P lp lq lm :=
  rootGroupPoints_le_pieceGroup j hχ hx

/-- The inverse of an ordered product of pairwise commuting factors is the ordered product of
the inverses. -/
theorem list_ofFn_prod_inv_of_commute {M : Type*} [Group M] {r : ℕ} (L : Fin r → M)
    (h : ∀ l m, l ≠ m → Commute (L l) (L m)) :
    (List.ofFn L).prod⁻¹ = (List.ofFn fun l => (L l)⁻¹).prod := by
  rw [List.prod_inv_reverse]
  apply List.Perm.prod_eq'
  · rw [List.map_ofFn]
    exact (List.reverse_perm _)
  · rw [List.pairwise_reverse, List.pairwise_map, List.pairwise_ofFn]
    intro l m hlm
    exact ((h m l (ne_of_lt hlm).symm).inv_inv)

omit [LocallyOfFiniteType G.X.hom] [Finite J] in
include hT hE in
/-- Root groups of roots restricting to positive multiples of `c` lie in the restricted root
group of `c`. -/
theorem rootGroupPoints_le_comp (hS : IsSplitTorus S.toGrp) {c : characterLattice S}
    (hc : c ≠ 0) {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) {n : ℕ} (hn : 0 < n)
    (hfχ : f ≫ χ = n • c) :
    rootGroupPoints j χ ≤ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) c := by
  intro x hx
  have hcar := RelativeRoot.subgroup_comp_torusHom_carrier_eq_iSup hS hT f j hE c hc
    (Over.mk (𝟙 _))
  have hmem : f ≫ χ ∈ RelativeRoot.cyclicTail c 1 := ⟨n, hn, hn, hfχ.symm⟩
  have hle := le_iSup (fun ψ : {ψ : characterLattice T |
      ψ ∈ relativeRoots j ∧ f ≫ ψ ∈ RelativeRoot.cyclicTail c 1} =>
    (RelativeRoot.subgroup j ψ.val).carrier (Over.mk (𝟙 _))) ⟨χ, hχ, hmem⟩
  have h := hle hx
  rw [← hcar] at h
  exact h

include hT hjc hP hE hline in
/-- **Opposite factors over all pieces.** Let `g = ∏ₗ X_l Z_l Y_l` be a nontrivial point of the
restricted root group of `a`, written in piece coordinates with every `Z_l ≠ 1`, and let
`g' g g''` normalize both `j` and `groupHom f ≫ j` with `g', g''` in the restricted root group
of `-a`. Then `g'` has piece coordinates `(E_l, Y_l, D_l)` over `-a` with
`φ_{-m}(Y_l) + φ_m(Z_l) = 0` and `φ_{-p}(D_l) = φ_q(X_l) + φ_{-m}(Y_l)`. -/
theorem opposite_coordinates (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    {ω : kˣ → ℝ} (D : KPApartmentData j ω) (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus j) (x : D.Apartment)
    (F : PieceFamily f P a) (ha0 : a ≠ 0)
    {X Z Y : Fin F.r → rationalPoints G}
    (hX : ∀ l, X l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hZ : ∀ l, Z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hY : ∀ l, Y l ∈ rootGroupPoints j (P.root (F.lp l)))
    (hZ1 : ∀ l, Z l ≠ 1)
    (hg : F.tripleProd X Z Y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hg1 : F.tripleProd X Z Y ≠ 1) {g' g'' : rationalPoints G}
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a))
    (hN : g' * F.tripleProd X Z Y * g'' ∈ normalizerPoints j)
    (hN' : g' * F.tripleProd X Z Y * g'' ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ j)) :
    ∃ E Yv Dv : Fin F.r → rationalPoints G,
      (∀ l, E l ∈ rootGroupPoints j (P.root (F.neg.lq l))) ∧
      (∀ l, Yv l ∈ rootGroupPoints j (P.root (F.neg.lm l))) ∧
      (∀ l, Dv l ∈ rootGroupPoints j (P.root (F.neg.lp l))) ∧
      g' = F.neg.tripleProd E Yv Dv ∧
      (∀ l, x.val (P.root (F.neg.lm l)) (Yv l) + x.val (P.root (F.lm l)) (Z l) = 0) ∧
      (∀ l, x.val (P.root (F.neg.lp l)) (Dv l) =
        x.val (P.root (F.lq l)) (X l) + x.val (P.root (F.neg.lm l)) (Yv l)) := by
  classical
  have hφ := x.isValuation
  -- the pairs of the `m`-coordinates and the uniform piece factorizations
  choose pr hpr using fun l =>
    hE (P.root (F.lm l)) (root_mem_relativeRoots j hP _) (Z l) (hZ l) (hZ1 l)
  choose e he N' f' hf' c hc hfac using fun l =>
    piece_factorization_uniform j hT hjc hP hE hline (F.piece l) (hX l) (hZ l) (hZ1 l) (hY l)
      (hpr l)
  set d : Fin F.r → rationalPoints G :=
    fun l => (pr l).1 * X l * (pr l).1⁻¹ * (X l)⁻¹ with hd
  set L : Fin F.r → rationalPoints G := fun l => (pr l).1⁻¹ * d l * e l with hL
  set R : Fin F.r → rationalPoints G := fun l => f' l * c l * (pr l).2⁻¹ with hR
  have hdmem : ∀ l, d l ∈ rootGroupPoints j (-P.root (F.lp l)) := fun l =>
    piece_commutator_mem_neg_m_q j hT hE hP hline (F.piece l).1 (F.piece l).2.1
      (F.piece l).2.2.1 (F.piece l).2.2.2 (hpr l).1 (hX l)
  -- piece group memberships
  have pr_mem : ∀ l (χ : characterLattice T),
      (χ = P.root (F.lp l) ∨ χ = P.root (F.lq l) ∨ χ = P.root (F.lm l) ∨
        χ = -P.root (F.lp l) ∨ χ = -P.root (F.lq l) ∨ χ = -P.root (F.lm l)) →
      ∀ y ∈ rootGroupPoints j χ, y ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) := by
    intro l χ hχ y hy
    apply mem_pieceGroup_of_mem j _ hy
    rcases hχ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pieceRoots]
  have hLG : ∀ l, L l ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (pr_mem l _ (by tauto) _ (hpr l).1)) (pr_mem l _ (by tauto) _ (hdmem l)))
      (pr_mem l _ (by tauto) _ (he l))
  have hRG : ∀ l, R l ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (pr_mem l _ (by tauto) _ (hf' l))
      (pr_mem l _ (by tauto) _ (hc l))) (Subgroup.inv_mem _ (pr_mem l _ (by tauto) _ (hpr l).2.1))
  have hhG : ∀ l, X l * Z l * Y l ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (pr_mem l _ (by tauto) _ (hX l))
      (pr_mem l _ (by tauto) _ (hZ l))) (pr_mem l _ (by tauto) _ (hY l))
  have hNG : ∀ l, (N' l : rationalPoints G) ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) := by
    intro l
    have h : (N' l : rationalPoints G) = (L l)⁻¹ * (X l * Z l * Y l) * (R l)⁻¹ := by
      rw [hfac l]; simp only [hL, hR, hd]; group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLG l)) (hhG l))
      (Subgroup.inv_mem _ (hRG l))
  have hcomm : ∀ l m, l ≠ m → ∀ {u v : rationalPoints G},
      u ∈ pieceGroup j P (F.lp l) (F.lq l) (F.lm l) →
      v ∈ pieceGroup j P (F.lp m) (F.lq m) (F.lm m) → Commute u v := by
    intro l m hlm u v hu hv
    exact commute_of_mem_pieceGroup j
      (pieces_commute j hT hP hline (F.piece l) (F.piece m) (F.disjoint l m hlm)) hu hv
  -- assembling the pieces
  have hprod : F.tripleProd X Z Y = (List.ofFn L).prod *
      (List.ofFn fun l => (N' l : rationalPoints G)).prod * (List.ofFn R).prod := by
    unfold PieceFamily.tripleProd
    rw [← list_ofFn_prod_mul_mul L (fun l => (N' l : rationalPoints G)) R]
    · congr 1
      apply List.ofFn_inj.mpr
      funext l
      exact hfac l
    · intro l m hlm
      exact ⟨hcomm l m hlm (hNG l) (hLG m), hcomm l m hlm (hRG l) (hLG m),
        hcomm l m hlm (hRG l) (hNG m)⟩
  -- memberships in the restricted root group of `-a`
  have hrest : ∀ (χ : characterLattice T) (n : ℕ), 0 < n → χ ∈ relativeRoots j →
      f ≫ χ = n • (-a) → ∀ y ∈ rootGroupPoints j χ,
        y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := by
    intro χ n hn hχ hfχ y hy
    exact rootGroupPoints_le_comp j hT hE hS (neg_ne_zero.mpr ha0) hχ hn hfχ hy
  have hnegroot : ∀ i : J, -P.root i ∈ relativeRoots j := fun i =>
    neg_mem_relativeRoots_of_isRootDatumOf j hP (root_mem_relativeRoots j hP i)
  have hfp : ∀ l, f ≫ (-P.root (F.lp l)) = 1 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).1, one_smul]
  have hfq : ∀ l, f ≫ (-P.root (F.lq l)) = 1 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).2.1, one_smul]
  have hfm : ∀ l, f ≫ (-P.root (F.lm l)) = 2 • (-a) := fun l => by
    rw [Preadditive.comp_neg, (F.piece l).2.2.2, Preadditive.comp_add, (F.piece l).1,
      (F.piece l).2.1, smul_neg, two_nsmul]
  have hLS : ∀ l, L l ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (hrest _ 2 two_pos (hnegroot _) (hfm l) _ (hpr l).1))
      (hrest _ 1 one_pos (hnegroot _) (hfp l) _ (hdmem l)))
      (hrest _ 1 one_pos (hnegroot _) (hfq l) _ (he l))
  have hRS : ∀ l, R l ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := fun l =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (hrest _ 1 one_pos (hnegroot _) (hfp l) _ (hf' l))
      (hrest _ 1 one_pos (hnegroot _) (hfq l) _ (hc l)))
      (Subgroup.inv_mem _ (hrest _ 2 two_pos (hnegroot _) (hfm l) _ (hpr l).2.1))
  have hLpS : (List.ofFn L).prod ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact hLS l
  have hRpS : (List.ofFn R).prod ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact hRS l
  have hNprod : ((List.ofFn L).prod)⁻¹ * F.tripleProd X Z Y * ((List.ofFn R).prod)⁻¹ ∈
      normalizerPoints j := by
    have h : ((List.ofFn L).prod)⁻¹ * F.tripleProd X Z Y * ((List.ofFn R).prod)⁻¹ =
        (List.ofFn fun l => (N' l : rationalPoints G)).prod := by
      rw [hprod]; group
    rw [h]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hy
    exact (N' l).prop
  obtain ⟨hg'eq, -⟩ := eq_of_mul_mul_mem_normalizer j hS f ha0 hg hg1 hg' hg'' hN hN'
    (Subgroup.inv_mem _ hLpS) (Subgroup.inv_mem _ hRpS) hNprod
  have hinv := list_ofFn_prod_inv_of_commute L (fun l m hlm => hcomm l m hlm (hLG l) (hLG m))
  -- the coordinates of `g'`
  refine ⟨fun l => (e l)⁻¹, fun l => (pr l).1, fun l => (d l)⁻¹, fun l => ?_, fun l => ?_,
    fun l => ?_, ?_, fun l => ?_, fun l => ?_⟩
  · change (e l)⁻¹ ∈ rootGroupPoints j (P.root (P.reflectionPerm (F.lq l) (F.lq l)))
    rw [root_reflectionPerm_self]
    exact Subgroup.inv_mem _ (he l)
  · change (pr l).1 ∈ rootGroupPoints j (P.root (P.reflectionPerm (F.lm l) (F.lm l)))
    rw [root_reflectionPerm_self]
    exact (hpr l).1
  · change (d l)⁻¹ ∈ rootGroupPoints j (P.root (P.reflectionPerm (F.lp l) (F.lp l)))
    rw [root_reflectionPerm_self]
    exact Subgroup.inv_mem _ (hdmem l)
  · rw [hg'eq, hinv]
    unfold PieceFamily.tripleProd
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    have hYd : (pr l).1 * (d l)⁻¹ = (d l)⁻¹ * (pr l).1 :=
      (piece_commute_neg_m_neg_p j hT hP hline (F.piece l).1 (F.piece l).2.1 (F.piece l).2.2.1
        (F.piece l).2.2.2 (hpr l).1 (Subgroup.inv_mem _ (hdmem l))).eq
    change (L l)⁻¹ = (e l)⁻¹ * (pr l).1 * (d l)⁻¹
    simp only [hL]
    rw [mul_assoc (e l)⁻¹, hYd]
    group
  · change x.val (P.root (P.reflectionPerm (F.lm l) (F.lm l))) (pr l).1 +
      x.val (P.root (F.lm l)) (Z l) = 0
    rw [root_reflectionPerm_self]
    exact hφ.opposite _ (root_mem_relativeRoots j hP _) (Z l) (hZ l) (hZ1 l) (pr l).1 (hpr l).1
      (pr l).2 (hpr l).2.1 (hpr l).2.2
  · change x.val (P.root (P.reflectionPerm (F.lp l) (F.lp l))) (d l)⁻¹ =
      x.val (P.root (F.lq l)) (X l) + x.val (P.root (P.reflectionPerm (F.lm l) (F.lm l))) (pr l).1
    rw [root_reflectionPerm_self, root_reflectionPerm_self, RootReflectionProof.apply_inv hφ]
    have hY1 : (pr l).1 ≠ 1 :=
      (RelativeRoot.IsOppositeFactorPair.factors_ne_one j hT (root_mem_relativeRoots j hP _).1
        (hZ l) (hZ1 l) (hpr l)).1
    exact piece_val_commutator_neg_m j hT hjc hP hE hline (F.piece l).1 (F.piece l).2.1
      (F.piece l).2.2.1 (F.piece l).2.2.2 D hG hi x (hpr l).1 hY1 (hX l)

end Core

section Symmetry

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hP : IsRootDatumOf j P)
  (hE : RelativeRoot.HasOppositeFactorPairs j)
  {f : S ⟶ T} {a : characterLattice S} (hline : RestrictsToMultipliableLine f P a)

variable (P f a) in
/-- A **piece symmetry** of the roots over the multiples of `a`: an injective endomorphism `s` of
the rational points and an injective map `σ` on root indices, additive on roots, preserving
the restriction to every integer multiple of `a`, with `s` carrying `U_{P.root i}` into
`U_{P.root (σ i)}`. Galois automorphisms of a splitting field give the examples. -/
structure IsPieceSymmetry (s : rationalPoints G →* rationalPoints G) (σi : J → J) : Prop where
  injective : Function.Injective s
  index_injective : Function.Injective σi
  root_add : ∀ i i' i'' : J, P.root i = P.root i' + P.root i'' →
    P.root (σi i) = P.root (σi i') + P.root (σi i'')
  restrict : ∀ (i : J) (n : ℤ), f ≫ P.root i = n • a → f ≫ P.root (σi i) = n • a
  mem : ∀ (i : J) (w : rationalPoints G), w ∈ rootGroupPoints j (P.root i) →
    s w ∈ rootGroupPoints j (P.root (σi i))

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
/-- A piece symmetry over a negated character. -/
theorem IsPieceSymmetry.neg {s : rationalPoints G →* rationalPoints G} {σi : J → J}
    (h : IsPieceSymmetry j P f a s σi) : IsPieceSymmetry j P f (-a) s σi where
  injective := h.injective
  index_injective := h.index_injective
  root_add := h.root_add
  restrict i n hi := by
    have h' := h.restrict i (-n) (by rw [hi, smul_neg, neg_smul])
    rw [h', smul_neg, neg_smul]
  mem := h.mem

include hT hP hE hline in
/-- **Symmetries permute pieces.** Let `(s, σ)` be a piece symmetry. If `s` fixes a product
`∏ₗ x_l z_l y_l` of piece triples, then for every piece `l` sent to the piece `l'`
(`σ (lm l) = lm l'`), either `σ` preserves the order of the two roots over `a` and `s` carries
the triple of `l` to that of `l'`, or `σ` exchanges them and `s y_l = x_{l'}`, `s x_l = y_{l'}`,
`s (z_l [x_l, y_l]) = z_{l'}`. -/
theorem PieceFamily.symmetry (F : PieceFamily f P a) (hS : IsSplitTorus S.toGrp) (ha0 : a ≠ 0)
    (hinj : Function.Injective F.enum)
    (hrange : Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)))
    {s : rationalPoints G →* rationalPoints G} {σi : J → J}
    (hsym : IsPieceSymmetry j P f a s σi)
    {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l)))
    (hg : F.tripleProd x z y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hfix : s (F.tripleProd x z y) = F.tripleProd x z y)
    {l l' : Fin F.r} (hll' : σi (F.lm l) = F.lm l') :
    (σi (F.lp l) = F.lp l' ∧ σi (F.lq l) = F.lq l' ∧
        s (x l) = x l' ∧ s (z l) = z l' ∧ s (y l) = y l') ∨
      (σi (F.lp l) = F.lq l' ∧ σi (F.lq l) = F.lp l' ∧
        s (y l) = x l' ∧ s (x l) = y l' ∧
        s (z l * (x l * y l * (x l)⁻¹ * (y l)⁻¹)) = z l') := by
  classical
  -- the permutation of pieces
  have hm2 : ∀ l₀, f ≫ P.root (σi (F.lm l₀)) = (2 : ℤ) • a := fun l₀ =>
    hsym.restrict _ 2 (by
      rw [(F.piece l₀).2.2.2, Preadditive.comp_add, (F.piece l₀).1, (F.piece l₀).2.1, two_zsmul])
  choose π hπ using fun l₀ => F.cover_two _ (hm2 l₀)
  have hπeq : ∀ l₀ l₁, σi (F.lm l₀) = F.lm l₁ → π l₀ = l₁ := fun l₀ l₁ h =>
    F.lm_injective ((hπ l₀).symm.trans h)
  have hπinj : Function.Injective π := by
    intro l₁ l₂ h
    apply F.lm_injective
    apply hsym.index_injective
    rw [hπ, hπ, h]
  have hpair : ∀ l₀, (σi (F.lp l₀) = F.lp (π l₀) ∧ σi (F.lq l₀) = F.lq (π l₀)) ∨
      (σi (F.lp l₀) = F.lq (π l₀) ∧ σi (F.lq l₀) = F.lp (π l₀)) := by
    intro l₀
    apply piece_decomposition_unique hline (F.piece (π l₀))
    · rw [hsym.restrict _ 1 (by rw [(F.piece l₀).1, one_smul]), one_smul]
    · rw [hsym.restrict _ 1 (by rw [(F.piece l₀).2.1, one_smul]), one_smul]
    · rw [← hsym.root_add _ _ _ (F.piece l₀).2.2.2, ← hπ]
  let e : Equiv.Perm (Fin F.r) := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hπinj)
  have he : ∀ l₀, e l₀ = π l₀ := fun _ => rfl
  -- the transported triples, indexed by the source piece
  let W : Fin F.r → rationalPoints G := fun l₀ => z l₀ * (x l₀ * y l₀ * (x l₀)⁻¹ * (y l₀)⁻¹)
  let x'' : Fin F.r → rationalPoints G := fun l₀ =>
    if σi (F.lp l₀) = F.lp (π l₀) then s (x l₀) else s (y l₀)
  let z'' : Fin F.r → rationalPoints G := fun l₀ =>
    if σi (F.lp l₀) = F.lp (π l₀) then s (z l₀) else s (W l₀)
  let y'' : Fin F.r → rationalPoints G := fun l₀ =>
    if σi (F.lp l₀) = F.lp (π l₀) then s (y l₀) else s (x l₀)
  have hreo : ∀ l₀, W l₀ ∈ rootGroupPoints j (P.root (F.lm l₀)) ∧
      x l₀ * z l₀ * y l₀ = y l₀ * W l₀ * x l₀ := fun l₀ =>
    piece_reorder j hT hP hline (F.piece l₀).1 (F.piece l₀).2.1 (F.piece l₀).2.2.1
      (F.piece l₀).2.2.2 hE (hx l₀) (hz l₀) (hy l₀)
  have hmemx : ∀ l₀, x'' l₀ ∈ rootGroupPoints j (P.root (F.lq (π l₀))) := by
    intro l₀
    simp only [x'']
    split_ifs with hsw
    · have h := hsym.mem _ _ (hx l₀)
      rcases hpair l₀ with ⟨_, hq'⟩ | ⟨hp', _⟩
      · rwa [hq'] at h
      · exact absurd hsw (by rw [hp']; exact fun h' => (F.piece (π l₀)).2.2.1 h'.symm)
    · have h := hsym.mem _ _ (hy l₀)
      rcases hpair l₀ with ⟨hp', _⟩ | ⟨hp', _⟩
      · exact absurd hp' hsw
      · rwa [hp'] at h
  have hmemz : ∀ l₀, z'' l₀ ∈ rootGroupPoints j (P.root (F.lm (π l₀))) := by
    intro l₀
    simp only [z'']
    split_ifs
    · have h := hsym.mem _ _ (hz l₀); rwa [hπ] at h
    · have h := hsym.mem _ _ (hreo l₀).1; rwa [hπ] at h
  have hmemy : ∀ l₀, y'' l₀ ∈ rootGroupPoints j (P.root (F.lp (π l₀))) := by
    intro l₀
    simp only [y'']
    split_ifs with hsw
    · have h := hsym.mem _ _ (hy l₀); rwa [hsw] at h
    · have h := hsym.mem _ _ (hx l₀)
      rcases hpair l₀ with ⟨hp', _⟩ | ⟨_, hq'⟩
      · exact absurd hp' hsw
      · rwa [hq'] at h
  have htriple : ∀ l₀, s (x l₀ * z l₀ * y l₀) = x'' l₀ * z'' l₀ * y'' l₀ := by
    intro l₀
    simp only [x'', z'', y'']
    split_ifs
    · simp only [map_mul]
    · rw [(hreo l₀).2]; simp only [map_mul]
  -- reindexed triples on the target pieces
  let x' : Fin F.r → rationalPoints G := fun l₁ => x'' (e.symm l₁)
  let z' : Fin F.r → rationalPoints G := fun l₁ => z'' (e.symm l₁)
  let y' : Fin F.r → rationalPoints G := fun l₁ => y'' (e.symm l₁)
  have hπe : ∀ l₁, π (e.symm l₁) = l₁ := fun l₁ => by rw [← he, e.apply_symm_apply]
  have hx' : ∀ l₁, x' l₁ ∈ rootGroupPoints j (P.root (F.lq l₁)) := fun l₁ => by
    have := hmemx (e.symm l₁); rwa [hπe] at this
  have hz' : ∀ l₁, z' l₁ ∈ rootGroupPoints j (P.root (F.lm l₁)) := fun l₁ => by
    have := hmemz (e.symm l₁); rwa [hπe] at this
  have hy' : ∀ l₁, y' l₁ ∈ rootGroupPoints j (P.root (F.lp l₁)) := fun l₁ => by
    have := hmemy (e.symm l₁); rwa [hπe] at this
  -- the image of the product
  have hcommG : ∀ l₁ l₂, l₁ ≠ l₂ → Commute (x' l₁ * z' l₁ * y' l₁) (x' l₂ * z' l₂ * y' l₂) := by
    intro l₁ l₂ hl
    have hmem : ∀ l₀, x' l₀ * z' l₀ * y' l₀ ∈ pieceGroup j P (F.lp l₀) (F.lq l₀) (F.lm l₀) :=
      fun l₀ => Subgroup.mul_mem _ (Subgroup.mul_mem _
        (mem_pieceGroup_of_mem j (by simp [pieceRoots]) (hx' l₀))
        (mem_pieceGroup_of_mem j (by simp [pieceRoots]) (hz' l₀)))
        (mem_pieceGroup_of_mem j (by simp [pieceRoots]) (hy' l₀))
    exact commute_of_mem_pieceGroup j
      (pieces_commute j hT hP hline (F.piece l₁) (F.piece l₂) (F.disjoint l₁ l₂ hl))
      (hmem l₁) (hmem l₂)
  have himage : s (F.tripleProd x z y) = F.tripleProd x' z' y' := by
    unfold PieceFamily.tripleProd
    rw [map_list_prod, List.map_ofFn]
    have h1 : (List.ofFn (s ∘ fun l₀ => x l₀ * z l₀ * y l₀)) =
        List.ofFn ((fun l₁ => x' l₁ * z' l₁ * y' l₁) ∘ e) := by
      apply List.ofFn_inj.mpr
      funext l₀
      simp only [Function.comp_apply, htriple, x', z', y', Equiv.symm_apply_apply]
    rw [h1]
    apply List.Perm.prod_eq'
    · exact Equiv.Perm.ofFn_comp_perm e _
    · rw [List.pairwise_ofFn]
      intro l₁ l₂ hl
      exact hcommG _ _ (fun h => (ne_of_lt hl) (e.injective h))
  have heq := (himage.symm.trans hfix).symm
  obtain ⟨hxx, hzz, hyy⟩ := F.triples_eq_of_tripleProd_eq j hS hT hE ha0 hinj hrange hx hz hy
    hx' hz' hy' hg heq
  -- conclusion for `l`
  have hπl : π l = l' := hπeq l l' hll'
  have hel : e.symm l' = l := by rw [← hπl, ← he, e.symm_apply_apply]
  have hxl : x l' = x'' l := by rw [hxx]; simp only [x', hel]
  have hzl : z l' = z'' l := by rw [hzz]; simp only [z', hel]
  have hyl : y l' = y'' l := by rw [hyy]; simp only [y', hel]
  rcases hpair l with ⟨hp', hq'⟩ | ⟨hp', hq'⟩
  · left
    rw [hπl] at hp' hq'
    refine ⟨hp', hq', ?_, ?_, ?_⟩
    · rw [hxl]; simp only [x'', hπl, hp', ite_true]
    · rw [hzl]; simp only [z'', hπl, hp', ite_true]
    · rw [hyl]; simp only [y'', hπl, hp', ite_true]
  · right
    rw [hπl] at hp' hq'
    have hne : ¬ σi (F.lp l) = F.lp l' := by
      rw [hp']; exact fun h' => (F.piece l').2.2.1 h'.symm
    refine ⟨hp', hq', ?_, ?_, ?_⟩
    · rw [hxl]; simp only [x'', hπl, hne, ite_false]
    · rw [hyl]; simp only [y'', hπl, hne, ite_false]
    · rw [hzl]; simp only [z'', hπl, hne, ite_false, W]

include hT hP hE hline in
/-- **Symmetries exchanging the two roots of a piece.** If a piece symmetry fixing
`∏ₗ x_l z_l y_l` carries `lp l` to `lq l`, it fixes `lm l` and `s y_l = x_l`, `s x_l = y_l`,
`s (z_l [x_l, y_l]) = z_l`. -/
theorem PieceFamily.swap_of_symmetry (F : PieceFamily f P a) (hS : IsSplitTorus S.toGrp)
    (ha0 : a ≠ 0) (hinj : Function.Injective F.enum)
    (hrange : Set.range F.enum = RelativeRoot.semigroupIndivisibleRoots j
      (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail a 1)))
    {s : rationalPoints G →* rationalPoints G} {σi : J → J}
    (hsym : IsPieceSymmetry j P f a s σi)
    {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l)))
    (hg : F.tripleProd x z y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a)
    (hfix : s (F.tripleProd x z y) = F.tripleProd x z y)
    {l : Fin F.r} (hsw : σi (F.lp l) = F.lq l) :
    σi (F.lm l) = F.lm l ∧ s (y l) = x l ∧ s (x l) = y l ∧
      s (z l * (x l * y l * (x l)⁻¹ * (y l)⁻¹)) = z l := by
  obtain ⟨l', hl'⟩ := F.cover_two _ (hsym.restrict _ 2 (by
    rw [(F.piece l).2.2.2, Preadditive.comp_add, (F.piece l).1, (F.piece l).2.1, two_zsmul]))
  rcases F.symmetry j hT hP hE hline hS ha0 hinj hrange hsym hx hz hy hg hfix hl' with
    ⟨hp, -⟩ | ⟨hp, -, h1, h2, h3⟩
  · exfalso
    rw [hsw] at hp
    by_cases hll : l = l'
    · subst hll
      exact (F.piece l).2.2.1 hp.symm
    · exact (F.disjoint l l' hll).2.1 hp.symm
  · rw [hsw] at hp
    have hll : l = l' := by
      by_contra hll
      exact (F.disjoint l l' hll).2.2.2 hp.symm
    subst hll
    exact ⟨hl', h1, h2, h3⟩

end Symmetry

section Main

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hjc : IsClosedSubgroup j) (hP : IsRootDatumOf j P)
  (hE : RelativeRoot.HasOppositeFactorPairs j)
  {f : S ⟶ T} {a : characterLattice S} (hline : RestrictsToMultipliableLine f P a)
  {ω : kˣ → ℝ} (D : KPApartmentData j ω) (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus j) (xa : D.Apartment)

include hT hjc hP hE hline hG hi xa in
/-- If a symmetry exchanging the two roots of a piece fixes the product, the piece has trivial
`p`- and `q`-coordinates as soon as its `m`-coordinate is trivial. -/
theorem PieceFamily.eq_one_of_swap (F : PieceFamily f P a)
    {s : rationalPoints G →* rationalPoints G} {σi : J → J}
    (hsym : IsPieceSymmetry j P f a s σi)
    {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) {l : Fin F.r}
    (h1 : s (y l) = x l) (h3 : s (z l * (x l * y l * (x l)⁻¹ * (y l)⁻¹)) = z l)
    (hz1 : z l = 1) : x l = 1 ∧ y l = 1 := by
  have hφ := xa.isValuation
  have hc : x l * y l * (x l)⁻¹ * (y l)⁻¹ = 1 := by
    apply hsym.injective
    rw [map_one]
    rw [hz1, one_mul] at h3
    exact h3
  have hpc := (F.piece l).swap
  have hxl : x l = 1 := by
    by_contra hx1
    have hy1 : y l ≠ 1 := fun hy1 => hx1 (by rw [← h1, hy1, map_one])
    have hv := piece_val_commutator j hT hjc hP hE hline hpc.1 hpc.2.1 hpc.2.2.1 hpc.2.2.2 D hG
      hi xa (hx l) hx1 (hy l)
    rw [hc, (hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) 1 (Subgroup.one_mem _)).mpr rfl]
      at hv
    have hyv : xa.val (P.root (F.lp l)) (y l) ≠ ⊤ := fun h =>
      hy1 ((hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) _ (hy l)).mp h)
    have hxv : xa.val (P.root (F.lq l)) (x l) ≠ ⊤ := fun h =>
      hx1 ((hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) _ (hx l)).mp h)
    exact WithTop.add_ne_top.mpr ⟨hyv, hxv⟩ hv.symm
  refine ⟨hxl, hsym.injective ?_⟩
  rw [h1, hxl, map_one]

include hT hjc hP hE hline hG hi in
/-- **Half-value bound.** If `φ_m(z_l) = κ`, `φ_q(x_l) = φ_p(y_l)` and
`φ_m(z_l [x_l, y_l]) = φ_m(z_l)`, then `φ_q(x_l) ≥ κ / 2`. -/
theorem PieceFamily.half_le (F : PieceFamily f P a)
    {x z y : Fin F.r → rationalPoints G}
    (hx : ∀ l, x l ∈ rootGroupPoints j (P.root (F.lq l)))
    (hz : ∀ l, z l ∈ rootGroupPoints j (P.root (F.lm l)))
    (hy : ∀ l, y l ∈ rootGroupPoints j (P.root (F.lp l))) {l : Fin F.r} {κ : ℝ}
    (hzκ : xa.val (P.root (F.lm l)) (z l) = κ)
    (hxy : xa.val (P.root (F.lq l)) (x l) = xa.val (P.root (F.lp l)) (y l))
    (hzc : xa.val (P.root (F.lm l)) (z l * (x l * y l * (x l)⁻¹ * (y l)⁻¹)) =
      xa.val (P.root (F.lm l)) (z l)) :
    ((κ / 2 : ℝ) : WithTop ℝ) ≤ xa.val (P.root (F.lq l)) (x l) := by
  have hφ := xa.isValuation
  by_cases hx1 : x l = 1
  · rw [hx1, (hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) 1 (Subgroup.one_mem _)).mpr rfl]
    exact le_top
  obtain ⟨t, ht⟩ : ∃ t : ℝ, xa.val (P.root (F.lq l)) (x l) = t := by
    have hne : xa.val (P.root (F.lq l)) (x l) ≠ ⊤ := fun h =>
      hx1 ((hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) _ (hx l)).mp h)
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨c, hc.symm⟩
  have hpc := (F.piece l).swap
  have hv := piece_val_commutator j hT hjc hP hE hline hpc.1 hpc.2.1 hpc.2.2.1 hpc.2.2.2 D hG
    hi xa (hx l) hx1 (hy l)
  rw [← hxy, ht, ← WithTop.coe_add] at hv
  rw [ht, WithTop.coe_le_coe]
  by_contra hlt
  push Not at hlt
  have hcm := piece_commutator_mem_pq j hT hE hP hline hpc.1 hpc.2.1 hpc.2.2.1 hpc.2.2.2 (hx l)
    (hy l)
  have hlt2 : xa.val (P.root (F.lm l)) (x l * y l * (x l)⁻¹ * (y l)⁻¹) <
      xa.val (P.root (F.lm l)) (z l) := by
    rw [hv, hzκ, WithTop.coe_lt_coe]
    linarith
  have h := hφ.apply_mul_eq_right_of_lt (root_mem_relativeRoots j hP _) (hz l) hcm hlt2
  rw [hzc, hzκ, hv, WithTop.coe_inj] at h
  linarith

include hT hjc hP hE hline hG hi in
/-- **The opposite-pair axiom from piece symmetries.** Let `a ≠ 0` restrict a pair of roots
`r₁, r₂` whose sum is a root, and let a family of piece symmetries `(s τ, σ τ)` preserve the
values of the point `xa` of a normalizer-stable apartment class and act transitively on the
roots over each integer multiple of `a`. If `g ≠ 1` in the restricted root group of `a` and
`g'` in that of `-a` are fixed by every `s τ`, and `g' g g''` normalizes `j` and
`groupHom f ≫ j` for some `g''` in the restricted root group of `-a`, then the restricted
values satisfy `ψ_{-a}(g') + ψ_a(g) = 0`. -/
theorem torusRestricted_opposite_of_pieceSymmetries (hS : IsSplitTorus S.toGrp)
    [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left] [P.IsReduced]
    [IsAddTorsionFree (characterLattice T)]
    (ha0 : a ≠ 0) (ha : ∀ n m : ℕ, n • a = m • a → n = m)
    {r₁ r₂ : J} (hr₁ : f ≫ P.root r₁ = a) (hr₂ : f ≫ P.root r₂ = a)
    (hr : P.root r₁ + P.root r₂ ∈ Set.range P.root)
    {Γ : Type*} (s : Γ → rationalPoints G →* rationalPoints G) (σi : Γ → J → J)
    (hsym : ∀ τ, IsPieceSymmetry j P f a (s τ) (σi τ))
    (hval : ∀ τ (i : J) (w : rationalPoints G),
      xa.val (P.root (σi τ i)) (s τ w) = xa.val (P.root i) w)
    (htrans : ∀ (i i' : J) (n : ℤ), f ≫ P.root i = n • a → f ≫ P.root i' = n • a →
      ∃ τ, σi τ i = i')
    {g g' g'' : rationalPoints G}
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) a) (hg1 : g ≠ 1)
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a))
    (hN : g' * g * g'' ∈ normalizerPoints j)
    (hN' : g' * g * g'' ∈ normalizerPoints (CommGroupScheme.groupHom f ≫ j))
    (hgfix : ∀ τ, s τ g = g) (hg'fix : ∀ τ, s τ g' = g') :
    torusRestrictedRootFunctionFamily hS hT hE xa.isValuation f (-a) g' +
      torusRestrictedRootFunctionFamily hS hT hE xa.isValuation f a g = 0 := by
  classical
  have hφ := xa.isValuation
  have hroot1 : ∀ τ (i : J), f ≫ P.root i = a → f ≫ P.root (σi τ i) = a := fun τ i hi => by
    rw [(hsym τ).restrict i 1 (by rw [hi, one_smul]), one_smul]
  -- the piece family
  have hpart : ∀ i : J, f ≫ P.root i = a →
      ∃ i', f ≫ P.root i' = a ∧ P.root i + P.root i' ∈ Set.range P.root := by
    intro i hi
    obtain ⟨τ, hτ⟩ := htrans r₁ i 1 (by rw [hr₁, one_smul]) (by rw [hi, one_smul])
    obtain ⟨m, hm⟩ := hr
    refine ⟨σi τ r₂, hroot1 τ r₂ hr₂, σi τ m, ?_⟩
    rw [(hsym τ).root_add _ _ _ hm, hτ]
  have hdec : ∀ i : J, f ≫ P.root i = (2 : ℤ) • a →
      ∃ i' i'', f ≫ P.root i' = a ∧ f ≫ P.root i'' = a ∧
        P.root i = P.root i' + P.root i'' := by
    intro i hi
    obtain ⟨m, hm⟩ := hr
    obtain ⟨τ, hτ⟩ := htrans m i 2 (by rw [hm, Preadditive.comp_add, hr₁, hr₂, two_zsmul]) hi
    refine ⟨σi τ r₁, σi τ r₂, hroot1 τ r₁ hr₁, hroot1 τ r₂ hr₂, ?_⟩
    rw [← hτ, (hsym τ).root_add _ _ _ hm]
  obtain ⟨F⟩ := PieceFamily.nonempty_of_partners hline hpart hdec
  have hinj := F.enum_injective ha
  have hrange := F.range_enum j hP hline ha
  have ha' : ∀ n m : ℕ, n • (-a) = m • (-a) → n = m := fun n m h =>
    ha n m (by simpa only [smul_neg, neg_inj] using h)
  have hinj' := F.neg.enum_injective ha'
  have hrange' := F.neg.range_enum j hP hline.neg ha'
  have hα : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    (mem_roots_comp_iff (T := T) (T' := S) hT hS f j a).mpr
      ⟨ha0, P.root r₁, root_mem_relativeRoots j hP r₁, hr₁⟩
  have hα' : -a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    (mem_roots_comp_iff (T := T) (T' := S) hT hS f j (-a)).mpr
      ⟨neg_ne_zero.mpr ha0, -P.root r₁,
        neg_mem_relativeRoots_of_isRootDatumOf j hP (root_mem_relativeRoots j hP r₁),
        by rw [Preadditive.comp_neg, hr₁]⟩
  -- the piece coordinates of `g`
  obtain ⟨X, Z, Y, hX, hZ, hY, hXZY⟩ := F.existsUnique_triples j hS hT hE ha0 hinj hrange hg
  subst hXZY
  have hm2 : ∀ l, f ≫ P.root (F.lm l) = (2 : ℤ) • a := fun l => by
    rw [(F.piece l).2.2.2, Preadditive.comp_add, (F.piece l).1, (F.piece l).2.1, two_zsmul]
  have hsw : ∀ l, ∃ τ, σi τ (F.lp l) = F.lq l ∧ σi τ (F.lm l) = F.lm l ∧ s τ (Y l) = X l ∧
      s τ (X l) = Y l ∧ s τ (Z l * (X l * Y l * (X l)⁻¹ * (Y l)⁻¹)) = Z l := by
    intro l
    obtain ⟨τ, hτ⟩ := htrans _ _ 1 (by rw [(F.piece l).1, one_smul])
      (by rw [(F.piece l).2.1, one_smul])
    exact ⟨τ, hτ, F.swap_of_symmetry j hT hP hE hline hS ha0 hinj hrange (hsym τ) hX hZ hY hg
      (hgfix τ) hτ⟩
  have hvals : ∀ l, xa.val (P.root (F.lq l)) (X l) = xa.val (P.root (F.lp l)) (Y l) ∧
      xa.val (P.root (F.lm l)) (Z l * (X l * Y l * (X l)⁻¹ * (Y l)⁻¹)) =
        xa.val (P.root (F.lm l)) (Z l) := by
    intro l
    obtain ⟨τ, hτ, hm, h1, -, h3⟩ := hsw l
    constructor
    · rw [← h1, ← hτ, hval]
    · rw [← hval τ (F.lm l) (Z l * (X l * Y l * (X l)⁻¹ * (Y l)⁻¹)), hm, h3]
  -- some `m`-coordinate is nontrivial
  have hex : ∃ l₀, Z l₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hg1
    have h1 : ∀ l, X l = 1 ∧ Y l = 1 := fun l => by
      obtain ⟨τ, -, -, h1, -, h3⟩ := hsw l
      exact F.eq_one_of_swap j hT hjc hP hE hline D hG hi xa (hsym τ) hX hY h1 h3 (hall l)
    unfold PieceFamily.tripleProd
    apply List.prod_eq_one
    intro w hw
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    simp only [(h1 l).1, (h1 l).2, hall l, mul_one]
  obtain ⟨l₀, hl₀⟩ := hex
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, xa.val (P.root (F.lm l₀)) (Z l₀) = κ := by
    have hne : xa.val (P.root (F.lm l₀)) (Z l₀) ≠ ⊤ := fun htop =>
      hl₀ ((hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) _ (hZ l₀)).mp htop)
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨c, hc.symm⟩
  -- all `m`-coordinates have the value `κ`
  have hzval : ∀ l, xa.val (P.root (F.lm l)) (Z l) = κ := by
    intro l
    obtain ⟨τ, hτ⟩ := htrans (F.lm l₀) (F.lm l) 2 (hm2 l₀) (hm2 l)
    rcases F.symmetry j hT hP hE hline hS ha0 hinj hrange (hsym τ) hX hZ hY hg (hgfix τ) hτ with
      ⟨-, -, -, h2, -⟩ | ⟨-, -, -, -, h3⟩
    · rw [← h2, ← hτ, hval, hκ]
    · rw [← h3, ← hτ, hval, (hvals l₀).2, hκ]
  have hZ1 : ∀ l, Z l ≠ 1 := fun l h => by
    have h' := hzval l
    rw [h, (hφ.eq_top_iff _ (root_mem_relativeRoots j hP _) 1 (Subgroup.one_mem _)).mpr rfl] at h'
    exact WithTop.top_ne_coe h'
  have hxbound : ∀ l, ((κ / 2 : ℝ) : WithTop ℝ) ≤ xa.val (P.root (F.lq l)) (X l) := fun l =>
    F.half_le j hT hjc hP hE hline D hG hi xa hX hZ hY (hzval l) (hvals l).1 (hvals l).2
  -- the value of `g`
  have hpos : torusRestrictedRootFunctionFamily hS hT hE hφ f a (F.tripleProd X Z Y) =
      ((κ / 2 : ℝ) : WithTop ℝ) :=
    F.tripleProd_value j hS hT hE hφ hα hinj hrange l₀.pos hX hZ hY (κ / 2)
      (fun l => by rw [hzval l]; congr 1; ring) hxbound
      (fun l => by rw [← (hvals l).1]; exact hxbound l)
  -- the piece coordinates of `g'`
  obtain ⟨E, Yv, Dv, hEm, hYv, hDv, hg'eq, hopp, hcomm⟩ :=
    opposite_coordinates j hT hjc hP hE hline hS D hG hi xa F ha0 hX hZ hY hZ1 hg hg1 hg' hg''
      hN hN'
  have hYval : ∀ l, xa.val (P.root (F.neg.lm l)) (Yv l) = ((-κ : ℝ) : WithTop ℝ) := fun l => by
    have h := hopp l
    rw [hzval l] at h
    exact withTop_eq_neg_of_add_coe_eq_zero h
  have hg'mem : F.neg.tripleProd E Yv Dv ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-a) := hg'eq ▸ hg'
  have hfix' : ∀ τ, s τ (F.neg.tripleProd E Yv Dv) = F.neg.tripleProd E Yv Dv := fun τ => by
    rw [← hg'eq]
    exact hg'fix τ
  have hEval : ∀ l, xa.val (P.root (F.neg.lq l)) (E l) =
      xa.val (P.root (F.neg.lp l)) (Dv l) := by
    intro l
    obtain ⟨τ, hτ⟩ := htrans (F.neg.lp l) (F.neg.lq l) (-1)
      (by rw [(F.neg.piece l).1, neg_smul, one_smul])
      (by rw [(F.neg.piece l).2.1, neg_smul, one_smul])
    obtain ⟨-, h1, -, -⟩ := F.neg.swap_of_symmetry j hT hP hE hline.neg hS (neg_ne_zero.mpr ha0)
      hinj' hrange' (hsym τ).neg hEm hYv hDv hg'mem (hfix' τ) hτ
    rw [← h1, ← hτ, hval]
  have hDbound : ∀ l, ((-(κ / 2) : ℝ) : WithTop ℝ) ≤ xa.val (P.root (F.neg.lp l)) (Dv l) := by
    intro l
    rw [hcomm l, hYval l]
    calc ((-(κ / 2) : ℝ) : WithTop ℝ) = ((κ / 2 : ℝ) : WithTop ℝ) + ((-κ : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]
          congr 1
          ring
      _ ≤ xa.val (P.root (F.lq l)) (X l) + ((-κ : ℝ) : WithTop ℝ) :=
          add_le_add (hxbound l) le_rfl
  have hneg : torusRestrictedRootFunctionFamily hS hT hE hφ f (-a) (F.neg.tripleProd E Yv Dv) =
      ((-(κ / 2) : ℝ) : WithTop ℝ) :=
    F.neg.tripleProd_value j hS hT hE hφ hα' hinj' hrange' l₀.pos hEm hYv hDv (-(κ / 2))
      (fun l => by rw [hYval l]; congr 1; ring)
      (fun l => by rw [hEval l]; exact hDbound l) hDbound
  rw [hg'eq, hneg, hpos, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]

end Main

end Langlands.Geometry.Building
