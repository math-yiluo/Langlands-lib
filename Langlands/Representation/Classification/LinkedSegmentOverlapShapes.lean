import Langlands.Representation.Classification.LinkedSegmentSocleIdentityPiece

/-!
# Block shapes of two overlapping segments

For `Δ' = init ∪ term` and `U = Δ ∪ init`, the shapes `(deg Δ, deg Δ')` and
`(deg U, deg term)` of `GL_n`, their identity intersection refinements, and the
two homomorphisms from the refined Levis onto `GL(deg Δ) × GL(deg init) × GL(deg term)`.
-/

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory PadicField.TopologicalData

universe uF uV

section Indices

variable {n : ℕ}

theorem index_zero_val (B : BlockShape n) (h : 0 < B.length) (a : Fin (B.size ⟨0, h⟩)) :
    ((B.index ⟨0, h⟩ a : Fin n) : ℕ) = a := by
  rw [CuspidalSupport.LeviAdmissibility.index_val]
  simp

theorem index_one_val (B : BlockShape n) (h : 1 < B.length) {s : ℕ}
    (hs : B.size ⟨0, by omega⟩ = s) (a : Fin (B.size ⟨1, h⟩)) :
    ((B.index ⟨1, h⟩ a : Fin n) : ℕ) = s + a := by
  subst hs
  rw [CuspidalSupport.LeviAdmissibility.index_val]
  simp
  rfl

/-- A coordinate lies in the first block exactly when it is smaller than its size. -/
theorem blockIndex_val_eq_zero_iff (B : BlockShape n) (h : 0 < B.length) (a : Fin n) :
    (blockIndex B a : ℕ) = 0 ↔ (a : ℕ) < B.size ⟨0, h⟩ := by
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective a
  change ((blockIndex B (B.index j b)) : ℕ) = 0 ↔ ((B.index j b : Fin n) : ℕ) < _
  rw [blockIndex_index, CuspidalSupport.LeviAdmissibility.index_val]
  constructor
  · intro hj
    obtain rfl : j = ⟨0, h⟩ := Fin.ext hj
    simp
  · intro hlt
    by_contra hj
    have hpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    have hle : B.size (Fin.castLE j.2.le (⟨0, hpos⟩ : Fin j)) ≤
        ∑ k : Fin j, B.size (Fin.castLE j.2.le k) :=
      Finset.single_le_sum (f := fun k : Fin j => B.size (Fin.castLE j.2.le k))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0, hpos⟩ : Fin j))
    change B.size ⟨0, h⟩ ≤ _ at hle
    omega

theorem blockIndex_le_of_length_one (B : BlockShape n) (h : B.length = 1) (a b : Fin n) :
    blockIndex B a ≤ blockIndex B b := by
  rw [Fin.le_iff_val_le_val]
  have := (blockIndex B a).2
  omega

/-- In a two-block shape, the block order of two coordinates is decided by the
size of the first block. -/
theorem blockIndex_le_iff_of_length_two (B : BlockShape n) (h : B.length = 2) {s : ℕ}
    (hs : B.size ⟨0, by omega⟩ = s) (a b : Fin n) :
    blockIndex B a ≤ blockIndex B b ↔ (a : ℕ) < s ∨ s ≤ (b : ℕ) := by
  have ha := blockIndex_val_eq_zero_iff B (by omega) a
  have hb := blockIndex_val_eq_zero_iff B (by omega) b
  have ha2 := (blockIndex B a).2
  have hb2 := (blockIndex B b).2
  rw [hs] at ha hb
  rw [Fin.le_iff_val_le_val]
  omega

end Indices

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Two segments `Δ`, `Δ'` with `Δ'` split after its first `q` members into
`init` and `term`, and a segment `U` of degree `deg Δ + deg init`. -/
structure OverlapConfig (T : F.TopologicalData) (n : ℕ) where
  Δ : Segment.{uV, uF} T
  Δ' : Segment.{uV, uF} T
  U : Segment.{uV, uF} T
  q : ℕ
  hq : 0 < q
  hqm : q < Δ'.length
  hn : ∑ i, (![Δ, Δ'] i).degree = n
  hU : ∑ i, (![Δ, Δ'.initial q hq] i).degree = U.degree

namespace OverlapConfig

variable {T : F.TopologicalData} {n : ℕ} (O : OverlapConfig.{uF, uV} T n)

/-- The initial part `init` of `Δ'`. -/
abbrev init : Segment.{uV, uF} T := O.Δ'.initial O.q O.hq

/-- The terminal part `term` of `Δ'`. -/
abbrev term : Segment.{uV, uF} T := O.Δ'.terminal O.q O.hqm

theorem degree_U : O.U.degree = O.Δ.degree + O.init.degree := by
  have := O.hU
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this.symm

theorem degree_Δ' : O.Δ'.degree = O.init.degree + O.term.degree :=
  (O.Δ'.initial_degree_add_terminal_degree O.q O.hq O.hqm).symm

theorem degree_n : O.Δ.degree + O.Δ'.degree = n := by
  have := O.hn
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  omega

theorem tgt_sum : ∑ i, (![O.U, O.term] i).degree = n := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have := O.degree_U
  have := O.degree_Δ'
  have := O.degree_n
  omega

/-- The source shape `(deg Δ, deg Δ')`. -/
abbrev B : BlockShape n := T.segmentShape ![O.Δ, O.Δ'] O.hn

/-- The target shape `(deg U, deg term)`. -/
abbrev C : BlockShape n := T.segmentShape ![O.U, O.term] O.tgt_sum

/-- The shape `(deg Δ, deg init)` of `GL(deg U)`. -/
abbrev unionShape : BlockShape O.U.degree := T.segmentShape ![O.Δ, O.init] O.hU

/-- The identity refinement of the source shape: `Δ` stays whole, `Δ'` splits. -/
def S : BlockRefinement O.B :=
  Fin.cons (α := fun i => BlockShape (O.B.size i))
    (CuspidalSupport.LeviAdmissibility.oneBlock O.Δ.degree O.Δ.degree_pos)
    (Fin.cons (α := fun j : Fin 1 => BlockShape (O.B.size j.succ))
      (O.Δ'.socleSplitShape O.q O.hq O.hqm) finZeroElim)

/-- The identity refinement of the target shape: `U` splits, `term` stays whole. -/
def R : BlockRefinement O.C :=
  Fin.cons (α := fun i => BlockShape (O.C.size i)) O.unionShape
    (Fin.cons (α := fun j : Fin 1 => BlockShape (O.C.size j.succ))
      (CuspidalSupport.LeviAdmissibility.oneBlock O.term.degree O.term.degree_pos)
      finZeroElim)

/-- The identity intersection refinement of the source shape. -/
theorem hS : IsIntersectionRefinement (F := F.Carrier) O.B O.C 1 O.S := by
  refine standardIntersections_of_comparisons F.Carrier O.B O.C 1 O.S ?_
  rintro ⟨i, hi⟩ a b
  simp only [Equiv.Perm.one_apply]
  have hU := O.degree_U
  rw [blockIndex_le_iff_of_length_two O.C rfl (s := O.U.degree) rfl]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by
    change i < 2 at hi
    omega
  · have ha := index_zero_val O.B hi a
    have hb := index_zero_val O.B hi b
    have ha' : (a : ℕ) < O.Δ.degree := a.2
    have hb' : (b : ℕ) < O.Δ.degree := b.2
    have := blockIndex_le_of_length_one (O.S ⟨0, hi⟩) rfl a b
    constructor
    · intro
      omega
    · intro
      exact this
  · rw [blockIndex_le_iff_of_length_two (O.S ⟨1, hi⟩) rfl (s := O.init.degree) rfl]
    have ha := index_one_val O.B hi (s := O.Δ.degree) rfl a
    have hb := index_one_val O.B hi (s := O.Δ.degree) rfl b
    omega

/-- The identity intersection refinement of the target shape. -/
theorem hR : IsIntersectionRefinement (F := F.Carrier) O.C O.B 1⁻¹ O.R := by
  refine standardIntersections_of_comparisons F.Carrier O.C O.B 1⁻¹ O.R ?_
  rintro ⟨i, hi⟩ a b
  simp only [inv_one, Equiv.Perm.one_apply]
  have hU := O.degree_U
  rw [blockIndex_le_iff_of_length_two O.B rfl (s := O.Δ.degree) rfl]
  obtain rfl | rfl : i = 0 ∨ i = 1 := by
    change i < 2 at hi
    omega
  · rw [blockIndex_le_iff_of_length_two (O.R ⟨0, hi⟩) rfl (s := O.Δ.degree) rfl]
    have ha := index_zero_val O.C hi a
    have hb := index_zero_val O.C hi b
    omega
  · have ha := index_one_val O.C hi (s := O.U.degree) rfl a
    have hb := index_one_val O.C hi (s := O.U.degree) rfl b
    have := blockIndex_le_of_length_one (O.R ⟨1, hi⟩) rfl a b
    constructor
    · intro
      omega
    · intro
      exact this

/-- The common product `GL(deg Δ) × GL(deg init) × GL(deg term)` of the two
identity refined Levis. -/
abbrev P : Type uF :=
  GeneralLinear O.Δ.degree F.Carrier × GeneralLinear O.init.degree F.Carrier ×
    GeneralLinear O.term.degree F.Carrier

/-- The three blocks of the source refined Levi product. -/
def sourceCoords : (∀ i, (O.S i).Levi F.Carrier) →* O.P where
  toFun m := (m ⟨0, Nat.zero_lt_two⟩ ⟨0, Nat.zero_lt_one⟩,
    m ⟨1, Nat.one_lt_two⟩ ⟨0, Nat.zero_lt_two⟩, m ⟨1, Nat.one_lt_two⟩ ⟨1, Nat.one_lt_two⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The three blocks of the target refined Levi product. -/
def targetCoords : (∀ j, (O.R j).Levi F.Carrier) →* O.P where
  toFun m := (m ⟨0, Nat.zero_lt_two⟩ ⟨0, Nat.zero_lt_two⟩,
    m ⟨0, Nat.zero_lt_two⟩ ⟨1, Nat.one_lt_two⟩, m ⟨1, Nat.one_lt_two⟩ ⟨0, Nat.zero_lt_one⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The source refined Levi in the common product. -/
abbrev φB : refinedLevi F.Carrier O.B O.S →* O.P :=
  O.sourceCoords.comp (refinedLeviEquiv F.Carrier O.B O.S).symm.toMonoidHom

/-- The target refined Levi in the common product. -/
abbrev φC : refinedLevi F.Carrier O.C O.R →* O.P :=
  O.targetCoords.comp (refinedLeviEquiv F.Carrier O.C O.R).symm.toMonoidHom

theorem idx_Δ (a : Fin O.Δ.degree) :
    O.B.index ⟨0, Nat.zero_lt_two⟩ ((O.S ⟨0, Nat.zero_lt_two⟩).index ⟨0, Nat.zero_lt_one⟩ a) =
      O.C.index ⟨0, Nat.zero_lt_two⟩
        ((O.R ⟨0, Nat.zero_lt_two⟩).index ⟨0, Nat.zero_lt_two⟩ a) := by
  apply Fin.ext
  have h1 := index_zero_val O.B Nat.zero_lt_two
    ((O.S ⟨0, Nat.zero_lt_two⟩).index ⟨0, Nat.zero_lt_one⟩ a)
  have h2 := index_zero_val (O.S ⟨0, Nat.zero_lt_two⟩) Nat.zero_lt_one a
  have h3 := index_zero_val O.C Nat.zero_lt_two
    ((O.R ⟨0, Nat.zero_lt_two⟩).index ⟨0, Nat.zero_lt_two⟩ a)
  have h4 := index_zero_val (O.R ⟨0, Nat.zero_lt_two⟩) Nat.zero_lt_two a
  omega

theorem idx_init (a : Fin O.init.degree) :
    O.B.index ⟨1, Nat.one_lt_two⟩ ((O.S ⟨1, Nat.one_lt_two⟩).index ⟨0, Nat.zero_lt_two⟩ a) =
      O.C.index ⟨0, Nat.zero_lt_two⟩
        ((O.R ⟨0, Nat.zero_lt_two⟩).index ⟨1, Nat.one_lt_two⟩ a) := by
  apply Fin.ext
  have h1 := index_one_val O.B Nat.one_lt_two (s := O.Δ.degree) rfl
    ((O.S ⟨1, Nat.one_lt_two⟩).index ⟨0, Nat.zero_lt_two⟩ a)
  have h2 := index_zero_val (O.S ⟨1, Nat.one_lt_two⟩) Nat.zero_lt_two a
  have h3 := index_zero_val O.C Nat.zero_lt_two
    ((O.R ⟨0, Nat.zero_lt_two⟩).index ⟨1, Nat.one_lt_two⟩ a)
  have h4 := index_one_val (O.R ⟨0, Nat.zero_lt_two⟩) Nat.one_lt_two (s := O.Δ.degree) rfl a
  omega

theorem idx_term (a : Fin O.term.degree) :
    O.B.index ⟨1, Nat.one_lt_two⟩ ((O.S ⟨1, Nat.one_lt_two⟩).index ⟨1, Nat.one_lt_two⟩ a) =
      O.C.index ⟨1, Nat.one_lt_two⟩
        ((O.R ⟨1, Nat.one_lt_two⟩).index ⟨0, Nat.zero_lt_one⟩ a) := by
  apply Fin.ext
  have h1 := index_one_val O.B Nat.one_lt_two (s := O.Δ.degree) rfl
    ((O.S ⟨1, Nat.one_lt_two⟩).index ⟨1, Nat.one_lt_two⟩ a)
  have h2 := index_one_val (O.S ⟨1, Nat.one_lt_two⟩) Nat.one_lt_two (s := O.init.degree) rfl a
  have h3 := index_one_val O.C Nat.one_lt_two (s := O.U.degree) rfl
    ((O.R ⟨1, Nat.one_lt_two⟩).index ⟨0, Nat.zero_lt_one⟩ a)
  have h4 := index_zero_val (O.R ⟨1, Nat.one_lt_two⟩) Nat.zero_lt_one a
  have hU := O.degree_U
  omega

/-- Refined Levi elements with the same ambient matrix have the same coordinates
in the common product. -/
theorem coords_compat (x : refinedLevi F.Carrier O.B O.S) (y : refinedLevi F.Carrier O.C O.R)
    (h : O.B.leviEmbedding F.Carrier x.val = O.C.leviEmbedding F.Carrier y.val) :
    O.φB x = O.φC y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact Matrix.GeneralLinearGroup.ext fun a b =>
      refinedLevi_entry_eq h (O.idx_Δ a) (O.idx_Δ b)
  · exact Matrix.GeneralLinearGroup.ext fun a b =>
      refinedLevi_entry_eq h (O.idx_init a) (O.idx_init b)
  · exact Matrix.GeneralLinearGroup.ext fun a b =>
      refinedLevi_entry_eq h (O.idx_term a) (O.idx_term b)

end OverlapConfig

end Langlands.Classification.QuotientHom
