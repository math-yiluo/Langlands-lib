import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite related tuples of an étale equivalence relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u})

/-- An auxiliary recursive presentation of the scheme of `n + 1` related points,
with its coordinate morphisms. The new point is appended at the last index. -/
noncomputable def tuplePresentation :
    (n : ℕ) → Σ X : Scheme.{u}, (Fin (n + 1) → (X ⟶ E.U))
  | 0 => ⟨E.U, fun _ => 𝟙 E.U⟩
  | n + 1 =>
    ⟨pullback ((tuplePresentation n).2 0) E.s,
      Fin.lastCases (pullback.snd _ _ ≫ E.t)
        (fun i => pullback.fst _ _ ≫ (tuplePresentation n).2 i)⟩

/-- The scheme representing `n + 1` mutually related points of `E`. -/
noncomputable abbrev tupleScheme (n : ℕ) : Scheme.{u} :=
  (E.tuplePresentation n).1

/-- A coordinate morphism on the scheme of related tuples. -/
noncomputable abbrev tupleProjection (n : ℕ) (i : Fin (n + 1)) :
    E.tupleScheme n ⟶ E.U :=
  (E.tuplePresentation n).2 i

@[simp] lemma tupleProjection_zero (i : Fin 1) :
    E.tupleProjection 0 i = 𝟙 E.U := rfl

@[simp] lemma tupleProjection_castSucc (n : ℕ) (i : Fin (n + 1)) :
    E.tupleProjection (n + 1) i.castSucc =
      pullback.fst (E.tupleProjection n 0) E.s ≫ E.tupleProjection n i := by
  simp [tupleProjection, tuplePresentation]

@[simp] lemma tupleProjection_last (n : ℕ) :
    E.tupleProjection (n + 1) (Fin.last (n + 1)) =
      pullback.snd (E.tupleProjection n 0) E.s ≫ E.t := by
  simp [tupleProjection, tuplePresentation]

/-- Every coordinate of a tuple is related to its first coordinate. -/
lemma tupleProjection_related_first (n : ℕ) (i : Fin (n + 1)) :
    ∃ r : E.tupleScheme n ⟶ E.R,
      r ≫ E.t = E.tupleProjection n i ∧ r ≫ E.s = E.tupleProjection n 0 := by
  induction n with
  | zero =>
    change ∃ r : E.U ⟶ E.R, r ≫ E.t = 𝟙 E.U ∧ r ≫ E.s = 𝟙 E.U
    exact E.refl E.U (𝟙 E.U)
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · refine ⟨pullback.snd _ _, E.tupleProjection_last n |>.symm, ?_⟩
      rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
        E.tupleProjection_castSucc]
      exact pullback.condition.symm
    · obtain ⟨r, ht, hs⟩ := ih j
      refine ⟨pullback.fst _ _ ≫ r, ?_, ?_⟩
      · simp [Category.assoc, ht]
      · rw [Category.assoc, hs,
          show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl,
          E.tupleProjection_castSucc]

/-- Any two coordinate morphisms are related, on all test schemes. -/
lemma tupleProjection_related (n : ℕ) (i j : Fin (n + 1)) :
    ∃ r : E.tupleScheme n ⟶ E.R,
      r ≫ E.t = E.tupleProjection n i ∧ r ≫ E.s = E.tupleProjection n j := by
  obtain ⟨a, hat, has⟩ := E.tupleProjection_related_first n i
  obtain ⟨b, hbt, hbs⟩ := E.tupleProjection_related_first n j
  obtain ⟨b', hb't, hb's⟩ := E.symm _ b
  obtain ⟨c, hct, hcs⟩ := E.trans _ a b' (has.trans (hb't.trans hbs).symm)
  exact ⟨c, hct.trans hat, hcs.trans (hb's.trans hbt)⟩

/-- Morphisms to a related-tuple scheme are determined by their coordinates. -/
lemma tuple_hom_ext (n : ℕ) {T : Scheme.{u}} {a b : T ⟶ E.tupleScheme n}
    (h : ∀ i, a ≫ E.tupleProjection n i = b ≫ E.tupleProjection n i) : a = b := by
  induction n with
  | zero =>
    have hz := h 0
    change a ≫ 𝟙 (E.tupleScheme 0) = b ≫ 𝟙 (E.tupleScheme 0) at hz
    simpa only [Category.comp_id] using hz
  | succ n ih =>
    apply pullback.hom_ext
    · apply ih
      intro i
      simpa [Category.assoc] using h i.castSucc
    · apply E.hom_ext
      · simpa [Category.assoc] using h (Fin.last (n + 1))
      · simpa only [tupleProjection_castSucc, Category.assoc, pullback.condition] using
          h ((0 : Fin (n + 1)).castSucc)

/-- Existence of a morphism realizing any family of pairwise related
`T`-valued points. -/
lemma exists_tuple_lift (n : ℕ) {T : Scheme.{u}}
    (a : Fin (n + 1) → (T ⟶ E.U))
    (h : ∀ i j, ∃ r : T ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j) :
    ∃ f : T ⟶ E.tupleScheme n, ∀ i, f ≫ E.tupleProjection n i = a i := by
  induction n with
  | zero =>
    refine ⟨a 0, fun i => ?_⟩
    change a 0 ≫ 𝟙 E.U = a i
    rw [Category.comp_id, Fin.eq_zero i]
  | succ n ih =>
    obtain ⟨f, hf⟩ := ih (fun i => a i.castSucc) (fun i j => h i.castSucc j.castSucc)
    obtain ⟨r, hrt, hrs⟩ := h (Fin.last (n + 1)) ((0 : Fin (n + 1)).castSucc)
    refine ⟨pullback.lift f r ((hf 0).trans hrs.symm), ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hrt]
    · simp [hf]

instance tupleScheme_isAffine [IsAffine E.U] [IsAffine E.R] (n : ℕ) :
    IsAffine (E.tupleScheme n) := by
  induction n with
  | zero => exact inferInstanceAs (IsAffine E.U)
  | succ n ih =>
    let := ih
    change IsAffine (pullback (E.tupleProjection n 0) E.s)
    infer_instance

/-- Each coordinate projection is étale. -/
instance tupleProjection_etale (n : ℕ) (i : Fin (n + 1)) :
    Etale (E.tupleProjection n i) := by
  let := E.etale_s
  let := E.etale_t
  induction n with
  | zero => exact inferInstanceAs (Etale (𝟙 E.U))
  | succ n ih =>
    let := ih 0
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [E.tupleProjection_last]
      infer_instance
    · let := ih j
      rw [E.tupleProjection_castSucc]
      infer_instance

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
