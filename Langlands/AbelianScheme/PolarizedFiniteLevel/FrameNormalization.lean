import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoLocus

/-! # Normalizing the evaluations of a projective frame -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

namespace FrameNormalization

variable {C : Type v} [Category.{w} C] [HasZeroMorphisms C] [HasFiniteProducts C]
    {I : Type} [Finite I] [DecidableEq I] {M : C} {L : I → C} (f : ∀ i, M ⟶ L i)

/-- Joint evaluation at all indices except `k`. -/
def omission (k : I) : M ⟶ ∏ᶜ fun j : {j : I // j ≠ k} => L j.val :=
  Pi.lift fun j => f j.val

omit [HasZeroMorphisms C] [DecidableEq I] in
@[reassoc (attr := simp)]
lemma omission_π (k : I) (j : {j : I // j ≠ k}) :
    omission f k ≫ Pi.π (fun j : {j : I // j ≠ k} => L j.val) j = f j.val :=
  Pi.lift_comp_π (fun j : {j : I // j ≠ k} => f j.val) j

variable [hf : ∀ k, IsIso (omission f k)]

/-- The section of `M` supported in the slot `i` of the product omitting `k`. -/
def slot (k : I) (i : {j : I // j ≠ k}) : L i.val ⟶ M :=
  Pi.ι (fun j : {j : I // j ≠ k} => L j.val) i ≫ inv (omission f k)

lemma slot_eval (k : I) (i : {j : I // j ≠ k}) (j : I) (hj : j ≠ k) :
    slot f k i ≫ f j =
      Pi.ι (fun j : {j : I // j ≠ k} => L j.val) i ≫
        Pi.π (fun j : {j : I // j ≠ k} => L j.val) ⟨j, hj⟩ := by
  rw [slot, Category.assoc, ← omission_π f k ⟨j, hj⟩, IsIso.inv_hom_id_assoc]

lemma slot_eval' (k : I) (i j : {j : I // j ≠ k}) :
    slot f k i ≫ f j.val =
      Pi.ι (fun j : {j : I // j ≠ k} => L j.val) i ≫
        Pi.π (fun j : {j : I // j ≠ k} => L j.val) j :=
  slot_eval f k i j.val j.property

omit [HasZeroMorphisms C] [DecidableEq I] in
include hf in
lemma hom_ext_omit (k : I) {T : C} {a b : T ⟶ M}
    (hh : ∀ j, j ≠ k → a ≫ f j = b ≫ f j) : a = b := by
  apply (cancel_mono (omission f k)).mp
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, omission_π]
  exact hh j.val j.property

/-- The evaluation at the omitted index `k` of the slot `i`: an isomorphism of lines. -/
def lastComponent (k : I) (i : {j : I // j ≠ k}) : L i.val ≅ L k where
  hom := slot f k i ≫ f k
  inv := slot f i.val ⟨k, Ne.symm i.property⟩ ≫ f i.val
  hom_inv_id := by
    have hh : (slot f k i ≫ f k) ≫ slot f i.val ⟨k, Ne.symm i.property⟩ = slot f k i := by
      apply hom_ext_omit f i.val
      intro j hj
      by_cases hjk : j = k
      · rw [hjk, Category.assoc, slot_eval f i.val ⟨k, Ne.symm i.property⟩ k
          (Ne.symm i.property), Pi.ι_π_eq_id, Category.comp_id]
      · rw [Category.assoc, slot_eval f i.val ⟨k, Ne.symm i.property⟩ j hj,
          Pi.ι_π_of_ne _ (fun e => hjk (congrArg Subtype.val e).symm), Limits.comp_zero,
          slot_eval f k i j hjk,
          Pi.ι_π_of_ne _ (fun e => hj (congrArg Subtype.val e).symm)]
    rw [← Category.assoc, hh]
    exact (slot_eval' f k i i).trans (Pi.ι_π_eq_id _ _)
  inv_hom_id := by
    have hh : (slot f i.val ⟨k, Ne.symm i.property⟩ ≫ f i.val) ≫ slot f k i =
        slot f i.val ⟨k, Ne.symm i.property⟩ := by
      apply hom_ext_omit f k
      intro j hj
      by_cases hji : j = i.val
      · rw [hji, Category.assoc, slot_eval' f k i i, Pi.ι_π_eq_id, Category.comp_id]
      · rw [Category.assoc, slot_eval f k i j hj,
          Pi.ι_π_of_ne _ (fun e => hji (congrArg Subtype.val e).symm), Limits.comp_zero,
          slot_eval f i.val ⟨k, Ne.symm i.property⟩ j hji,
          Pi.ι_π_of_ne _ (fun e => hj (congrArg Subtype.val e).symm)]
    rw [← Category.assoc, hh]
    exact (slot_eval f i.val ⟨k, Ne.symm i.property⟩ k (Ne.symm i.property)).trans
      (Pi.ι_π_eq_id _ _)

lemma ι_mapIso_hom (k : I) (c : ∀ i : {j : I // j ≠ k}, L k ≅ L i.val)
    (i : {j : I // j ≠ k}) :
    Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (Pi.mapIso c).hom =
      (c i).hom ≫ Pi.ι (fun j : {j : I // j ≠ k} => L j.val) i := by
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.mapIso_hom_π, Category.assoc]
  by_cases hij : i = j
  · subst hij
    rw [Pi.ι_π_eq_id_assoc, Pi.ι_π_eq_id, Category.comp_id]
  · rw [Pi.ι_π_of_ne_assoc _ hij, Pi.ι_π_of_ne _ hij, Limits.zero_comp, Limits.comp_zero]

/-- The frame normalized at the omitted index `k`: an isomorphism from the product of
copies of `L k` to `M` whose `i`-th inclusion evaluates to zero at every other
non-omitted index and to the identity at `k`. -/
def normalizedFrame (k : I) : (∏ᶜ fun _ : {j : I // j ≠ k} => L k) ≅ M :=
  Pi.mapIso (fun i => (lastComponent f k i).symm) ≪≫ (asIso (omission f k)).symm

lemma ι_normalizedFrame (k : I) (i : {j : I // j ≠ k}) :
    Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (normalizedFrame f k).hom =
      (lastComponent f k i).inv ≫ slot f k i := by
  rw [normalizedFrame, Iso.trans_hom, ← Category.assoc, ι_mapIso_hom, Category.assoc]
  rfl

lemma normalizedFrame_offDiag (k : I) (i j : {j : I // j ≠ k}) (hij : i ≠ j) :
    Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (normalizedFrame f k).hom ≫ f j.val = 0 := by
  rw [← Category.assoc, ι_normalizedFrame, Category.assoc, slot_eval', Pi.ι_π_of_ne _ hij,
    Limits.comp_zero]

lemma normalizedFrame_omitted (k : I) (i : {j : I // j ≠ k}) :
    Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (normalizedFrame f k).hom ≫ f k = 𝟙 (L k) := by
  rw [← Category.assoc, ι_normalizedFrame, Category.assoc]
  exact (lastComponent f k i).inv_hom_id

lemma normalizedFrame_diag (k : I) (i : {j : I // j ≠ k}) :
    Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (normalizedFrame f k).hom ≫ f i.val =
      (lastComponent f k i).inv := by
  rw [← Category.assoc, ι_normalizedFrame, Category.assoc, slot_eval', Pi.ι_π_eq_id,
    Category.comp_id]

lemma isIso_normalizedFrame_diag (k : I) (i : {j : I // j ≠ k}) :
    IsIso (Pi.ι (fun _ : {j : I // j ≠ k} => L k) i ≫ (normalizedFrame f k).hom ≫ f i.val) := by
  rw [normalizedFrame_diag]
  infer_instance

end FrameNormalization

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- A full frame locus makes every omission evaluation an isomorphism on the base. -/
theorem Datum.isIso_frameEvaluation_of_frameLocus_eq_top (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (hρ : a.frameLocus ρ = ⊤)
    (k : Fin (m + 2)) : IsIso (a.frameEvaluation ρ k) := by
  rw [isIso_iff_forall_mem_isoLocus]
  intro x
  have hx : x ∈ a.frameLocus ρ := by rw [hρ]; trivial
  rw [Datum.frameLocus, mem_sSup_isIso_restrict_iff] at hx
  obtain ⟨W, hxW, hW⟩ := hx
  exact hW k x hxW

/-- For a datum whose frame locus is the whole base, the cubic direct image is the
product of `m + 1` copies of the cubic line at the last entry of the frame, by an
isomorphism whose `i`-th inclusion has zero evaluation at every other non-last entry,
identity evaluation at the last entry and invertible evaluation at the entry `i`. -/
theorem Datum.exists_normalizedFrame (a : Datum P S g d n)
    (ρ : Fin (m + 2) → Fin (2 * g) → ZMod n) (hρ : a.frameLocus ρ = ⊤) :
    ∃ e : (∏ᶜ fun _ : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)} =>
        (Scheme.Modules.pullback (a.torsionPoint (ρ (Fin.last (m + 1))))).obj
          a.cubicBundle.obj) ≅ a.rigidificationModule,
      (∀ i j : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)}, i ≠ j →
        Pi.ι _ i ≫ e.hom ≫ a.torsionEvaluation (ρ j.val) = 0) ∧
      (∀ i : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)},
        Pi.ι _ i ≫ e.hom ≫ a.torsionEvaluation (ρ (Fin.last (m + 1))) = 𝟙 _) ∧
      (∀ i : {j : Fin (m + 2) // j ≠ Fin.last (m + 1)},
        IsIso (Pi.ι _ i ≫ e.hom ≫ a.torsionEvaluation (ρ i.val))) := by
  classical
  let f : ∀ i : Fin (m + 2), a.rigidificationModule ⟶
      (Scheme.Modules.pullback (a.torsionPoint (ρ i))).obj a.cubicBundle.obj :=
    fun i => a.torsionEvaluation (ρ i)
  have : ∀ k, IsIso (FrameNormalization.omission f k) := fun k =>
    a.isIso_frameEvaluation_of_frameLocus_eq_top ρ hρ k
  exact ⟨FrameNormalization.normalizedFrame f (Fin.last (m + 1)),
    fun i j hij => FrameNormalization.normalizedFrame_offDiag f _ i j hij,
    fun i => FrameNormalization.normalizedFrame_omitted f _ i, fun i => FrameNormalization.isIso_normalizedFrame_diag f _ i⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
