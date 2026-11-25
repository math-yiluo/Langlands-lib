/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-! # Removing the positive tail of a bounded projective complex

Source: Stacks Project, More on Algebra, Tag 066Q; the explicit tail-splitting
argument in lem-sc-strict-perfect-closed-pushforward-stalk-resolution, step 3.
(blueprint: lem-sc-bounded-projective-nonpositive-model).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Cycles in nonnegative degrees of a bounded-above projective complex are projective
when its positive homology vanishes. The descending split-epimorphism argument for
(blueprint: lem-sc-bounded-projective-nonpositive-model), source Stacks Tag 066Q. -/
private theorem projective_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    (L : CochainComplex C ℤ) (hproj : ∀ j : ℤ, Projective (L.X j))
    (hexact : ∀ j : ℤ, 0 < j → IsZero (L.homology j))
    (n : ℕ) (j : ℤ) (hj : 0 ≤ j)
    (hb : ∀ k : ℤ, j + n < k → IsZero (L.X k)) :
    Projective (L.cycles j) := by
  induction n generalizing j with
  | zero =>
    have hd : L.d j (j + 1) = 0 := (hb (j + 1) (by omega)).eq_of_tgt _ _
    have := hproj j
    exact (Retract.ofIso (L.iCyclesIso j (j + 1) (by simp) hd)).projective
  | succ n ih =>
    have : Projective (L.cycles (j + 1)) := ih (j + 1) (by omega)
      (fun k hk ↦ hb k (by omega))
    have hs : (L.sc' j (j + 1) (j + 2)).Exact :=
      (L.exactAt_iff' j (j + 1) (j + 2) (by simp) (by simp; omega)).mp
        ((L.exactAt_iff_isZero_homology (j + 1)).mpr (hexact (j + 1) (by omega)))
    have : Epi (L.sc' j (j + 1) (j + 2)).toCycles := hs.epi_toCycles
    let E := L.cyclesIsoSc' j (j + 1) (j + 2) (by simp) (by simp; omega)
    have he : Epi (L.toCycles j (j + 1) ≫ E.hom) := by
      rw [L.toCycles_cyclesIsoSc'_hom j (j + 1) (j + 2) (by simp) (by simp; omega)]
      infer_instance
    have : Epi (L.toCycles j (j + 1)) := by
      have : Epi ((L.toCycles j (j + 1) ≫ E.hom) ≫ E.inv) := inferInstance
      simpa only [Category.assoc, E.hom_inv_id, Category.comp_id] using this
    let f := L.toCycles j (j + 1)
    let s := Projective.factorThru (𝟙 (L.cycles (j + 1))) f
    have hsf : s ≫ f = 𝟙 _ := Projective.factorThru_comp _ _
    have hif : L.iCycles j ≫ f = 0 := by
      rw [← cancel_mono (L.iCycles (j + 1)), Category.assoc]
      simp [f]
    have hd : (𝟙 (L.X j) - f ≫ s) ≫ L.d j (j + 1) = 0 := by
      rw [← L.toCycles_i j (j + 1)]
      change (𝟙 (L.X j) - f ≫ s) ≫ (f ≫ L.iCycles (j + 1)) = 0
      rw [Preadditive.sub_comp, Category.id_comp]
      rw [Category.assoc, ← Category.assoc s f, hsf]
      simp
    let r := L.liftCycles (𝟙 (L.X j) - f ≫ s) (j + 1) (by simp) hd
    have hir : L.iCycles j ≫ r = 𝟙 _ := by
      rw [← cancel_mono (L.iCycles j), Category.assoc]
      dsimp only [r]
      rw [L.liftCycles_i]
      simp [Preadditive.comp_sub, ← Category.assoc, hif]
    have := hproj j
    exact (⟨L.iCycles j, r, hir⟩ : Retract (L.cycles j) (L.X j)).projective

/-- A bounded projective complex exact in positive degrees admits a bounded projective
model with zero positive terms, together with a quasi-isomorphism to the original complex.

Source: Stacks Project, More on Algebra, Tag 066Q; explicit tail splitting in
lem-sc-strict-perfect-closed-pushforward-stalk-resolution, step 3.
(blueprint: lem-sc-bounded-projective-nonpositive-model).

Proof. First show that the cycle object in degree j ≥ 0 is projective by downward
induction from an upper bound. At the upper end the outgoing differential is zero,
so cycles equal the term. For the inductive step, vanishing of homology in degree
j+1 makes L^j → Z^(j+1) epic. Split this map using projectivity of Z^(j+1).
The endomorphism 1-fs of L^j factors through Z^j and gives a retraction of its
inclusion; hence Z^j is projective as a retract of the projective term L^j.
Take the good truncation at zero. Its degree-zero term is Z^0, its negative terms
are those of L and its positive terms are zero, so all its terms are projective.
The lower bound min(a,0) works. The inclusion of this truncation into L is a
quasi-isomorphism because the positive homology of L vanishes. This realizes the same
successive split-epimorphism argument as positive-tail removal without constructing the
contractible summands.
It covers an empty support interval and the zero complex, uses only projectivity,
and chooses no degree-zero target module. -/
theorem boundedProjective_nonpositiveModel
    {C : Type u} [Category.{v} C] [Abelian C]
    (L : CochainComplex C ℤ)
    (hbound : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j))
    (hproj : ∀ j : ℤ, Projective (L.X j))
    (hexact : ∀ j : ℤ, 0 < j → IsZero (L.homology j)) :
    ∃ Q : CochainComplex C ℤ, ∃ a : ℤ,
      (∀ j : ℤ, j < a → IsZero (Q.X j)) ∧
      (∀ j : ℤ, Projective (Q.X j)) ∧
      (∀ j : ℤ, 0 < j → IsZero (Q.X j)) ∧
      ∃ ι : Q ⟶ L, QuasiIso ι := by
  obtain ⟨a, b, hb⟩ := hbound
  let emb := ComplexShape.embeddingUpIntLE 0
  let Q := L.truncLE emb
  have hz (j : ℤ) (hj : 0 < j) : IsZero (Q.X j) :=
    Q.isZero_X_of_isStrictlySupported emb j
      (fun n hn ↦ by simp only [emb, ComplexShape.embeddingUpIntLE_f] at hn; omega)
  have hc : Projective (L.cycles 0) :=
    projective_cycles L hproj hexact b.toNat 0 (by omega)
      (fun k hk ↦ hb k (Or.inr (by omega)))
  have hp (j : ℤ) : Projective (Q.X j) := by
    rcases lt_trichotomy j 0 with hj | rfl | hj
    · let n := (-j).toNat
      have hn : emb.f n = j := by
        simp only [emb, ComplexShape.embeddingUpIntLE_f, n]
        omega
      have hboundary : ¬ emb.BoundaryLE n := by
        rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
        dsimp [n]
        omega
      have := hproj j
      exact (Retract.ofIso (L.truncLEXIso emb hn hboundary)).projective
    · exact (Retract.ofIso (L.truncLEXIsoCycles emb (i := 0) (by simp [emb])
        (by simp [emb, ComplexShape.boundaryLE_embeddingUpIntLE_iff]))).projective
    · exact (hz j hj).projective
  have hlower (j : ℤ) (hj : j < min a 0) : IsZero (Q.X j) := by
    let n := (-j).toNat
    have hn : emb.f n = j := by
      simp only [emb, ComplexShape.embeddingUpIntLE_f, n]
      omega
    have hboundary : ¬ emb.BoundaryLE n := by
      rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
      dsimp [n]
      omega
    exact (hb j (Or.inl (by omega))).of_iso (L.truncLEXIso emb hn hboundary)
  have hsupport : L.IsSupported emb := by
    constructor
    intro j hj
    rw [L.exactAt_iff_isZero_homology]
    exact hexact j ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 j).mp hj)
  have hq : QuasiIso (L.ιTruncLE emb) :=
    (L.quasiIso_ιTruncLE_iff_isSupported emb).mpr hsupport
  exact ⟨Q, min a 0, hlower, hp, hz, L.ιTruncLE emb, hq⟩

end CochainComplex
