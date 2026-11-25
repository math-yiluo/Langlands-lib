/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Graded projections of termwise split filtrations

For a filtered cochain complex whose graded quotient projections split in each degree and
whose filtration is exhaustive from some index, each degree admits a projection onto the
`t`-th graded piece that restricts to the graded quotient map on `Fᵗ` and kills `Fᵖ` for
`p > t`. We also record the vanishing of graded pieces outside the bounds and the
monomorphism `grᵠ ⟶ K / F^{q+1}`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} (F : DecreasingFiltration K)

/-- A graded piece vanishes when the next filtration step is everything. -/
theorem isZero_gradedPiece_of_eq_top {p : ℤ} (h : F.F (p + 1) = ⊤) :
    IsZero (F.gradedPiece p) := by
  have hp : F.F p = ⊤ := top_le_iff.1 (h ▸ F.F_succ_le p)
  have : IsIso (F.F (p + 1)).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  have : IsIso (F.F p).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hp
  have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) := by
    rw [(IsIso.eq_comp_inv _).2 (Subobject.ofLE_arrow (F.F_succ_le p))]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- A graded piece vanishes when its filtration step is zero. -/
theorem isZero_gradedPiece_of_eq_bot {p : ℤ} (h : F.F p = ⊥) :
    IsZero (F.gradedPiece p) := by
  have hz : IsZero ((F.F p : CochainComplex C ℤ)) :=
    h ▸ (Subobject.botCoeIsoZero (B := K)).isZero_iff.2 (isZero_zero _)
  have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) := hz.epi _
  exact isZero_cokernel_of_epi _

/-- The map `grᵠ K = F^q / F^{q+1} ⟶ K / F^{q+1}` induced by the inclusion `F^q ⟶ K`. -/
def gradedPieceToQuotient (q : ℤ) : F.gradedPiece q ⟶ cokernel (F.F (q + 1)).arrow :=
  cokernel.desc _ ((F.F q).arrow ≫ cokernel.π _) (by
    rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition])

@[reassoc (attr := simp)]
theorem complexQuotientπ_gradedPieceToQuotient (q : ℤ) :
    F.complexQuotientπ q (q + 1) (by omega) ≫ F.gradedPieceToQuotient q =
      (F.F q).arrow ≫ cokernel.π _ :=
  cokernel.π_desc _ _ _

instance (q : ℤ) : Mono (F.gradedPieceToQuotient q) := by
  have hS : (ShortComplex.mk (Subobject.ofLE _ _ (F.F_succ_le q))
      ((F.F q).arrow ≫ cokernel.π (F.F (q + 1)).arrow)
      (by rw [← Category.assoc, Subobject.ofLE_arrow, cokernel.condition])).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    obtain ⟨A', π, hπ, y, hy⟩ :=
      (ShortComplex.exact_cokernel (F.F (q + 1)).arrow).exact_up_to_refinements
        (x ≫ (F.F q).arrow) (by simpa using hx)
    refine ⟨A', π, hπ, y, ?_⟩
    rw [← cancel_mono (F.F q).arrow]
    simpa using hy
  exact hS.mono_cokernelDesc

/-- Degreewise graded projections of a termwise split filtration exhaustive from `a`. -/
theorem exists_gradedProjection (a : ℤ) (hPa : F.F a = ⊤)
    (hSplit : ∀ p n : ℤ, IsSplitEpi ((F.complexQuotientπ p (p + 1) (by omega)).f n))
    (t i : ℤ) :
    ∃ s : K.X i ⟶ (F.gradedPiece t).X i,
      (F.F t).arrow.f i ≫ s = (F.complexQuotientπ t (t + 1) (by omega)).f i ∧
      ∀ p, t < p → (F.F p).arrow.f i ≫ s = 0 := by
  rcases lt_or_ge t a with hta | hta
  · have h1 : F.F (t + 1) = ⊤ := by
      rw [eq_top_iff, ← hPa]
      exact F.antitone (by omega)
    have hz : IsZero ((F.gradedPiece t).X i) :=
      (HomologicalComplex.eval C _ i).map_isZero (F.isZero_gradedPiece_of_eq_top h1)
    exact ⟨0, hz.eq_of_tgt _ _, fun _ _ => hz.eq_of_tgt _ _⟩
  have hR : ∃ R : K.X i ⟶ (F.F t : CochainComplex C ℤ).X i,
      (F.F t).arrow.f i ≫ R = 𝟙 _ := by
    induction t, hta using Int.leInduction with
    | base =>
      have : IsIso (F.F a).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hPa
      exact ⟨inv ((F.F a).arrow.f i), by simp⟩
    | succ t hat ih =>
      obtain ⟨R, hR⟩ := ih
      have hex := (ShortComplex.exact_cokernel (Subobject.ofLE _ _ (F.F_succ_le t))).map
        (HomologicalComplex.eval C _ i)
      have hmono : Mono ((Subobject.ofLE _ _ (F.F_succ_le t)).f i) :=
        inferInstanceAs (Mono ((HomologicalComplex.eval C _ i).map _))
      let σ := (hSplit t i).exists_splitEpi.some
      let sp := ShortComplex.Splitting.ofExactOfSection _ hex σ.section_ σ.id hmono
      let r : (F.F t : CochainComplex C ℤ).X i ⟶ (F.F (t + 1) : CochainComplex C ℤ).X i :=
        sp.r
      have hr : (Subobject.ofLE _ _ (F.F_succ_le t)).f i ≫ r = 𝟙 _ := sp.f_r
      refine ⟨R ≫ r, ?_⟩
      rw [← Subobject.ofLE_arrow (F.F_succ_le t), HomologicalComplex.comp_f, Category.assoc,
        ← Category.assoc _ R, hR, Category.id_comp, hr]
  obtain ⟨R, hR⟩ := hR
  let π : (F.F t : CochainComplex C ℤ).X i ⟶ (F.gradedPiece t).X i :=
    (F.complexQuotientπ t (t + 1) (by omega)).f i
  have hπ : (Subobject.ofLE _ _ (F.F_succ_le t)).f i ≫ π = 0 := by
    have h := HomologicalComplex.congr_hom
      (cokernel.condition (Subobject.ofLE _ _ (F.F_succ_le t))) i
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
    exact h
  refine ⟨R ≫ π, ?_, fun p hp => ?_⟩
  · rw [← Category.assoc, hR, Category.id_comp]
  · rw [← Subobject.ofLE_arrow (F.antitone (show t + 1 ≤ p by omega)),
      ← Subobject.ofLE_arrow (F.F_succ_le t), HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, Category.assoc, Category.assoc, ← Category.assoc _ R, hR,
      Category.id_comp, hπ, comp_zero]

/-- The projection `Fᵖ K ⟶ grᵖ K`: the quotient map `complexQuotientπ p (p + 1)`, with the
graded piece as its declared target. -/
def gradedπ (p : ℤ) : (F.F p : CochainComplex C ℤ) ⟶ F.gradedPiece p :=
  F.complexQuotientπ p (p + 1) (by omega)

instance (p : ℤ) : Epi (F.gradedπ p) := by
  unfold gradedπ complexQuotientπ
  exact @coequalizer.π_epi _ _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem gradedπ_gradedPieceToQuotient (q : ℤ) :
    F.gradedπ q ≫ F.gradedPieceToQuotient q = (F.F q).arrow ≫ cokernel.π _ :=
  F.complexQuotientπ_gradedPieceToQuotient q

end CategoryTheory.DecreasingFiltration
