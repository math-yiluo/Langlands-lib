/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.FilteredComplexGradedHomology
import WeilConjectures.CategoryTheory.FilteredComplexPageHomology
import WeilConjectures.CategoryTheory.SecondFiltrationSignedFirstPage

/-! # Signed row identifications for the second-filtration spectral sequence

Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-second-filtration-row-cohomology).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A zero degreewise step has a zero graded quotient in the same degree. -/
private theorem gradedPiece_isZero_of_complexStep_eq_bot
    {C : Type*} [Category C] [Abelian C] {K : CochainComplex C ℤ}
    (L : DecreasingFiltration K) (p n : ℤ) (h : L.complexStep p n = ⊥) :
    IsZero ((L.gradedPiece p).X n) := by
  have hstep : IsZero ((L.step p : CochainComplex C ℤ).X n) := by
    apply IsZero.of_mono_eq_zero ((L.step p).arrow.f n)
    have hh : (imageSubobject ((L.step p).arrow.f n)).arrow = 0 := by
      rw [← DecreasingFiltration.complexStep, h]
      simp
    rw [← imageSubobject_arrow_comp ((L.step p).arrow.f n), hh]
    simp
  have hle : p ≤ p + 1 := by omega
  have : Epi ((L.complexQuotientπ p (p + 1) hle).f n) := by
    dsimp [DecreasingFiltration.complexQuotientπ]
    infer_instance
  exact IsZero.of_epi ((L.complexQuotientπ p (p + 1) hle).f n) hstep

/-- Row cohomology, including the differential, for the second-degree filtration.
The differential retains the totalization sign. No injectivity or augmentation
is assumed, and no convergence is claimed.
Source: Stacks Project, Tag 0130; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-second-filtration-row-cohomology).

Proof.
Build the spectral sequence of the filtration by the differential-object self-map
construction, retaining the page-zero and cycle/boundary identifications. The graded
complex at s is the row F(I.X s), extended by zero and placed in degrees s+r: the
component raising s disappears on taking the quotient. Thus page one is its cohomology.
To compute d₁, lift a row cocycle to L^s/L^(s+2). Its total differential has only
the component raising complex degree, with coefficient (-1)^r. The connecting map
is consequently (-1)^r times the map of row cohomology induced by I.d s (s+1).
The extended row is zero in negative resolution degrees, so its cohomology there
vanishes. This proves the negative-degree page-one clause. -/
theorem secondFiltration_row_cohomology
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p) :
    ∃ (E : CohomologicalSpectralSequence B 0)
      (e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q))
      (e₁ : ∀ (r : ℕ) (s : ℤ), (E.page 1).X (s, (r : ℤ)) ≅
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).homology r),
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
        (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      (∀ (p q t : ℤ) (ht : 1 ≤ t),
        ∃ hBZ : L.complexBoundaries p (p + q) t ≤ L.complexCycles p (p + q) t,
          Nonempty ((E.page t (le_trans (by decide : (0 : ℤ) ≤ 1) ht)).X (p, q) ≅
            cokernel (Subobject.ofLE _ _ hBZ))) ∧
      (∀ (r : ℕ) (s : ℤ),
        (E.page 1).d (s, (r : ℤ)) (s + 1, (r : ℤ)) ≫ (e₁ r (s + 1)).hom =
          (r : ℤ).negOnePow • ((e₁ r s).hom ≫ HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map (I.d s (s + 1))) r)) ∧
      (∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))) := by
  classical
  let K := (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
    (ComplexShape.up ℤ)
  let P : HomologicalComplex B (ComplexShape.up' (⟨0, 1⟩ : ℤ × ℤ)) :=
    { X := fun a ↦ (L.gradedPiece a.1).X (a.1 + a.2)
      d := fun a b ↦ if h : a.1 = b.1 then
        (L.gradedPiece a.1).d (a.1 + a.2) (a.1 + b.2) ≫
          eqToHom (by rw [h]) else 0
      shape := by
        rintro ⟨p, q⟩ ⟨p', q'⟩ h
        dsimp
        split_ifs with hp
        · subst p'
          simp only [eqToHom_refl, Category.comp_id]
          apply HomologicalComplex.shape
          intro hd
          apply h
          change (p, q) + (0, 1) = (p, q')
          change p + q + 1 = p + q' at hd
          ext <;> dsimp <;> omega
        · rfl
      d_comp_d' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩ ⟨p'', q''⟩ h h'
        change (p, q) + (0, 1) = (p', q') at h
        change (p', q') + (0, 1) = (p'', q'') at h'
        have hp : p = p' := by simpa using congrArg _root_.Prod.fst h
        have hp' : p' = p'' := by simpa using congrArg _root_.Prod.fst h'
        subst p'
        subst p''
        simp }
  let e₀ : ∀ p q : ℤ, P.X (p, q) ≅ (L.gradedPiece p).X (p + q) :=
    fun _ _ ↦ Iso.refl _
  have hd₀ : ∀ p q : ℤ, P.d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
      (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1)) := by
    intro p q
    simp [P, e₀]
  let D (r : ℤ) (hr : 1 ≤ r) : FilteredComplexPageDifferential K L r :=
    (filteredComplex_page_differential_exists_unique K L r hr).choose
  have h01 : ∀ a : ℤ × ℤ, Nonempty (P.homology a ≅ (D 1 (by omega)).page.X a) := by
    rintro ⟨p, q⟩
    obtain ⟨hBZ, ⟨eQ⟩⟩ := filteredComplex_graded_homology K L P e₀ hd₀ p q
    exact ⟨eQ⟩
  let E : CohomologicalSpectralSequence B 0 :=
    { page := fun r hr ↦ if h : r = 0 then h ▸ P else (D r (by omega)).page
      iso := by
        intro r r' a hrr' hr
        by_cases h : r = 0
        · subst r
          have h' : r' = 1 := by omega
          subst r'
          simpa using (h01 a).some
        · have h' : r' ≠ 0 := by omega
          have hr1 : 1 ≤ r := by omega
          have eH := (filteredComplex_page_homology K L r hr1 (D r hr1) a).some
          have eX : filteredComplexPageObject K L (r + 1) a ≅
              filteredComplexPageObject K L r' a :=
            eqToIso (congrArg (fun t ↦ filteredComplexPageObject K L t a) hrr')
          simpa [h, h', FilteredComplexPageDifferential.page] using eH ≪≫ eX }
  obtain ⟨e₁, hd₁⟩ := secondFiltration_signed_firstPage F I hbelow L hL (D 1 (by omega))
  refine ⟨E, e₀, e₁, ?_, ?_, ?_, ?_⟩
  · simpa [E] using hd₀
  · intro p q t ht
    refine ⟨filteredComplex_boundaries_le_cycles K L p (p + q) t, ?_⟩
    have ht0 : t ≠ 0 := by omega
    simpa [E, ht0, FilteredComplexPageDifferential.page, filteredComplexPageObject]
      using (show Nonempty ((D t ht).page.X (p, q) ≅
        filteredComplexPageObject K L t (p, q)) from ⟨Iso.refl _⟩)
  · simpa [E] using hd₁
  · intro p q hq
    have hstep : L.complexStep p (p + q) = ⊥ := by
      rw [hL]
      simp [HomologicalComplex₂.secondFiltration, Finset.Icc_eq_empty_of_lt (by omega :
        p + q < p)]
    have hz := gradedPiece_isZero_of_complexStep_eq_bot L p (p + q) hstep
    have hcycles : IsZero (L.complexCycles p (p + q) 1 : B) :=
      IsZero.of_mono (L.complexCycles p (p + q) 1).arrow hz
    have : Epi (filteredComplexPageπ K L 1 (p, q)) := by
      dsimp [filteredComplexPageπ]
      infer_instance
    have hpage : IsZero (filteredComplexPageObject K L 1 (p, q)) :=
      IsZero.of_epi (filteredComplexPageπ K L 1 (p, q)) hcycles
    simpa [E, FilteredComplexPageDifferential.page] using hpage

end CategoryTheory.Functor
