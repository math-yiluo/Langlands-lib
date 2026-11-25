/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex


public import WeilConjectures.CategoryTheory.FilteredCohomologyImage
import all WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation
import WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap

/-! # Normalized presentation of the cohomology image graded piece

Source: Stacks Project, Tag 012Q.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

/-- The image filtration graded piece is represented by the normalized cycle quotient.
Source: Stacks Project, Tag 012Q, final quotient calculation.
(blueprint: lem-sp-filtered-cohomology-image-normalized-quotient).
-/
theorem cohomologyImage_graded_normalized
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (L : DecreasingFiltration K) (p n : ℤ) :
  let A := L.complexStep p n
  let A' := L.complexStep (p + 1) n
  let Z := (Subobject.pullback (K.d n (n + 1))).obj ⊥
  let B := imageSubobject (K.d (n - 1) n)
  let q := (L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n
  let P := Subobject.pullback ((L.step p).arrow.f n)
  let Zbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ Z) ⊔ A'))
  let Bbar := (Subobject.«exists» q).obj (P.obj ((A ⊓ B) ⊔ A'))
  ∃ hBZ : Bbar ≤ Zbar,
    Nonempty ((L.homologyFiltration n).gradedPiece p ≅
      cokernel (Subobject.ofLE Bbar Zbar hBZ)) := by
  dsimp only
  have hBZ0 : imageSubobject (K.d (n - 1) n) ≤
      (Subobject.pullback (K.d n (n + 1))).obj ⊥ := by
    apply (Subobject.imageSubobject_le_iff _ _).2
    apply (Subobject.factors_pullback_obj_iff _ _ _).2
    apply (Subobject.bot_factors_iff_zero _).2
    exact K.d_comp_d _ _ _
  have hAB : L.complexStep p n ⊓ imageSubobject (K.d (n - 1) n) ≤
      L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥ :=
    inf_le_inf_left _ hBZ0
  have hsum : (L.complexStep p n ⊓ imageSubobject (K.d (n - 1) n)) ⊔
      L.complexStep (p + 1) n ≤
      (L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥) ⊔
        L.complexStep (p + 1) n := sup_le_sup_right hAB _
  have hP : (Subobject.pullback ((L.step p).arrow.f n)).obj
      ((L.complexStep p n ⊓ imageSubobject (K.d (n - 1) n)) ⊔ L.complexStep (p + 1) n) ≤
      (Subobject.pullback ((L.step p).arrow.f n)).obj
        ((L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥) ⊔
          L.complexStep (p + 1) n) :=
    (Subobject.pullback ((L.step p).arrow.f n)).monotone hsum
  have hbar :
      (Subobject.«exists» ((L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n)).obj
          ((Subobject.pullback ((L.step p).arrow.f n)).obj
            ((L.complexStep p n ⊓ imageSubobject (K.d (n - 1) n)) ⊔
              L.complexStep (p + 1) n)) ≤
      (Subobject.«exists» ((L.complexQuotientπ p (p + 1) (Int.le_add_one le_rfl)).f n)).obj
          ((Subobject.pullback ((L.step p).arrow.f n)).obj
            ((L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥) ⊔
              L.complexStep (p + 1) n)) := (Subobject.«exists» _).monotone hP
  let S := L.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj ⊥
  have hz : S.arrow ≫ K.d n (n + 1) = 0 := by
    apply (Subobject.bot_factors_iff_zero _).1
    apply (Subobject.factors_pullback_obj_iff _ _ _).1
    exact (Subobject.factors_iff _ _).2
      ⟨Subobject.ofLE S _ inf_le_right, Subobject.ofLE_arrow inf_le_right⟩
  let c := K.liftCycles S.arrow (n + 1) (by simp) hz
  obtain ⟨himage, hpreimage⟩ := L.cohomologyImage_cycle_map p n c
    (K.liftCycles_i S.arrow (n + 1) (by simp) hz)
  obtain ⟨e⟩ := image_quotient (c ≫ K.homologyπ n)
    ((L.homologyFiltration n).step p) ((L.homologyFiltration n).step (p + 1))
    ((L.homologyFiltration n).antitone_step (Int.le_add_one le_rfl)) himage
  have he : Nonempty ((L.homologyFiltration n).gradedPiece p ≅
      cokernel ((Subobject.pullback S.arrow).obj
        ((L.complexStep p n ⊓ imageSubobject (K.d (n - 1) n)) ⊔
          (L.complexStep (p + 1) n ⊓
            (Subobject.pullback (K.d n (n + 1))).obj ⊥))).arrow) := by
    rw [hpreimage] at e
    exact ⟨e⟩
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := L.normalizedStationaryQuotient_presentation p n hbar
  exact ⟨hbar, ⟨e ≪≫ e'.symm⟩⟩


end CategoryTheory.DecreasingFiltration
