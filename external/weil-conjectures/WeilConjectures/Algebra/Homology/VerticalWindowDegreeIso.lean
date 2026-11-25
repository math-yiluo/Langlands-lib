/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical identification of the surviving term of a single smart window.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof steps 1 and 2.
Proof: the upper boundary is the cycles of the lower truncation. Its incoming
term is zero, so cycles equal homology. The lower truncation projection induces
an isomorphism on this homology, and extension by zero preserves homology.
(blueprint: lem-sp-vertical-window-degree-iso). -/
noncomputable def verticalWindowDegreeIso (q : ℕ) (K : CochainComplex C ℕ) :
    ((verticalWindow (C := C) (q : ℤ) (q + 1)).obj K).X q ≅ K.homology q := by
  let E : CochainComplex C ℤ := K.extend ComplexShape.embeddingUpNat
  let T : CochainComplex C ℤ := CochainComplex.truncGE E (q : ℤ)
  have hπ : IsIso (HomologicalComplex.homologyMap (CochainComplex.πTruncGE E (q : ℤ)) (q : ℤ)) := by
    have h := HomologicalComplex.quasiIsoAt_πTruncGE E (ComplexShape.embeddingUpIntGE (q : ℤ))
      (j := 0) (j' := (q : ℤ)) (by simp)
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp h
  have hd : T.d (q - 1) q = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE T (q : ℤ) (q - 1) (by omega)).eq_of_src _ _
  change (CochainComplex.truncLE (CochainComplex.truncGE E (q : ℤ)) ((q : ℤ) + 1 - 1)).X (q : ℤ) ≅ _
  rw [add_sub_cancel_right]
  exact CochainComplex.truncLEXIsoCycles T (q : ℤ) ≪≫
    T.isoHomologyπ (q - 1) q (by simp) hd ≪≫
    (asIso (HomologicalComplex.homologyMap (CochainComplex.πTruncGE E (q : ℤ)) (q : ℤ))).symm ≪≫
    K.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)


end HomologicalComplex₂
