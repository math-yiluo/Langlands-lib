/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.VerticalWindowDegreeIso
public import Mathlib.Algebra.Homology.Single

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Canonical single-window comparison, using the degree identification and zero
objects in all other degrees.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof steps 1 and 2.
Proof: lower and upper truncation force all terms except q to vanish. Use the
canonical degree-q isomorphism for the only nonzero component, and zero maps
elsewhere. The differential conditions and inverse equations follow degreewise.
(blueprint: lem-sp-vertical-window-component-iso). -/
noncomputable def verticalWindowComponentIso (q : ℕ) (K : CochainComplex C ℕ) :
    (verticalWindow (C := C) (q : ℤ) (q + 1)).obj K ≅
      (HomologicalComplex.single C (ComplexShape.up ℕ) q).obj (K.homology q) := by
  let W := (verticalWindow (C := C) (q : ℤ) (q + 1)).obj K
  have hz : ∀ i : ℕ, i ≠ q → IsZero (W.X i) := by
    intro i hi
    let E : CochainComplex C ℤ := K.extend ComplexShape.embeddingUpNat
    let T : CochainComplex C ℤ := CochainComplex.truncLE (CochainComplex.truncGE E (q : ℤ)) (q : ℤ)
    change IsZero ((CochainComplex.truncLE (CochainComplex.truncGE E (q : ℤ))
      ((q : ℤ) + 1 - 1)).X (i : ℤ))
    rw [add_sub_cancel_right]
    rcases lt_or_gt_of_ne hi with h | h
    · exact CochainComplex.isZero_of_isStrictlyGE T (q : ℤ) (i : ℤ) (by exact_mod_cast h)
    · exact CochainComplex.isZero_of_isStrictlyLE T (q : ℤ) (i : ℤ) (by exact_mod_cast h)
  let e := verticalWindowDegreeIso (C := C) q K
  exact
    { hom := HomologicalComplex.mkHomToSingle e.hom (fun i hi ↦
        (hz i (by change i + 1 = q at hi; omega)).eq_of_src _ _)
      inv := HomologicalComplex.mkHomFromSingle e.inv (fun i hi ↦
        (hz i (by change q + 1 = i at hi; omega)).eq_of_tgt _ _)
      hom_inv_id := by
        apply HomologicalComplex.Hom.ext
        funext i
        by_cases hi : i = q
        · subst i
          simp
        · exact (hz i hi).eq_of_src _ _
      inv_hom_id := by
        apply HomologicalComplex.Hom.ext
        funext i
        by_cases hi : i = q
        · subst i
          simp
        · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _ }


end HomologicalComplex₂
