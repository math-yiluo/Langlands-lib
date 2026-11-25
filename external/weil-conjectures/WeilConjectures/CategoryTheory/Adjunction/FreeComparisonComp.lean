/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit

/-!
# The free comparison of a composite

For adjunctions `free₁ ⊣ forget₁`, `free₂ ⊣ forget₂`, `free₃ ⊣ forget₃` and isomorphisms
`c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁'`, `c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂'`, the free comparison of the
composite `L₁ ⋙ L₂` (for the pasted isomorphism `CategoryTheory.Adjunction.compForgetIso c₁ c₂`) is
the composite of the free comparisons
(`CategoryTheory.Adjunction.freeComparison_comp`); in particular it is an isomorphism when both
are.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category C₁'] [Category C₂'] [Category C₃']
  {free₁ : C₁' ⥤ C₁} {forget₁ : C₁ ⥤ C₁'} (adj₁ : free₁ ⊣ forget₁)
  {free₂ : C₂' ⥤ C₂} {forget₂ : C₂ ⥤ C₂'} (adj₂ : free₂ ⊣ forget₂)
  {free₃ : C₃' ⥤ C₃} {forget₃ : C₃ ⥤ C₃'} (adj₃ : free₃ ⊣ forget₃)
  {L₁ : C₁ ⥤ C₂} {L₁' : C₁' ⥤ C₂'} {L₂ : C₂ ⥤ C₃} {L₂' : C₂' ⥤ C₃'}

/-- The pasting of `c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁'` and `c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂'`:
`(L₁ ⋙ L₂) ⋙ forget₃ ≅ forget₁ ⋙ (L₁' ⋙ L₂')`. -/
noncomputable def compForgetIso (c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁')
    (c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂') :
    (L₁ ⋙ L₂) ⋙ forget₃ ≅ forget₁ ⋙ (L₁' ⋙ L₂') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ c₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight c₁ L₂' ≪≫ Functor.associator _ _ _

/-- The free comparison of a composite is the composite of the free comparisons. -/
theorem freeComparison_comp (c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁')
    (c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂') (M : C₁') :
    freeComparison adj₁ adj₃ (L₁ ⋙ L₂) (L₁' ⋙ L₂') (compForgetIso c₁ c₂) M =
      freeComparison adj₂ adj₃ L₂ L₂' c₂ (L₁'.obj M) ≫
        L₂.map (freeComparison adj₁ adj₂ L₁ L₁' c₁ M) := by
  have h := c₂.inv.naturality (freeComparison adj₁ adj₂ L₁ L₁' c₁ M)
  dsimp at h
  rw [freeComparison, Equiv.symm_apply_eq, homEquiv_naturality_right, freeComparison.eq_1 adj₂ adj₃]
  dsimp only [Functor.comp_obj]
  rw [Equiv.apply_symm_apply, Category.assoc, ← h, ← Category.assoc, ← L₂'.map_comp,
    ← homEquiv_unit, freeComparison, Equiv.apply_symm_apply]
  simp [compForgetIso]

/-- The free comparison of a composite is an isomorphism if both free comparisons are. -/
theorem isIso_freeComparison_comp (c₁ : L₁ ⋙ forget₂ ≅ forget₁ ⋙ L₁')
    (c₂ : L₂ ⋙ forget₃ ≅ forget₂ ⋙ L₂') (M : C₁')
    (h₁ : IsIso (freeComparison adj₁ adj₂ L₁ L₁' c₁ M))
    (h₂ : IsIso (freeComparison adj₂ adj₃ L₂ L₂' c₂ (L₁'.obj M))) :
    IsIso (freeComparison adj₁ adj₃ (L₁ ⋙ L₂) (L₁' ⋙ L₂') (compForgetIso c₁ c₂) M) := by
  rw [freeComparison_comp adj₁ adj₂ adj₃]
  infer_instance

/-- The free comparison is unchanged, up to precomposition with the image of the given
isomorphism, by replacing `L'` with an isomorphic functor: for `e : L' ≅ L''`,
`freeComparison (c ≪≫ forget₁ ◁ e) = free₂ (e⁻¹) ≫ freeComparison c`. -/
theorem freeComparison_trans_isoWhiskerLeft {L : C₁ ⥤ C₂} {L' L'' : C₁' ⥤ C₂'}
    (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') (e : L' ≅ L'') (M : C₁') :
    freeComparison adj₁ adj₂ L L'' (c ≪≫ Functor.isoWhiskerLeft forget₁ e) M =
      free₂.map (e.inv.app M) ≫ freeComparison adj₁ adj₂ L L' c M := by
  rw [freeComparison, freeComparison, ← homEquiv_naturality_left_symm, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    ← NatTrans.naturality_assoc]
  rfl

end CategoryTheory.Adjunction
