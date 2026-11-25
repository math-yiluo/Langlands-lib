/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.FieldTheory.TensorProductDiagonal

/-!
# Spreading out over an algebraic field extension

Let `E/F` be an algebraic field extension. Then `Spec E` is the cofiltered limit of the schemes
`Spec L` over the finite subextensions `L`, and also of the schemes `Spec (E ⊗_L E)`, embedded
diagonally. Consequently a scheme of finite presentation over `E` descends to some finite
subextension (Stacks 01ZM), and an equality of morphisms over `Spec (E ⊗_L E)` which holds on the
diagonal holds over `Spec (E ⊗_{L'} E)` for some larger finite `L'`.

## Main statements

- `AlgebraicGeometry.exists_finiteSubext_isPullback`
- `AlgebraicGeometry.isLimitDiagonalSpecCone`
-/

@[expose] public section

universe u

open CategoryTheory Limits IntermediateField TensorProduct

namespace AlgebraicGeometry

variable (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/-- `Spec E` as a cone over the schemes `Spec L`, `L` a finite subextension of `E/F`. -/
noncomputable abbrev subextSpecCone : Cone ((subextDiagram F E).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (subextCocone F E).op

/-- `Spec E` is the limit of the schemes `Spec L` over the finite subextensions `L` of `E/F`. -/
noncomputable def isLimitSubextSpecCone : IsLimit (subextSpecCone F E) :=
  isLimitOfPreserves Scheme.Spec (isColimitSubextCocone (F := F) (E := E)).op

/-- `Spec E` as a cone over the schemes `Spec (E ⊗_L E)`, `L` a finite subextension of `E/F`,
through the diagonal. -/
noncomputable abbrev diagonalSpecCone : Cone ((diagonalDiagram F E).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (diagonalCocone F E).op

/-- `Spec E` is the limit of the schemes `Spec (E ⊗_L E)` over the finite subextensions `L` of
`E/F`, through the diagonal. -/
noncomputable def isLimitDiagonalSpecCone : IsLimit (diagonalSpecCone F E) :=
  isLimitOfPreserves Scheme.Spec (isColimitDiagonalCocone (F := F) (E := E)).op

variable {F E}

/-- **Schemes of finite presentation over an algebraic extension descend to a finite
subextension** (Stacks 01ZM). -/
theorem exists_finiteSubext_isPullback {X : Scheme.{u}} (g : X ⟶ Spec (.of E))
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (L : FiniteSubext F E) (Y : Scheme.{u}) (p : Y ⟶ Spec (.of L.1))
      (_ : LocallyOfFinitePresentation p) (_ : QuasiCompact p) (_ : QuasiSeparated p)
      (h : X ⟶ Y),
      IsPullback h g p (Spec.map (CommRingCat.ofHom (algebraMap L.1 E))) := by
  have : ∀ {i j : (FiniteSubext F E)ᵒᵖ} (f : i ⟶ j),
      IsAffineHom (((subextDiagram F E).op ⋙ Scheme.Spec).map f) := fun f ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have : ∀ i : (FiniteSubext F E)ᵒᵖ,
      CompactSpace (((subextDiagram F E).op ⋙ Scheme.Spec).obj i) := fun i ↦
    have : IsAffine (((subextDiagram F E).op ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  have : ∀ i : (FiniteSubext F E)ᵒᵖ,
      QuasiSeparatedSpace (((subextDiagram F E).op ⋙ Scheme.Spec).obj i) := fun i ↦
    have : IsAffine (((subextDiagram F E).op ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  obtain ⟨⟨L⟩, Y, p, h₁, h₂, h₃, h, hh⟩ := Scheme.exists_isPullback_of_finitePresentation
    (isLimitSubextSpecCone F E) (X := X) g
  exact ⟨L, Y, p, h₁, h₂, h₃, h, hh⟩

section Projections

set_option linter.unusedSectionVars false

variable (L : FiniteSubext F E)

/-- The first projection `Spec (E ⊗_L E) ⟶ Spec E`. -/
noncomputable abbrev tensorSpecPr₁ : Spec (.of (E ⊗[L.1] E)) ⟶ Spec (.of E) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The second projection `Spec (E ⊗_L E) ⟶ Spec E`. -/
noncomputable abbrev tensorSpecPr₂ : Spec (.of (E ⊗[L.1] E)) ⟶ Spec (.of E) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- `Spec (E ⊗_L E)` is the fibre product `Spec E ×_{Spec L} Spec E`. -/
lemma isPullback_tensorSpecPr :
    IsPullback (tensorSpecPr₁ L) (tensorSpecPr₂ L)
      (Spec.map (CommRingCat.ofHom (algebraMap L.1 E)))
      (Spec.map (CommRingCat.ofHom (algebraMap L.1 E))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct L.1 E E)

lemma diagonalSpecCone_π_comp_tensorSpecPr₁ :
    (diagonalSpecCone F E).π.app (.op L) ≫ tensorSpecPr₁ L = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of E))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  change (Algebra.TensorProduct.lmul' L.1 (S := E)) (x ⊗ₜ 1) = x
  simp

lemma diagonalSpecCone_π_comp_tensorSpecPr₂ :
    (diagonalSpecCone F E).π.app (.op L) ≫ tensorSpecPr₂ L = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of E))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  change (Algebra.TensorProduct.lmul' L.1 (S := E)) (1 ⊗ₜ x) = x
  simp

variable {L} {L' : FiniteSubext F E}

lemma map_comp_tensorSpecPr₁ (f : Opposite.op L' ⟶ .op L) :
    ((diagonalDiagram F E).op ⋙ Scheme.Spec).map f ≫ tensorSpecPr₁ L = tensorSpecPr₁ L' := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

lemma map_comp_tensorSpecPr₂ (f : Opposite.op L' ⟶ .op L) :
    ((diagonalDiagram F E).op ⋙ Scheme.Spec).map f ≫ tensorSpecPr₂ L = tensorSpecPr₂ L' := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end Projections

end AlgebraicGeometry
