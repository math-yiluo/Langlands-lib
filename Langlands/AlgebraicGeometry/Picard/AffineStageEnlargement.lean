import Langlands.AlgebraicGeometry.Picard.AffineIsomColimit
import Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_fg_restrictScalars_and_le_of_fg

/-! # Finite subalgebra stages above a chosen stage -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Regard a subalgebra containing `B` as an algebra over `B`, with the same carrier. -/
def subalgebraOver {B C : Subalgebra R A} (h : B ≤ C) : Subalgebra B A :=
  { C with algebraMap_mem' := fun b ↦ h b.property }

@[simp]
lemma mem_subalgebraOver {B C : Subalgebra R A} (h : B ≤ C) (x : A) :
    x ∈ subalgebraOver h ↔ x ∈ C :=
  Iff.rfl

@[simp]
lemma subalgebraOver_restrictScalars {B C : Subalgebra R A} (h : B ≤ C) :
    (subalgebraOver h).restrictScalars R = C :=
  SetLike.coe_injective rfl

@[simp]
lemma subalgebraOver_of_restrictScalars (B : Subalgebra R A) (C : Subalgebra B A) :
    subalgebraOver (B := B) (C := C.restrictScalars R)
      (fun x hx ↦ C.algebraMap_mem ⟨x, hx⟩) = C :=
  SetLike.coe_injective rfl

/-- Generators over `R` remain generators over a subalgebra already contained in `C`. -/
lemma subalgebraOver_fg {B C : Subalgebra R A} (h : B ≤ C) (hC : C.FG) :
    (subalgebraOver h).FG := by
  obtain ⟨s, hs⟩ := hC
  refine ⟨s, le_antisymm (Algebra.adjoin_le ?_) ?_⟩
  · intro x hx
    change x ∈ C
    rw [← hs]
    exact Algebra.subset_adjoin hx
  · change C ≤ (Algebra.adjoin B (↑s : Set A)).restrictScalars R
    rw [← hs]
    exact Algebra.adjoin_le Algebra.subset_adjoin

/-- The finite `R`-stages that contain a specified subalgebra. -/
def AffineAlgebraStageAbove (B : Subalgebra R A) :=
  {C : AffineAlgebraStage R A // B ≤ C.val}
  deriving PartialOrder

/-- Finite stages over a finite `B` are exactly finite `R`-stages containing `B`. -/
def affineAlgebraStageEnlargementOrderIso (B : Subalgebra R A) (hB : B.FG) :
    AffineAlgebraStage B A ≃o AffineAlgebraStageAbove B where
  toFun C :=
    let h := Subalgebra.fg_restrictScalars_and_le_of_fg B hB C.val C.property
    ⟨⟨C.val.restrictScalars R, h.1⟩, h.2⟩
  invFun C := ⟨subalgebraOver C.property, subalgebraOver_fg C.property C.val.property⟩
  left_inv C := by
    apply Subtype.ext
    exact SetLike.coe_injective rfl
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact SetLike.coe_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
lemma affineAlgebraStageEnlargementOrderIso_val
    (B : Subalgebra R A) (hB : B.FG) (C : AffineAlgebraStage B A) :
    ((affineAlgebraStageEnlargementOrderIso B hB C).val).val =
      C.val.restrictScalars R :=
  rfl

@[simp]
lemma affineAlgebraStageEnlargementOrderIso_symm_val
    (B : Subalgebra R A) (hB : B.FG) (C : AffineAlgebraStageAbove B) :
    ((affineAlgebraStageEnlargementOrderIso B hB).symm C).val =
      subalgebraOver C.property :=
  rfl

/-- Composing the two affine structure maps gives the original affine test. -/
def affineBaseTowerIso (B : Subalgebra R A) :
    (Over.map (affineBase R B).hom).obj (affineBase B A) ≅ affineBase R A :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B))
    rw [Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl)

end Langlands.AlgebraicGeometry.Picard
