import Langlands.Geometry.FormalGroup.CopyMorphisms
import Langlands.Geometry.FormalGroup.RationalEndAlgebra

/-! # Block matrices of rational formal endomorphisms -/

noncomputable section

namespace Langlands.FormalGroup.ModuleLaw.RationalHom

universe u v w

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]

section Sums

variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {I : Type*} (s : Finset I)

/-- Rational composition distributes over a finite sum on the right. -/
theorem comp_sum (g : RationalHom F N P) (f : I → RationalHom F M N) :
    comp g (∑ i ∈ s, f i) = ∑ i ∈ s, comp g (f i) :=
  map_sum (compLinear g) f s

/-- Rational composition distributes over a finite sum on the left. -/
theorem sum_comp (g : I → RationalHom F N P) (f : RationalHom F M N) :
    comp (∑ i ∈ s, g i) f = ∑ i ∈ s, comp (g i) f :=
  map_sum (compLinear.flip f) g s

end Sums

variable (M : ModuleLaw O R Unit) {I : Type} [Fintype I] [DecidableEq I]

/-- The rational projection from a finite power to its chosen factor. -/
def copyProjection (i : I) : RationalHom F (M.copies I) M := ofHom (Hom.copyProjection M i)

/-- The rational inclusion into a factor of a finite power. -/
def copyInclusion (i : I) : RationalHom F M (M.copies I) := ofHom (Hom.copyInclusion M i)

local notation "Q" => copyProjection (F := F) M
local notation "J" => copyInclusion (F := F) M
local notation "X" => M.copies I

@[simp]
theorem copyProjection_comp_copyInclusion (i j : I) :
    comp (Q i) (J j) = if i = j then id M else 0 := by
  rw [copyProjection, copyInclusion, ← ofHom_comp, Hom.copyProjection_comp_copyInclusion]
  split_ifs <;> simp only [ofHom_id, map_zero]

/-- The rational projections and inclusions sum to the product identity. -/
theorem sum_copyInclusion_comp_copyProjection : (∑ i : I, comp (J i) (Q i)) = id X := by
  simp only [copyProjection, copyInclusion, ← ofHom_comp, ← map_sum,
    Hom.sum_copyInclusion_comp_copyProjection, ofHom_id]

/-- The `(i,j)` block is projection to `i` after the map on the inclusion of `j`. -/
def copiesEntry (z : RationalHom F X X) (i j : I) : RationalHom F M M :=
  comp (Q i) (comp z (J j))

/-- Assemble a matrix of rational formal maps using the actual inclusions and projections. -/
def assembleCopiesMatrix (c : Matrix I I (RationalHom F M M)) : RationalHom F X X :=
  ∑ i, ∑ j, comp (J i) (comp (c i j) (Q j))

private theorem copiesEntry_block (z : RationalHom F M M) (i j k l : I) :
    copiesEntry M (comp (J k) (comp z (Q l))) i j = if k = i then if l = j then z else 0 else 0 := by
  unfold copiesEntry
  calc
    _ = comp (comp (Q i) (J k)) (comp z (comp (Q l) (J j))) := by simp only [comp_assoc]
    _ = _ := by
      rw [copyProjection_comp_copyInclusion, copyProjection_comp_copyInclusion]
      by_cases hik : k = i
      · subst k
        by_cases hlj : l = j <;> simp [hlj]
      · simp [hik, Ne.symm hik]

@[simp]
theorem copiesEntry_assembleCopiesMatrix (c : Matrix I I (RationalHom F M M)) (i j : I) :
    copiesEntry M (assembleCopiesMatrix M c) i j = c i j := by
  calc
    _ = ∑ k, ∑ l, copiesEntry M (comp (J k) (comp (c k l) (Q l))) i j := by
      simp only [assembleCopiesMatrix, copiesEntry, sum_comp, comp_sum]
    _ = _ := by
      simp only [copiesEntry_block]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · simp

@[simp]
theorem assembleCopiesMatrix_copiesEntry (z : RationalHom F X X) :
    assembleCopiesMatrix M (copiesEntry M z) = z := by
  calc
    _ = ∑ i, ∑ j, comp (comp (J i) (Q i)) (comp z (comp (J j) (Q j))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [copiesEntry, comp_assoc]
    _ = _ := by
      simp only [← comp_sum, ← sum_comp, sum_copyInclusion_comp_copyProjection M, comp_id, id_comp]

@[simp]
theorem copiesEntry_id (i j : I) : copiesEntry M (id X : RationalHom F X X) i j = if i = j then id M else 0 := by
  simp only [copiesEntry, id_comp, copyProjection_comp_copyInclusion]

/-- Composition in blocks is the usual matrix multiplication. -/
theorem copiesEntry_comp (f g : RationalHom F X X) (i j : I) :
    copiesEntry M (comp f g) i j = ∑ k, comp (copiesEntry M f i k) (copiesEntry M g k j) := by
  calc
    _ = comp (comp (Q i) f) (comp (id X) (comp g (J j))) := by simp only [copiesEntry, comp_assoc, id_comp]
    _ = _ := by
      rw [← sum_copyInclusion_comp_copyProjection M]
      simp only [sum_comp, comp_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [copiesEntry, comp_assoc]

/-- The rational endomorphism algebra of a finite power is the matrix algebra
of the actual rational endomorphisms of the line. -/
def copiesMatrixEquiv : RationalHom F X X ≃ₐ[F] Matrix I I (RationalHom F M M) :=
  AlgEquiv.ofLinearEquiv
    { toFun := copiesEntry M
      invFun := assembleCopiesMatrix M
      left_inv := assembleCopiesMatrix_copiesEntry M
      right_inv := fun c => Matrix.ext fun i j => copiesEntry_assembleCopiesMatrix M c i j
      map_add' := fun f g => by
        apply Matrix.ext
        intro i j
        change copiesEntry M (f + g) i j = copiesEntry M f i j + copiesEntry M g i j
        simp [copiesEntry]
      map_smul' := fun a f => by
        apply Matrix.ext
        intro i j
        change copiesEntry M (a • f) i j = a • copiesEntry M f i j
        simp [copiesEntry] }
    (by
      apply Matrix.ext
      intro i j
      change copiesEntry M (id X : RationalHom F X X) i j = (1 : Matrix I I (RationalHom F M M)) i j
      rw [copiesEntry_id, Matrix.one_apply]
      rfl)
    (fun f g => by
      apply Matrix.ext
      intro i j
      rw [Matrix.mul_apply]
      exact copiesEntry_comp M f g i j)

@[simp]
theorem copiesMatrixEquiv_apply (z : RationalHom F X X) (i j : I) :
    copiesMatrixEquiv M z i j = copiesEntry M z i j := rfl

end Langlands.FormalGroup.ModuleLaw.RationalHom
