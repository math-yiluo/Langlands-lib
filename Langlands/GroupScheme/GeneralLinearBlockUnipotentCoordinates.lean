import Langlands.Group.GL.BlockUnipotent
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.GeneralLinearPointTopology

/-! # Coordinates on the actual two-block unipotent subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GeneralLinear

variable {a b n : ℕ} (h : a + b = n)

/-- The weight is one on the first block and zero on the second, with the same numbering
as the original `blockUnipotent`. Empty blocks are allowed. -/
def twoBlockWeight (k : Fin n) : ℤ :=
  Sum.elim (fun _ : Fin a => 1) (fun _ : Fin b => 0)
    ((finSumFinEquiv.trans (finCongr h)).symm k)

@[simp] theorem twoBlockWeight_inl (i : Fin a) :
    twoBlockWeight h ((finSumFinEquiv.trans (finCongr h)) (Sum.inl i)) = 1 := by
  simp [twoBlockWeight]

@[simp] theorem twoBlockWeight_inr (j : Fin b) :
    twoBlockWeight h ((finSumFinEquiv.trans (finCongr h)) (Sum.inr j)) = 0 := by
  simp [twoBlockWeight]

variable {R : Type*} [CommRing R]

/-- Read the upper right block in the original consecutive numbering. -/
def blockUnipotentCoordinates (g : GeneralLinear n R) : Matrix (Fin a) (Fin b) R :=
  fun i j => (g : Matrix (Fin n) (Fin n) R)
    ((finSumFinEquiv.trans (finCongr h)) (Sum.inl i))
    ((finSumFinEquiv.trans (finCongr h)) (Sum.inr j))

@[simp] theorem blockUnipotentCoordinates_blockUnipotent (X : Matrix (Fin a) (Fin b) R) :
    blockUnipotentCoordinates h (blockUnipotent h X) = X := by
  ext i j
  simp [blockUnipotentCoordinates, blockUnipotent_val, Matrix.reindex_apply]

theorem blockUnipotent_entry (X : Matrix (Fin a) (Fin b) R)
    (i j : Fin a ⊕ Fin b) :
    (blockUnipotent h X : Matrix (Fin n) (Fin n) R)
      ((finSumFinEquiv.trans (finCongr h)) i)
      ((finSumFinEquiv.trans (finCongr h)) j) =
        Matrix.fromBlocks 1 X 0 1 i j := by
  simp only [blockUnipotent_val, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]

theorem twoBlockIndex_one (i j : Fin a ⊕ Fin b) :
    (1 : Matrix (Fin n) (Fin n) R)
      ((finSumFinEquiv.trans (finCongr h)) i)
      ((finSumFinEquiv.trans (finCongr h)) j) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) i j := by
  simp only [Matrix.one_apply, (finSumFinEquiv.trans (finCongr h)).injective.eq_iff]

theorem blockUnipotent_mem (X : Matrix (Fin a) (Fin b) R) :
    blockUnipotent h X ∈ GroupScheme.GeneralLinear.blockUnipotentSubgroup R
      (twoBlockWeight h) := by
  intro k l hkl
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective k
  obtain ⟨l, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective l
  rw [blockUnipotent_entry, twoBlockIndex_one]
  cases k <;> cases l <;>
    simp only [twoBlockWeight_inl, twoBlockWeight_inr] at hkl <;>
    simp_all [Matrix.one_apply]

theorem blockUnipotent_coordinates_eq
    (g : GroupScheme.GeneralLinear.blockUnipotentSubgroup R (twoBlockWeight h)) :
    blockUnipotent h (blockUnipotentCoordinates h g.val) = g.val := by
  apply Units.ext
  ext k l
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective k
  obtain ⟨l, rfl⟩ := (finSumFinEquiv.trans (finCongr h)).surjective l
  cases k with
  | inl i =>
      cases l with
      | inl j =>
          have hg := g.property
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inl i))
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inl j))
            (by simp only [twoBlockWeight_inl]; omega)
          rw [twoBlockIndex_one] at hg
          rw [blockUnipotent_entry]
          simpa [Matrix.one_apply] using hg.symm
      | inr j =>
          simp [blockUnipotent_val, Matrix.reindex_apply, blockUnipotentCoordinates]
  | inr i =>
      cases l with
      | inl j =>
          have hg := g.property
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inr i))
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inl j))
            (by simp only [twoBlockWeight_inr, twoBlockWeight_inl]; omega)
          rw [twoBlockIndex_one] at hg
          rw [blockUnipotent_entry]
          simpa [Matrix.one_apply] using hg.symm
      | inr j =>
          have hg := g.property
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inr i))
            ((finSumFinEquiv.trans (finCongr h)) (Sum.inr j))
            (by simp only [twoBlockWeight_inr]; omega)
          rw [twoBlockIndex_one] at hg
          rw [blockUnipotent_entry]
          simpa [Matrix.one_apply] using hg.symm

/-- The additive matrix group, written multiplicatively, is the existing weight-block
unipotent subgroup. The forward map is the original block matrix. -/
def blockUnipotentEquiv :
    Multiplicative (Matrix (Fin a) (Fin b) R) ≃*
      GroupScheme.GeneralLinear.blockUnipotentSubgroup R (twoBlockWeight h) where
  toFun X := ⟨blockUnipotent h X.toAdd, blockUnipotent_mem h X.toAdd⟩
  invFun g := Multiplicative.ofAdd (blockUnipotentCoordinates h g.val)
  left_inv X := congrArg Multiplicative.ofAdd (blockUnipotentCoordinates_blockUnipotent h X.toAdd)
  right_inv g := Subtype.ext (blockUnipotent_coordinates_eq h g)
  map_mul' X Y := Subtype.ext (blockUnipotent_add h X.toAdd Y.toAdd)

@[simp] theorem blockUnipotentEquiv_coe
    (X : Multiplicative (Matrix (Fin a) (Fin b) R)) :
    (blockUnipotentEquiv h X : GeneralLinear n R) = blockUnipotent h X.toAdd := rfl

theorem blockUnipotentCoordinates_map {S : Type*} [CommRing S] (f : R →+* S)
    (g : GeneralLinear n R) :
    blockUnipotentCoordinates h (Matrix.GeneralLinearGroup.map f g) =
      (blockUnipotentCoordinates h g).map f := rfl

variable [TopologicalSpace R]

theorem continuous_blockUnipotentCoordinates :
    Continuous (blockUnipotentCoordinates (R := R) h) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply _).comp
    (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id _)

variable [IsTopologicalRing R]

/-- Both the block matrix map and its coordinate inverse are continuous for the inherited
matrix-units topology. -/
def blockUnipotentHomeomorph :
    Multiplicative (Matrix (Fin a) (Fin b) R) ≃ₜ*
      GroupScheme.GeneralLinear.blockUnipotentSubgroup R (twoBlockWeight h) where
  toMulEquiv := blockUnipotentEquiv h
  continuous_toFun := ((continuous_blockUnipotent h).comp continuous_id).subtype_mk _
  continuous_invFun := (continuous_blockUnipotentCoordinates h).comp continuous_subtype_val

end Langlands.GeneralLinear

namespace Langlands.GroupScheme.GeneralLinear

variable {a b n : ℕ} (h : a + b = n) (R : CommRingCat.{u}) (S : CommAlgCat.{u} R)

/-- On an actual affine test scheme, membership in the existing block subgroup functor
is equivalent to membership of the actual coefficient matrix. -/
theorem mem_blockUnipotent_affinePoints_iff (e : Fin n → ℤ)
    (x : (groupScheme (Fin n) R).affinePoints S) :
    x ∈ (blockUnipotent (Fin n) R e).carrier ((algSpec R).obj (op S)) ↔
      affinePointsEquiv (Fin n) R S x ∈ blockUnipotentSubgroup S e := by
  change pointsEquiv (Fin n) R _ x ∈ blockUnipotentSubgroup _ e ↔ _
  rw [pointsEquiv_eq_affinePointsEquiv]
  constructor
  · intro hx i j hij
    have hx' := hx i j hij
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    change (Scheme.ΓSpecIso (CommRingCat.of S)).inv
      (affinePointsEquiv (Fin n) R S x i j) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ((1 : Matrix (Fin n) (Fin n) S) i j)
    change (Scheme.ΓSpecIso (CommRingCat.of S)).inv
      (affinePointsEquiv (Fin n) R S x i j) =
        (1 : Matrix (Fin n) (Fin n) Γ(Spec (CommRingCat.of S), ⊤)) i j at hx'
    rw [hx']
    by_cases heq : i = j <;> simp [Matrix.one_apply, heq]
  · intro hx
    exact map_mem_blockUnipotentSubgroup e
      (Corepresented.affineSectionsIso S).inv.hom.toRingHom hx

open Langlands.GeneralLinear

/-- Actual coefficient points of the existing two-block subgroup functor. -/
abbrev twoBlockPoints :=
  (blockUnipotent (Fin n) R (twoBlockWeight h)).carrier ((algSpec R).obj (op S))

/-- Restrict the actual point comparison to the existing block subgroups. -/
def twoBlockMatrixEquiv :
    twoBlockPoints h R S ≃* blockUnipotentSubgroup S (twoBlockWeight h) where
  toFun x := ⟨affinePointsEquiv (Fin n) R S x.val,
    (mem_blockUnipotent_affinePoints_iff R S (twoBlockWeight h) x.val).mp x.property⟩
  invFun g := ⟨(affinePointsEquiv (Fin n) R S).symm g.val,
    (mem_blockUnipotent_affinePoints_iff R S (twoBlockWeight h) _).mpr
      (by simpa only [MulEquiv.apply_symm_apply] using g.property)⟩
  left_inv x := Subtype.ext ((affinePointsEquiv (Fin n) R S).symm_apply_apply x.val)
  right_inv g := Subtype.ext ((affinePointsEquiv (Fin n) R S).apply_symm_apply g.val)
  map_mul' x y := Subtype.ext ((affinePointsEquiv (Fin n) R S).map_mul x.val y.val)

/-- The actual subgroup points and the original additive block coordinates. -/
def twoBlockPointsEquiv :
    twoBlockPoints h R S ≃* Multiplicative (Matrix (Fin a) (Fin b) S) :=
  (twoBlockMatrixEquiv h R S).trans (blockUnipotentEquiv h).symm

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- The actual subgroup point topology is the original matrix-coordinate topology. -/
def twoBlockPointsHomeomorph :
    twoBlockPoints h R S ≃ₜ* Multiplicative (Matrix (Fin a) (Fin b) S) where
  toMulEquiv := twoBlockPointsEquiv h R S
  continuous_toFun :=
    (continuous_blockUnipotentCoordinates h).comp
      ((continuous_affinePointsEquiv (Fin n) R S).comp continuous_subtype_val)
  continuous_invFun :=
    ((continuous_affinePointsEquiv_symm (Fin n) R S).comp
      ((continuous_blockUnipotent h).comp continuous_id)).subtype_mk _

end Langlands.GroupScheme.GeneralLinear
