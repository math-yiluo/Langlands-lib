import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.GeneralLinear
import Langlands.GroupScheme.Multiplicative
import Langlands.Group.GL.Blocks
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Diagonal cocharacters and weight-block subgroups of `GL_n`

For a weight vector `e : n → ℤ`, this module defines the diagonal cocharacter
`t ↦ diag(t ^ e i)` of the general linear group scheme over `Spec R`, and the subgroup functors
of block upper triangular, block diagonal and block unipotent invertible matrices for the weight
blocks `{i | e i = c}`, ordered by decreasing weight. For the decreasing weights of an ordered
block shape `B : Langlands.GeneralLinear.BlockShape N`, these subgroups are the Library's
`B.parabolic`, `B.leviSubgroup` and `B.unipotentSubgroup`, and the block diagonal projection is
`B.leviProjection` followed by `B.leviEmbedding`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]

section Matrix

variable (A : Type*) [CommRing A] (e : n → ℤ)

/-- The diagonal matrix `diag(u ^ e i)` attached to a unit `u`. -/
def diagonalUnits : Aˣ →* GL n A :=
  (Units.map (Matrix.diagonalRingHom n A).toMonoidHom).comp
    (MulEquiv.piUnits.symm.toMonoidHom.comp (MonoidHom.pi fun i => zpowGroupHom (e i)))

theorem coe_diagonalUnits (t : Aˣ) :
    (diagonalUnits A e t : Matrix n n A) = Matrix.diagonal fun i => ((t ^ e i : Aˣ) : A) :=
  rfl

variable {A} in
/-- Diagonal matrices of units are compatible with ring homomorphisms. -/
theorem map_diagonalUnits {B : Type*} [CommRing B] (f : A →+* B) (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagonalUnits A e t) =
      diagonalUnits B e (Units.map f.toMonoidHom t) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, coe_diagonalUnits, Matrix.diagonal_apply]
  split_ifs
  · rw [← map_zpow, Units.coe_map]
    rfl
  · exact map_zero f

/-- Invertible matrices whose `(i, j)` entry vanishes whenever `e i < e j`. For weights listed
in decreasing order these are the block upper triangular matrices. The condition is Mathlib's
`BlockTriangular` for the order-reversed weights. -/
def blockParabolicSubgroup : Subgroup (GL n A) where
  carrier := {g | (g : Matrix n n A).BlockTriangular (OrderDual.toDual ∘ e)}
  one_mem' := Matrix.blockTriangular_one
  mul_mem' ha hb := ha.mul hb
  inv_mem' := by
    intro g hg
    let := g.invertible
    change Matrix.BlockTriangular ((g⁻¹ : GL n A) : Matrix n n A) _
    simpa only [Matrix.coe_units_inv] using Matrix.blockTriangular_inv_of_blockTriangular hg

theorem mem_blockParabolicSubgroup {g : GL n A} :
    g ∈ blockParabolicSubgroup A e ↔ ∀ i j, e i < e j → (g : Matrix n n A) i j = 0 :=
  Iff.rfl

/-- Invertible matrices whose `(i, j)` entry vanishes whenever `e i ≠ e j`: the block diagonal
matrices for the weight blocks of `e`. -/
def blockLeviSubgroup : Subgroup (GL n A) where
  carrier := {g | ∀ i j, e i ≠ e j → (g : Matrix n n A) i j = 0}
  one_mem' i j h := Matrix.one_apply_ne fun hij => h (congrArg e hij)
  mul_mem' := by
    intro g h hg hh i j hij
    have hg₁ : (g : Matrix n n A).BlockTriangular (OrderDual.toDual ∘ e) :=
      fun i j (h' : e i < e j) => hg i j h'.ne
    have hg₂ : (g : Matrix n n A).BlockTriangular e := fun i j h' => hg i j h'.ne'
    have hh₁ : (h : Matrix n n A).BlockTriangular (OrderDual.toDual ∘ e) :=
      fun i j (h' : e i < e j) => hh i j h'.ne
    have hh₂ : (h : Matrix n n A).BlockTriangular e := fun i j h' => hh i j h'.ne'
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hg₁.mul hh₁ (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from hlt)
    · exact hg₂.mul hh₂ hlt
  inv_mem' := by
    intro g hg i j hij
    let := g.invertible
    have hg₁ : (g : Matrix n n A).BlockTriangular (OrderDual.toDual ∘ e) :=
      fun i j (h' : e i < e j) => hg i j h'.ne
    have hg₂ : (g : Matrix n n A).BlockTriangular e := fun i j h' => hg i j h'.ne'
    change ((g⁻¹ : GL n A) : Matrix n n A) i j = 0
    rw [Matrix.coe_units_inv]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact Matrix.blockTriangular_inv_of_blockTriangular hg₁
        (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from hlt)
    · exact Matrix.blockTriangular_inv_of_blockTriangular hg₂ hlt

theorem mem_blockLeviSubgroup {g : GL n A} :
    g ∈ blockLeviSubgroup A e ↔ ∀ i j, e i ≠ e j → (g : Matrix n n A) i j = 0 :=
  Iff.rfl

/-- The block diagonal part of a matrix: the entries `(i, j)` with `e i = e j` are kept and all
other entries are replaced by zero. -/
def blockDiagonalPart (M : Matrix n n A) : Matrix n n A :=
  Matrix.of fun i j => if e i = e j then M i j else 0

omit [Fintype n] [DecidableEq n] in
theorem blockDiagonalPart_apply (M : Matrix n n A) (i j : n) :
    blockDiagonalPart A e M i j = if e i = e j then M i j else 0 :=
  rfl

omit [Fintype n] in
theorem blockDiagonalPart_one : blockDiagonalPart A e 1 = 1 := by
  ext i j
  rw [blockDiagonalPart_apply]
  split_ifs with h
  · rfl
  · exact (Matrix.one_apply_ne fun hij => h (congrArg e hij)).symm

omit [DecidableEq n] in
/-- On block upper triangular matrices, taking the block diagonal part is multiplicative. -/
theorem blockDiagonalPart_mul {M N : Matrix n n A}
    (hM : M.BlockTriangular (OrderDual.toDual ∘ e)) (hN : N.BlockTriangular (OrderDual.toDual ∘ e)) :
    blockDiagonalPart A e (M * N) = blockDiagonalPart A e M * blockDiagonalPart A e N := by
  ext i j
  simp only [blockDiagonalPart_apply, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hik : e i = e k
    · rw [ite_eq_left hik, ite_eq_left (hik.symm.trans hij)]
    · rw [ite_eq_right hik, zero_mul]
      rcases lt_or_gt_of_ne hik with hlt | hlt
      · rw [hM (show OrderDual.toDual (e k) < OrderDual.toDual (e i) from hlt), zero_mul]
      · rw [hN (show OrderDual.toDual (e j) < OrderDual.toDual (e k) from hij ▸ hlt), mul_zero]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hik : e i = e k
    · rw [ite_eq_right fun hkj => hij (hik.trans hkj), mul_zero]
    · rw [ite_eq_right hik, zero_mul]

/-- The block diagonal part of a block upper triangular invertible matrix, as an invertible
matrix whose inverse is the block diagonal part of the inverse. -/
def blockLeviProjection : blockParabolicSubgroup A e →* GL n A where
  toFun g :=
    { val := blockDiagonalPart A e g.val
      inv := blockDiagonalPart A e ((g.val⁻¹ : GL n A) : Matrix n n A)
      val_inv := by
        rw [← blockDiagonalPart_mul A e g.property ((blockParabolicSubgroup A e).inv_mem g.property),
          ← Units.val_mul, mul_inv_cancel, Units.val_one, blockDiagonalPart_one]
      inv_val := by
        rw [← blockDiagonalPart_mul A e ((blockParabolicSubgroup A e).inv_mem g.property) g.property,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, blockDiagonalPart_one] }
  map_one' := Units.ext (blockDiagonalPart_one A e)
  map_mul' g h := Units.ext (blockDiagonalPart_mul A e g.property h.property)

theorem coe_blockLeviProjection (g : blockParabolicSubgroup A e) :
    (blockLeviProjection A e g : Matrix n n A) = blockDiagonalPart A e g.val :=
  rfl

omit [Fintype n] in
/-- A matrix has the entries of the identity matrix at all positions `(i, j)` with `e i ≤ e j`
exactly when it is block upper triangular with block diagonal part the identity. -/
theorem blockUnipotent_iff (M : Matrix n n A) :
    (∀ i j, e i ≤ e j → M i j = (1 : Matrix n n A) i j) ↔
      M.BlockTriangular (OrderDual.toDual ∘ e) ∧ blockDiagonalPart A e M = 1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hij
      change e i < e j at hij
      rw [h i j hij.le]
      exact Matrix.one_apply_ne fun h' => hij.ne (congrArg e h')
    · ext i j
      rw [blockDiagonalPart_apply]
      split_ifs with hij
      · exact h i j hij.le
      · exact (Matrix.one_apply_ne fun h' => hij (congrArg e h')).symm
  · rintro ⟨hM, hD⟩ i j hij
    rcases hij.lt_or_eq with hlt | heq
    · rw [hM (show OrderDual.toDual (e j) < OrderDual.toDual (e i) from hlt)]
      exact (Matrix.one_apply_ne fun h' => hlt.ne (congrArg e h')).symm
    · have := congrFun (congrFun hD i) j
      rwa [blockDiagonalPart_apply, ite_eq_left heq] at this

/-- Invertible matrices with the entries of the identity matrix at all positions `(i, j)` with
`e i ≤ e j`: the block upper triangular matrices whose diagonal blocks are identity matrices. -/
def blockUnipotentSubgroup : Subgroup (GL n A) where
  carrier := {g | ∀ i j, e i ≤ e j → (g : Matrix n n A) i j = (1 : Matrix n n A) i j}
  one_mem' _ _ _ := rfl
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg₁, hg₂⟩ := (blockUnipotent_iff A e _).1 hg
    obtain ⟨hh₁, hh₂⟩ := (blockUnipotent_iff A e _).1 hh
    refine (blockUnipotent_iff A e _).2 ⟨hg₁.mul hh₁, ?_⟩
    rw [Units.val_mul, blockDiagonalPart_mul A e hg₁ hh₁, hg₂, hh₂, one_mul]
  inv_mem' := by
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := (blockUnipotent_iff A e _).1 hg
    have hinv := (blockParabolicSubgroup A e).inv_mem (x := g) hg₁
    refine (blockUnipotent_iff A e _).2 ⟨hinv, ?_⟩
    calc blockDiagonalPart A e ((g⁻¹ : GL n A) : Matrix n n A)
        = blockDiagonalPart A e ((g⁻¹ : GL n A) : Matrix n n A) *
            blockDiagonalPart A e (g : Matrix n n A) := by rw [hg₂, mul_one]
      _ = blockDiagonalPart A e (((g⁻¹ * g : GL n A)) : Matrix n n A) :=
          (blockDiagonalPart_mul A e hinv hg₁).symm
      _ = 1 := by rw [inv_mul_cancel, Units.val_one, blockDiagonalPart_one]

theorem mem_blockUnipotentSubgroup {g : GL n A} :
    g ∈ blockUnipotentSubgroup A e ↔
      ∀ i j, e i ≤ e j → (g : Matrix n n A) i j = (1 : Matrix n n A) i j :=
  Iff.rfl

variable {A} {B : Type*} [CommRing B] (f : A →+* B)

theorem map_mem_blockParabolicSubgroup {g : GL n A} (hg : g ∈ blockParabolicSubgroup A e) :
    Matrix.GeneralLinearGroup.map f g ∈ blockParabolicSubgroup B e := fun i j hij => by
  change f _ = 0
  rw [hg hij, map_zero]

theorem map_mem_blockLeviSubgroup {g : GL n A} (hg : g ∈ blockLeviSubgroup A e) :
    Matrix.GeneralLinearGroup.map f g ∈ blockLeviSubgroup B e := fun i j hij => by
  change f _ = 0
  rw [hg i j hij, map_zero]

theorem map_mem_blockUnipotentSubgroup {g : GL n A} (hg : g ∈ blockUnipotentSubgroup A e) :
    Matrix.GeneralLinearGroup.map f g ∈ blockUnipotentSubgroup B e := fun i j hij => by
  change f _ = _
  rw [hg i j hij]
  exact congrFun (congrFun (map_one f.mapMatrix) i) j

end Matrix

section Scheme

variable (n) (R : CommRingCat.{u}) (e : n → ℤ)

/-- The points of the diagonal cocharacter over a test scheme `T`: a unit `t` of `Γ(T, 𝒪_T)`
goes to the point of `GL_n` with matrix `diag(t ^ e i)`. -/
def diagonalPoints (T : Over (Spec R)) : (T ⟶ (Gm (Spec R)).X) →* (T ⟶ (groupScheme n R).X) :=
  (pointsEquiv n R T).symm.toMonoidHom.comp
    ((diagonalUnits Γ(T.left, ⊤) e).comp (Gm.pointsEquiv (Spec R) T).toMonoidHom)

variable {n R} in
theorem pointsEquiv_diagonalPoints {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    pointsEquiv n R T (diagonalPoints n R e T x) =
      diagonalUnits Γ(T.left, ⊤) e (Gm.pointsEquiv (Spec R) T x) :=
  MulEquiv.apply_symm_apply _ _

variable {n R} in
theorem diagonalPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec R)).X) :
    diagonalPoints n R e T' (a ≫ x) = a ≫ diagonalPoints n R e T x := by
  apply (pointsEquiv n R T').injective
  rw [pointsEquiv_naturality, pointsEquiv_diagonalPoints, pointsEquiv_diagonalPoints,
    Gm.pointsEquiv_naturality, map_diagonalUnits]

/-- The diagonal cocharacter `t ↦ diag(t ^ e i)` of the general linear group scheme over
`Spec R`, defined on points over every scheme `T` over `Spec R`. -/
def diagonalCocharacter : (Gm (Spec R)).toGrp ⟶ groupScheme n R :=
  homOfPoints (diagonalPoints n R e) (diagonalPoints_naturality e)

variable {n R}

/-- On points, the diagonal cocharacter sends a unit `t` to the matrix `diag(t ^ e i)`. -/
theorem pointsEquiv_diagonalCocharacter {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    pointsEquiv n R T (x ≫ (diagonalCocharacter n R e).hom.hom) =
      diagonalUnits Γ(T.left, ⊤) e (Gm.pointsEquiv (Spec R) T x) := by
  rw [diagonalCocharacter, comp_homOfPoints, pointsEquiv_diagonalPoints]

/-- The subgroup functor of `GL_n` over `Spec R` whose points over `T` are the invertible matrices
over `Γ(T, 𝒪_T)` lying in a family of matrix subgroups preserved by ring homomorphisms. -/
def ofMatrixSubgroups (H : ∀ A : CommRingCat.{u}, Subgroup (GL n A))
    (hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B) :
    SubgroupFunctor (groupScheme n R) where
  carrier T := (H Γ(T.left, ⊤)).comap (pointsEquiv n R T).toMonoidHom
  comp_mem := fun {T T'} a {x} hx => by
    change pointsEquiv n R T' (a ≫ x) ∈ H Γ(T'.left, ⊤)
    rw [pointsEquiv_naturality]
    exact hH a.left.appTop hx

theorem mem_ofMatrixSubgroups {H : ∀ A : CommRingCat.{u}, Subgroup (GL n A)}
    {hH : ∀ {A B : CommRingCat.{u}} (f : A ⟶ B) {g : GL n A}, g ∈ H A →
      Matrix.GeneralLinearGroup.map f.hom g ∈ H B}
    {T : Over (Spec R)} {x : T ⟶ (groupScheme n R).X} :
    x ∈ (ofMatrixSubgroups (R := R) H hH).carrier T ↔ pointsEquiv n R T x ∈ H Γ(T.left, ⊤) :=
  Iff.rfl

variable (n R)

/-- The block parabolic subgroup functor of `GL_n` for the weights `e`: points whose matrix has
`(i, j)` entry zero whenever `e i < e j`. -/
def blockParabolic : SubgroupFunctor (groupScheme n R) :=
  ofMatrixSubgroups (fun A => blockParabolicSubgroup A e)
    (fun f _ hg => map_mem_blockParabolicSubgroup e f.hom hg)

/-- The block Levi subgroup functor of `GL_n` for the weights `e`: points whose matrix has
`(i, j)` entry zero whenever `e i ≠ e j`. -/
def blockLevi : SubgroupFunctor (groupScheme n R) :=
  ofMatrixSubgroups (fun A => blockLeviSubgroup A e)
    (fun f _ hg => map_mem_blockLeviSubgroup e f.hom hg)

/-- The block unipotent subgroup functor of `GL_n` for the weights `e`: points whose matrix has
the entries of the identity matrix at all positions `(i, j)` with `e i ≤ e j`. -/
def blockUnipotent : SubgroupFunctor (groupScheme n R) :=
  ofMatrixSubgroups (fun A => blockUnipotentSubgroup A e)
    (fun f _ hg => map_mem_blockUnipotentSubgroup e f.hom hg)

variable {n R}

theorem mem_blockParabolic {T : Over (Spec R)} {x : T ⟶ (groupScheme n R).X} :
    x ∈ (blockParabolic n R e).carrier T ↔
      ∀ i j, e i < e j → pointsEquiv n R T x i j = 0 :=
  Iff.rfl

theorem mem_blockLevi {T : Over (Spec R)} {x : T ⟶ (groupScheme n R).X} :
    x ∈ (blockLevi n R e).carrier T ↔
      ∀ i j, e i ≠ e j → pointsEquiv n R T x i j = 0 :=
  Iff.rfl

theorem mem_blockUnipotent {T : Over (Spec R)} {x : T ⟶ (groupScheme n R).X} :
    x ∈ (blockUnipotent n R e).carrier T ↔
      ∀ i j, e i ≤ e j → pointsEquiv n R T x i j = (1 : Matrix n n Γ(T.left, ⊤)) i j :=
  Iff.rfl

end Scheme

section BlockShape

open Langlands.GeneralLinear (BlockShape)

variable {N : ℕ} (B : BlockShape N)

/-- The weights of the standard cocharacter of an ordered block shape: every coordinate in the
block numbered `i` gets the weight `-i`, so the weights decrease along the block order. -/
def blockShapeWeight (k : Fin N) : ℤ :=
  -(((B.indexEquiv.symm k).1 : ℕ) : ℤ)

@[simp] theorem blockShapeWeight_index (i : Fin B.length) (a : Fin (B.size i)) :
    blockShapeWeight B (B.index i a) = -((i : ℕ) : ℤ) := by
  change -(((B.indexEquiv.symm (B.indexEquiv ⟨i, a⟩)).1 : ℕ) : ℤ) = _
  rw [Equiv.symm_apply_apply]

/-- Every standard coordinate is the coordinate of a position in some block. -/
theorem exists_eq_index (k : Fin N) : ∃ (i : Fin B.length) (a : Fin (B.size i)), B.index i a = k :=
  ⟨(B.indexEquiv.symm k).1, (B.indexEquiv.symm k).2, B.indexEquiv.apply_symm_apply k⟩

theorem index_eq_index_iff {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j)) :
    B.index i a = B.index j b ↔ (⟨i, a⟩ : B.Index) = ⟨j, b⟩ :=
  B.indexEquiv.injective.eq_iff

theorem blockShapeWeight_lt_iff {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j)) :
    blockShapeWeight B (B.index i a) < blockShapeWeight B (B.index j b) ↔ j < i := by
  rw [blockShapeWeight_index, blockShapeWeight_index, neg_lt_neg_iff, Nat.cast_lt]
  exact Fin.lt_def.symm

theorem blockShapeWeight_eq_iff {i j : Fin B.length} (a : Fin (B.size i)) (b : Fin (B.size j)) :
    blockShapeWeight B (B.index i a) = blockShapeWeight B (B.index j b) ↔ i = j := by
  rw [blockShapeWeight_index, blockShapeWeight_index, neg_inj, Nat.cast_inj]
  exact Fin.val_inj

variable (A : Type*) [CommRing A]

/-- For the weights of a block shape, the weight-block parabolic is the Library's standard
upper block parabolic. -/
theorem blockParabolicSubgroup_blockShapeWeight :
    blockParabolicSubgroup A (blockShapeWeight B) = B.parabolic A := by
  ext g
  rw [mem_blockParabolicSubgroup, B.mem_parabolic_iff]
  constructor
  · intro h i j a b hji
    exact h _ _ ((blockShapeWeight_lt_iff B a b).2 hji)
  · intro h k l hkl
    obtain ⟨i, a, rfl⟩ := exists_eq_index B k
    obtain ⟨j, b, rfl⟩ := exists_eq_index B l
    exact h i j a b ((blockShapeWeight_lt_iff B a b).1 hkl)

/-- For the weights of a block shape, the weight-block Levi subgroup is the Library's block
diagonal subgroup, the image of `B.leviEmbedding`. -/
theorem blockLeviSubgroup_blockShapeWeight :
    blockLeviSubgroup A (blockShapeWeight B) = B.leviSubgroup A := by
  ext g
  rw [mem_blockLeviSubgroup]
  constructor
  · intro h
    have hP : g ∈ B.parabolic A := by
      rw [← blockParabolicSubgroup_blockShapeWeight, mem_blockParabolicSubgroup]
      exact fun k l hkl => h k l hkl.ne
    refine ⟨B.leviProjection A ⟨g, hP⟩, Units.ext ?_⟩
    ext k l
    obtain ⟨i, a, rfl⟩ := exists_eq_index B k
    obtain ⟨j, b, rfl⟩ := exists_eq_index B l
    by_cases hij : i = j
    · subst hij
      exact B.leviEmbedding_apply_same A _ i a b
    · rw [B.leviEmbedding_apply_ne A _ a b hij]
      exact (h _ _ fun hw => hij ((blockShapeWeight_eq_iff B a b).1 hw)).symm
  · rintro ⟨m, rfl⟩ k l hkl
    obtain ⟨i, a, rfl⟩ := exists_eq_index B k
    obtain ⟨j, b, rfl⟩ := exists_eq_index B l
    exact B.leviEmbedding_apply_ne A m a b fun hij =>
      hkl ((blockShapeWeight_eq_iff B a b).2 hij)

/-- For the weights of a block shape, the weight-block unipotent subgroup is the Library's block
unipotent radical, included in the general linear group. -/
theorem blockUnipotentSubgroup_blockShapeWeight :
    blockUnipotentSubgroup A (blockShapeWeight B) = B.unipotentSubgroup A := by
  ext g
  rw [mem_blockUnipotentSubgroup, B.mem_unipotentSubgroup_iff]
  constructor
  · intro h
    refine ⟨?_, fun i a b => ?_⟩
    · rw [← blockParabolicSubgroup_blockShapeWeight]
      exact ((blockUnipotent_iff A _ _).1 h).1
    · rw [h _ _ ((blockShapeWeight_eq_iff B a b).2 rfl).le, Matrix.one_apply]
      simp only [EmbeddingLike.apply_eq_iff_eq]
  · rintro ⟨hP, hD⟩ k l hkl
    obtain ⟨i, a, rfl⟩ := exists_eq_index B k
    obtain ⟨j, b, rfl⟩ := exists_eq_index B l
    rcases hkl.lt_or_eq with hlt | heq
    · have hji : j < i := (blockShapeWeight_lt_iff B a b).1 hlt
      rw [(B.mem_parabolic_iff A g).1 hP i j a b hji, Matrix.one_apply_ne]
      rw [Ne, index_eq_index_iff, Sigma.mk.inj_iff]
      exact fun h => hji.ne' h.1
    · obtain rfl := (blockShapeWeight_eq_iff B a b).1 heq
      rw [hD i a b, Matrix.one_apply]
      simp only [EmbeddingLike.apply_eq_iff_eq]

/-- For the weights of a block shape, the block diagonal part of a block upper triangular matrix
is the image under `B.leviEmbedding` of the Library's diagonal-block projection
`B.leviProjection`. -/
theorem leviEmbedding_leviProjection (g : blockParabolicSubgroup A (blockShapeWeight B)) :
    B.leviEmbedding A (B.leviProjection A
        (MulEquiv.subgroupCongr (blockParabolicSubgroup_blockShapeWeight B A) g)) =
      blockLeviProjection A (blockShapeWeight B) g := by
  apply Units.ext
  ext k l
  rw [coe_blockLeviProjection, blockDiagonalPart_apply]
  obtain ⟨i, a, rfl⟩ := exists_eq_index B k
  obtain ⟨j, b, rfl⟩ := exists_eq_index B l
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left ((blockShapeWeight_eq_iff B a b).2 rfl)]
    exact B.leviEmbedding_apply_same A _ i a b
  · rw [ite_eq_right fun hw => hij ((blockShapeWeight_eq_iff B a b).1 hw)]
    exact B.leviEmbedding_apply_ne A _ a b hij

variable (R : CommRingCat.{u})

/-- The standard cocharacter of a block shape: `t` acts on the `i`-th block by `t ^ (-i)`. -/
def blockShapeCocharacter : (Gm (Spec R)).toGrp ⟶ groupScheme (Fin N) R :=
  diagonalCocharacter (Fin N) R (blockShapeWeight B)

/-- The subgroup functor of `GL_N` over `Spec R` given by the Library's standard upper block
parabolic `B.parabolic` on the points over every test scheme. -/
def blockShapeParabolic : SubgroupFunctor (groupScheme (Fin N) R) :=
  ofMatrixSubgroups (fun A => B.parabolic A) fun f _ hg => by
    rw [← blockParabolicSubgroup_blockShapeWeight] at hg ⊢
    exact map_mem_blockParabolicSubgroup _ f.hom hg

/-- The subgroup functor of `GL_N` over `Spec R` given by the Library's block diagonal subgroup
`B.leviSubgroup` on the points over every test scheme. -/
def blockShapeLevi : SubgroupFunctor (groupScheme (Fin N) R) :=
  ofMatrixSubgroups (fun A => B.leviSubgroup A) fun f _ hg => by
    rw [← blockLeviSubgroup_blockShapeWeight] at hg ⊢
    exact map_mem_blockLeviSubgroup _ f.hom hg

/-- The subgroup functor of `GL_N` over `Spec R` given by the Library's block unipotent subgroup
`B.unipotentSubgroup` on the points over every test scheme. -/
def blockShapeUnipotent : SubgroupFunctor (groupScheme (Fin N) R) :=
  ofMatrixSubgroups (fun A => B.unipotentSubgroup A) fun f _ hg => by
    rw [← blockUnipotentSubgroup_blockShapeWeight] at hg ⊢
    exact map_mem_blockUnipotentSubgroup _ f.hom hg

theorem blockParabolic_blockShapeWeight :
    blockParabolic (Fin N) R (blockShapeWeight B) = blockShapeParabolic B R :=
  SubgroupFunctor.ext fun T =>
    congrArg (Subgroup.comap _) (blockParabolicSubgroup_blockShapeWeight B Γ(T.left, ⊤))

theorem blockLevi_blockShapeWeight :
    blockLevi (Fin N) R (blockShapeWeight B) = blockShapeLevi B R :=
  SubgroupFunctor.ext fun T =>
    congrArg (Subgroup.comap _) (blockLeviSubgroup_blockShapeWeight B Γ(T.left, ⊤))

theorem blockUnipotent_blockShapeWeight :
    blockUnipotent (Fin N) R (blockShapeWeight B) = blockShapeUnipotent B R :=
  SubgroupFunctor.ext fun T =>
    congrArg (Subgroup.comap _) (blockUnipotentSubgroup_blockShapeWeight B Γ(T.left, ⊤))

end BlockShape

end Langlands.GroupScheme.GeneralLinear
