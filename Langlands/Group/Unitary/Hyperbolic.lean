import Langlands.Group.Unitary.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The quasi-split unitary group `U(ν, ν)`

The hyperbolic form on `E^{ν ⊕ ν}` has the Gram matrix

`hyperbolicForm ν E = [[0, 1], [-1, 0]] = -J`,

for Mathlib's `Matrix.J ν E = [[0, -1], [1, 0]]` (`hyperbolicForm_eq_neg_J`). Its unitary group
`U(ν, ν) = UnitaryGroup.ofForm c (hyperbolicForm ν E)` is the group of `g` with
`gᵀ J c(g) = J`, equivalently `g J c(g)ᵀ = J` (`mem_ofForm_hyperbolicForm_iff`). It contains

- the Siegel Levi elements `siegelLevi c hc a = diag(a, c(a)⁻ᵀ)` for `a ∈ GL_ν(E)`,
- the Siegel unipotent elements `siegelUnipotent c b hb = [[1, b], [0, 1]]` for `b` Hermitian
  (`c(b)ᵀ = b`),
- the Weyl element `weylElement c ν = hyperbolicForm ν E`.

The Siegel parabolic subgroup `siegelParabolic c ν` consists of the elements whose lower left
block vanishes; it is the product of the Levi and unipotent parts
(`exists_eq_siegelLevi_mul_siegelUnipotent`). An element is in the big cell (`IsInBigCell`) if it
lies in `P w P`, for `P` the Siegel parabolic and `w` the Weyl element.
-/

open Matrix

namespace Langlands

namespace UnitaryGroup

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)

/-- The Gram matrix `[[0, 1], [-1, 0]]` of the hyperbolic form on `E^{ν ⊕ ν}`, which is
`-Matrix.J ν E`. -/
def hyperbolicForm (ν E : Type*) [DecidableEq ν] [CommRing E] : Matrix (ν ⊕ ν) (ν ⊕ ν) E :=
  -Matrix.J ν E

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

omit [Fintype ν] in
theorem hyperbolicForm_eq_fromBlocks : hyperbolicForm ν E = fromBlocks 0 1 (-1) 0 := by
  simp [hyperbolicForm, Matrix.J, fromBlocks_neg]

omit [Fintype ν] in
theorem hyperbolicForm_eq_neg_J : hyperbolicForm ν E = -Matrix.J ν E := rfl

theorem hyperbolicForm_mul_self : hyperbolicForm ν E * hyperbolicForm ν E = -1 := by
  simp [hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

omit [Fintype ν] in
theorem transpose_hyperbolicForm : (hyperbolicForm ν E)ᵀ = -hyperbolicForm ν E := by
  simp [hyperbolicForm_eq_fromBlocks, fromBlocks_transpose, fromBlocks_neg]

/-- Membership in `U(ν, ν)` read on the other side: `g J c(g)ᵀ = J`. -/
theorem mem_ofForm_hyperbolicForm_iff (g : GL (ν ⊕ ν) E) :
    g ∈ ofForm c (hyperbolicForm ν E) ↔
      (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E) * hyperbolicForm ν E *
        ((g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c)ᵀ = hyperbolicForm ν E := by
  have hT := transpose_hyperbolicForm (ν := ν) (E := E)
  have key : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * hyperbolicForm ν E * B = hyperbolicForm ν E →
      B * hyperbolicForm ν E * A = hyperbolicForm ν E := by
    intro A B h
    have h1 : A * (hyperbolicForm ν E * B * -hyperbolicForm ν E) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_neg, hyperbolicForm_mul_self,
        neg_neg]
    have h2 := mul_eq_one_comm.mp h1
    calc B * hyperbolicForm ν E * A =
        (hyperbolicForm ν E * hyperbolicForm ν E) * (B * -hyperbolicForm ν E * A) := by
          rw [hyperbolicForm_mul_self]; simp
      _ = hyperbolicForm ν E * (hyperbolicForm ν E * B * -hyperbolicForm ν E * A) := by
          simp only [Matrix.mul_assoc]
      _ = hyperbolicForm ν E := by rw [h2, Matrix.mul_one]
  have tr : ∀ A B : Matrix (ν ⊕ ν) (ν ⊕ ν) E, A * hyperbolicForm ν E * B = hyperbolicForm ν E →
      Bᵀ * hyperbolicForm ν E * Aᵀ = hyperbolicForm ν E := by
    intro A B h
    have h1 := congrArg Matrix.transpose h
    rw [transpose_mul, transpose_mul, hT, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] at h1
    exact neg_injective h1
  constructor
  · intro h
    have h1 := tr _ _ (show (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)ᵀ * hyperbolicForm ν E *
      (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c = _ from h)
    rw [transpose_transpose] at h1
    exact key _ _ h1
  · intro h
    have h1 := tr _ _ (key _ _ h)
    rw [transpose_transpose] at h1
    exact h1

/-- The Siegel Levi element `diag(a, c(a⁻¹)ᵀ)` of `U(ν, ν)`. -/
def siegelLevi (hc : Function.Involutive c) (a : GL ν E) : ofForm c (hyperbolicForm ν E) :=
  ⟨⟨fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ,
    fromBlocks ((a⁻¹ : GL ν E) : Matrix ν ν E) 0 0 ((a : Matrix ν ν E).map c)ᵀ, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp, by
      rw [fromBlocks_multiply, ← transpose_mul, ← Matrix.map_mul (f := c), Units.inv_mul,
        Matrix.map_one _ (map_zero c) (map_one c)]
      simp⟩, by
    rw [mem_ofForm_hyperbolicForm_iff]
    have h1 : ∀ A : Matrix ν ν E, (A.map c)ᵀ.map c = Aᵀ := fun A => by ext i j; simp [hc _]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    simp only [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose,
      fromBlocks_multiply, h1, h0, transpose_transpose, transpose_zero, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul,
      neg_zero]
    rw [← transpose_mul, ← Matrix.map_mul (f := c), Units.mul_inv,
      Matrix.map_one _ (map_zero c) (map_one c), transpose_one]⟩

theorem siegelLevi_val (hc : Function.Involutive c) (a : GL ν E) :
    ((siegelLevi c hc a : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      fromBlocks (a : Matrix ν ν E) 0 0 (((a⁻¹ : GL ν E) : Matrix ν ν E).map c)ᵀ := rfl

/-- The Weyl element `[[0, 1], [-1, 0]]` of `U(ν, ν)`. -/
def weylElement (ν : Type*) [Fintype ν] [DecidableEq ν] : ofForm c (hyperbolicForm ν E) :=
  ⟨⟨hyperbolicForm ν E, -hyperbolicForm ν E,
    by rw [Matrix.mul_neg, hyperbolicForm_mul_self, neg_neg],
    by rw [Matrix.neg_mul, hyperbolicForm_mul_self, neg_neg]⟩, by
    rw [mem_ofForm_hyperbolicForm_iff]
    have h : ((hyperbolicForm ν E).map c)ᵀ = -hyperbolicForm ν E := by
      ext (i | i) (j | j) <;> simp [hyperbolicForm_eq_fromBlocks, one_apply, eq_comm]
    change hyperbolicForm ν E * hyperbolicForm ν E * ((hyperbolicForm ν E).map c)ᵀ =
      hyperbolicForm ν E
    rw [h, hyperbolicForm_mul_self]
    simp⟩

theorem weylElement_val :
    ((weylElement c ν : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = hyperbolicForm ν E := rfl

/-- The Siegel unipotent element `[[1, b], [0, 1]]` of `U(ν, ν)`, for `b` Hermitian. -/
def siegelUnipotent (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : ofForm c (hyperbolicForm ν E) :=
  ⟨⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, by
    rw [mem_ofForm_hyperbolicForm_iff]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
    simp [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
      h0, h1, hb]⟩

theorem siegelUnipotent_val (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ((siegelUnipotent c b hb : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromBlocks 1 b 0 1 :=
  rfl

/-- The matrix of the inverse: `g⁻¹ = -J c(g)ᵀ J`. -/
theorem val_inv (g : ofForm c (hyperbolicForm ν E)) :
    (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) =
      -(hyperbolicForm ν E * (((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E).map c)ᵀ *
        hyperbolicForm ν E) := by
  set G := ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) with hG
  have hg : G * hyperbolicForm ν E * (G.map c)ᵀ = hyperbolicForm ν E :=
    (mem_ofForm_hyperbolicForm_iff c (g : GL (ν ⊕ ν) E)).1 g.2
  have hr : G * -(hyperbolicForm ν E * (G.map c)ᵀ * hyperbolicForm ν E) = 1 := by
    rw [Matrix.mul_neg, ← mul_assoc, ← mul_assoc, hg, hyperbolicForm_mul_self, neg_neg]
  have hl : (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) :
      Matrix (ν ⊕ ν) (ν ⊕ ν) E) * G = 1 := by
    rw [hG, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  calc (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
      = (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) *
        (G * -(hyperbolicForm ν E * (G.map c)ᵀ * hyperbolicForm ν E)) := by rw [hr, mul_one]
    _ = -(hyperbolicForm ν E * (G.map c)ᵀ * hyperbolicForm ν E) := by
        rw [← mul_assoc, hl, one_mul]

/-- The Siegel parabolic subgroup: the elements of `U(ν, ν)` with vanishing lower left block. -/
def siegelParabolic (ν : Type*) [Fintype ν] [DecidableEq ν] :
    Subgroup (ofForm c (hyperbolicForm ν E)) where
  carrier := {g | ((g : GL (ν ⊕ ν) E).val).toBlocks₂₁ = 0}
  one_mem' := by
    ext i j
    simp [toBlocks₂₁]
  mul_mem' := by
    intro g h hg hh
    change ((g : GL (ν ⊕ ν) E).val * (h : GL (ν ⊕ ν) E).val).toBlocks₂₁ = 0
    rw [← fromBlocks_toBlocks ((g : GL (ν ⊕ ν) E).val), ← fromBlocks_toBlocks ((h : GL
        (ν ⊕ ν) E).val), fromBlocks_multiply,
      toBlocks_fromBlocks₂₁, show ((g : GL (ν ⊕ ν) E).val).toBlocks₂₁ = 0 from hg,
      show ((h : GL (ν ⊕ ν) E).val).toBlocks₂₁ = 0 from hh]
    simp
  inv_mem' := by
    intro g hg
    change (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) :
      Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    rw [val_inv, ← fromBlocks_toBlocks ((g : GL (ν ⊕ ν) E).val),
        show ((g : GL (ν ⊕ ν) E).val).toBlocks₂₁ = 0 from hg]
    simp [hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply,
      fromBlocks_neg, h0]

theorem mem_siegelParabolic {g : ofForm c (hyperbolicForm ν E)} :
    g ∈ siegelParabolic c ν ↔
      (((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)).toBlocks₂₁ = 0 :=
  Iff.rfl

theorem siegelLevi_mem (hc : Function.Involutive c) (a : GL ν E) :
    siegelLevi c hc a ∈ siegelParabolic c ν := by
  rw [mem_siegelParabolic, siegelLevi_val, toBlocks_fromBlocks₂₁]

theorem siegelUnipotent_mem (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    siegelUnipotent c b hb ∈ siegelParabolic c ν := by
  rw [mem_siegelParabolic, siegelUnipotent_val, toBlocks_fromBlocks₂₁]

/-- `g` lies in the big cell `P w P` of the Siegel parabolic `P` and the Weyl element `w`. -/
def IsInBigCell (g : ofForm c (hyperbolicForm ν E)) : Prop :=
  ∃ p ∈ siegelParabolic c ν, ∃ q ∈ siegelParabolic c ν, g = p * weylElement c ν * q

/-- **The Siegel parabolic is the product of its Levi and unipotent parts.** An element
`p = [[A, B], [0, D]]` of the Siegel parabolic has `A c(D)ᵀ = 1` and `A c(B)ᵀ = B c(A)ᵀ`, and
`p = siegelLevi a * siegelUnipotent b` with `a = A`, `b = c(D)ᵀ B`. -/
theorem exists_eq_siegelLevi_mul_siegelUnipotent (hc : Function.Involutive c)
    (p : ofForm c (hyperbolicForm ν E)) (hp : p ∈ siegelParabolic c ν) :
    ((p : GL (ν ⊕ ν) E).val).toBlocks₁₁ * ((((p : GL (ν ⊕ ν) E).val).toBlocks₂₂).map c)ᵀ = 1 ∧
    ((p : GL (ν ⊕ ν) E).val).toBlocks₁₁ * ((((p : GL (ν ⊕ ν) E).val).toBlocks₁₂).map c)ᵀ =
      ((p : GL (ν ⊕ ν) E).val).toBlocks₁₂ * ((((p : GL (ν ⊕ ν) E).val).toBlocks₁₁).map c)ᵀ ∧
    ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b),
      p = siegelLevi c hc a * siegelUnipotent c b hb := by
  rw [mem_siegelParabolic] at hp
  have hu := (mem_ofForm_hyperbolicForm_iff c (p : GL (ν ⊕ ν) E)).mp p.2
  set M := (p : GL (ν ⊕ ν) E).val
  rw [← fromBlocks_toBlocks M, hp] at hu
  rw [hyperbolicForm_eq_fromBlocks] at hu
  simp only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu
  simp at hu
  obtain ⟨h1, h2, h3⟩ := hu
  have h2' := mul_eq_one_comm.mp h2
  have h3' := mul_eq_one_comm.mp h3
  have hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X := fun X => by ext i j; simp [hc _]
  have hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ :=
    sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)
  refine ⟨h2, hAB, ?_⟩
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  let a : GL ν E := ⟨A, (D.map c)ᵀ, h2, h2'⟩
  have hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B := by
    rw [Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]
    have hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ := hAB.symm
    calc (B.map c)ᵀ * D = (D.map c)ᵀ * A * (B.map c)ᵀ * D := by rw [h2', Matrix.one_mul]
      _ = (D.map c)ᵀ * (B * (A.map c)ᵀ) * D := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B * ((A.map c)ᵀ * D) := by simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B := by rw [h3', Matrix.mul_one]
  refine ⟨a, (D.map c)ᵀ * B, hb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, siegelLevi_val]
  unfold siegelUnipotent
  simp only [fromBlocks_multiply]
  have ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ := rfl
  rw [ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]
  change M = _
  conv_lhs => rw [← fromBlocks_toBlocks M, hp]
  simp [A, B, D]
  rfl

end UnitaryGroup

end Langlands
