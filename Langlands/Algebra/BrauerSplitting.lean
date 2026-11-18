import Langlands.Algebra.BrauerGroup

/-! # Neutral Brauer classes and actual matrix charts -/

noncomputable section

namespace Langlands.Brauer

universe u v w t

section MatrixCorner

variable {K : Type u} [Field K]
variable {A : Type v} [Ring A] [Algebra K A]
variable {V : Type w} [AddCommGroup V] [Module K V]
variable {ι : Type t} [Fintype ι] [DecidableEq ι]
variable (e : Matrix ι ι A ≃ₐ[K] Module.End K V) (i : ι)

/-- The image of a diagonal matrix idempotent in an actual representation. -/
abbrev matrixCornerSpace : Submodule K V :=
  LinearMap.range (e (Matrix.single i i (1 : A)))

theorem matrixCorner_fixed (x : matrixCornerSpace e i) :
    e (Matrix.single i i (1 : A)) x = x := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy, ← Module.End.mul_apply, ← map_mul]
  simp

theorem matrixCorner_mem (a : A) (x : V) :
    e (Matrix.single i i a) x ∈ matrixCornerSpace e i := by
  refine ⟨e (Matrix.single i i a) x, ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  simp

/-- The coefficient algebra acts on the image of the diagonal idempotent. -/
def matrixCornerLinear : A →ₗ[K] Module.End K (matrixCornerSpace e i) where
  toFun a := (e (Matrix.single i i a)).restrict (fun x _ => matrixCorner_mem e i a x)
  map_add' a b := by
    ext x
    change e (Matrix.single i i (a + b)) x =
      e (Matrix.single i i a) x + e (Matrix.single i i b) x
    simp [Matrix.single_add]
  map_smul' r a := by
    ext x
    change e (Matrix.single i i (r • a)) x = r • e (Matrix.single i i a) x
    simp [← Matrix.smul_single]

/-- The unital corner action on its actual image space. -/
def matrixCornerHom : A →ₐ[K] Module.End K (matrixCornerSpace e i) :=
  AlgHom.ofLinearMap (matrixCornerLinear e i)
    (by
      ext x
      exact matrixCorner_fixed e i x)
    (by
      intro a b
      ext x
      change e (Matrix.single i i (a * b)) x =
        e (Matrix.single i i a) (e (Matrix.single i i b) x)
      rw [← Module.End.mul_apply, ← map_mul]
      simp)

@[simp] theorem matrixCornerHom_apply (a : A) (x : matrixCornerSpace e i) :
    (matrixCornerHom e i a x : V) = e (Matrix.single i i a) x := rfl

instance matrixCorner_nontrivial [Nontrivial A] :
    Nontrivial (matrixCornerSpace e i) := by
  have hp : e (Matrix.single i i (1 : A)) ≠ 0 := by
    intro h
    have hs := e.injective (h.trans e.map_zero.symm)
    have hentry := congrArg (fun M : Matrix ι ι A => M i i) hs
    simp at hentry
  have hx : ∃ x : V, e (Matrix.single i i (1 : A)) x ≠ 0 := by
    by_contra! h
    exact hp (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hx
  exact ⟨⟨⟨e (Matrix.single i i (1 : A)) x, ⟨x, rfl⟩⟩, 0,
    fun h => hx (congrArg Subtype.val h)⟩⟩

theorem matrixCornerHom_surjective :
    Function.Surjective (matrixCornerHom e i) := by
  intro g
  let p := e (Matrix.single i i (1 : A))
  let f : Module.End K V :=
    (matrixCornerSpace e i).subtype.comp (g.comp p.rangeRestrict)
  let x := e.symm f
  have hfx : e x = f := e.apply_symm_apply f
  have he : e (Matrix.single i i (x i i)) = p * f * p := by
    calc
      e (Matrix.single i i (x i i)) =
          e (Matrix.single i i (1 : A) * x * Matrix.single i i (1 : A)) := by simp
      _ = p * f * p := by rw [map_mul, map_mul, hfx]
  refine ⟨x i i, ?_⟩
  ext y
  change e (Matrix.single i i (x i i)) y = (g y : V)
  rw [he]
  change p (f (p y)) = (g y : V)
  rw [matrixCorner_fixed e i y]
  have hpy : p.rangeRestrict y = y := Subtype.ext (matrixCorner_fixed e i y)
  change p (g (p.rangeRestrict y)) = (g y : V)
  rw [hpy]
  exact matrixCorner_fixed e i (g y)

/-- A matrix algebra represented as a full endomorphism algebra has full corners. -/
def matrixCornerEquiv [IsSimpleRing A] :
    A ≃ₐ[K] Module.End K (matrixCornerSpace e i) :=
  AlgEquiv.ofBijective (matrixCornerHom e i)
    ⟨(matrixCornerHom e i).toRingHom.injective, matrixCornerHom_surjective e i⟩

end MatrixCorner

variable {K : Type u} [Field K]

/-- Actual splitting means an algebra chart of positive matrix size. -/
def IsSplit (A : CSA.{u, u} K) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-- Cancelling matrix stabilization against the ground field gives a matrix chart. -/
theorem isSplit_of_equivalent_groundField (A : CSA.{u, u} K)
    (h : IsBrauerEquivalent A (groundField K)) : IsSplit A := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  let : NeZero n := ⟨hn⟩
  let e' : Matrix (Fin n) (Fin n) A ≃ₐ[K] Module.End K (Fin m → K) :=
    e.trans Matrix.toLinAlgEquiv'
  let W := matrixCornerSpace e' (0 : Fin n)
  exact ⟨Module.finrank K W, Module.finrank_pos, ⟨
    (matrixCornerEquiv e' 0).trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K W))⟩⟩

theorem classOf_eq_zero_iff (A : CSA.{u, u} K) :
    classOf A = 0 ↔ IsSplit A := by
  constructor
  · intro h
    exact isSplit_of_equivalent_groundField A ((classOf_eq_iff A (groundField K)).mp h)
  · rintro ⟨n, hn, ⟨e⟩⟩
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact (classOf_eq_of_algEquiv (A := A) (B := matrix (groundField K) n) e).trans
      ((classOf_matrix (groundField K) n).trans classOf_groundField)

/-- A chosen positive size for a neutral actual Brauer class. -/
def neutralMatrixSize (A : CSA.{u, u} K) (h : classOf A = 0) : ℕ :=
  ((classOf_eq_zero_iff A).mp h).choose

theorem neutralMatrixSize_pos (A : CSA.{u, u} K) (h : classOf A = 0) :
    0 < neutralMatrixSize A h :=
  ((classOf_eq_zero_iff A).mp h).choose_spec.1

/-- A chosen actual matrix chart for a neutral Brauer class. -/
def neutralMatrixChart (A : CSA.{u, u} K) (h : classOf A = 0) :
    A ≃ₐ[K] Matrix (Fin (neutralMatrixSize A h)) (Fin (neutralMatrixSize A h)) K :=
  ((classOf_eq_zero_iff A).mp h).choose_spec.2.some

end Langlands.Brauer
