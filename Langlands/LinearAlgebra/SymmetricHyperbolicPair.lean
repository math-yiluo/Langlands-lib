import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Orthogonal decomposition along a normalized hyperbolic pair -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.SymmetricBilinear

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- An isotropic pair with mutual pairing one. -/
structure HyperbolicPair (B : LinearMap.BilinForm K V) where
  x : V
  y : V
  xx : B x x = 0
  xy : B x y = 1
  yy : B y y = 0

namespace HyperbolicPair

variable {B : LinearMap.BilinForm K V}

/-- Complete a nonzero isotropic vector of a nondegenerate symmetric form to a
  normalized hyperbolic pair. -/
theorem exists_with_first (hS : B.IsSymm) (hB : B.Nondegenerate) (h2 : (2 : K) ≠ 0)
    (x : V) (hx : x ≠ 0) (hxx : B x x = 0) : ∃ P : HyperbolicPair B, P.x = x := by
  obtain ⟨y, hy⟩ : ∃ y, B x y ≠ 0 := by
    by_contra! h
    exact hx (hB.1 x h)
  obtain ⟨z, hz⟩ : ∃ z, B x z = 1 := by
    refine ⟨(B x y)⁻¹ • y, ?_⟩
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  let a := B z z / 2
  refine ⟨⟨x, z - a • x, hxx, ?_, ?_⟩, rfl⟩
  · rw [map_sub, map_smul, hxx, smul_zero, sub_zero, hz]
  · have hzx := (hS.eq z x).trans hz
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hxx, hz, hzx, smul_eq_mul,
      mul_one, mul_zero, sub_zero]
    change B z z - a - a = 0
    dsimp only [a]
    field_simp
    ring

variable (P : HyperbolicPair B)

/-- The common kernel of the two hyperbolic pairings. -/
def orthogonalComplement : Submodule K V := LinearMap.ker (B P.x) ⊓ LinearMap.ker (B P.y)

@[simp]
theorem mem_orthogonalComplement (v : V) :
    v ∈ P.orthogonalComplement ↔ B P.x v = 0 ∧ B P.y v = 0 := Iff.rfl

private theorem project_mem (hS : B.IsSymm) (v : V) :
    v - B P.y v • P.x - B P.x v • P.y ∈ P.orthogonalComplement := by
  have hyx := (hS.eq P.y P.x).trans P.xy
  rw [P.mem_orthogonalComplement]
  constructor <;> simp [P.xx, P.yy, P.xy, hyx, smul_eq_mul]

/-- Coordinates in the hyperbolic plane and its orthogonal complement. -/
def split (hS : B.IsSymm) : ((K × K) × P.orthogonalComplement) ≃ₗ[K] V where
  toFun p := p.1.1 • P.x + p.1.2 • P.y + p.2
  invFun v := ((B P.y v, B P.x v), ⟨v - B P.y v • P.x - B P.x v • P.y, P.project_mem hS v⟩)
  left_inv p := by
    have hyx := (hS.eq P.y P.x).trans P.xy
    have hp := (P.mem_orthogonalComplement p.2).mp p.2.property
    have hx : B P.x (p.1.1 • P.x + p.1.2 • P.y + p.2) = p.1.2 := by
      simp [P.xx, P.xy, hp.1, smul_eq_mul]
    have hy : B P.y (p.1.1 • P.x + p.1.2 • P.y + p.2) = p.1.1 := by
      simp [P.yy, hyx, hp.2, smul_eq_mul]
    refine Prod.ext (Prod.ext hy hx) (Subtype.ext ?_)
    change (p.1.1 • P.x + p.1.2 • P.y + p.2) - (B P.y _) • P.x - (B P.x _) • P.y = p.2
    rw [hy, hx]
    abel
  right_inv v := by
    change (B P.y v) • P.x + (B P.x v) • P.y + (v - B P.y v • P.x - B P.x v • P.y) = v
    abel
  map_add' p q := by
    change (p.1.1 + q.1.1) • P.x + (p.1.2 + q.1.2) • P.y + ((p.2 : V) + q.2) =
      (p.1.1 • P.x + p.1.2 • P.y + p.2) + (q.1.1 • P.x + q.1.2 • P.y + q.2)
    simp only [add_smul]
    abel
  map_smul' r p := by
    change (r * p.1.1) • P.x + (r * p.1.2) • P.y + r • (p.2 : V) =
      r • (p.1.1 • P.x + p.1.2 • P.y + p.2)
    rw [smul_add, smul_add, mul_smul, mul_smul]

@[simp]
theorem split_apply (hS : B.IsSymm) (p : (K × K) × P.orthogonalComplement) :
    P.split hS p = p.1.1 • P.x + p.1.2 • P.y + p.2 := rfl

theorem split_symm_snd (hS : B.IsSymm) (v : V) :
    ((P.split hS).symm v).2.val = v - B P.y v • P.x - B P.x v • P.y := rfl

/-- In the split coordinates the two summands are mutually orthogonal. -/
theorem split_pairing (hS : B.IsSymm) (p q : (K × K) × P.orthogonalComplement) :
    B (P.split hS p) (P.split hS q) = p.1.1 * q.1.2 + p.1.2 * q.1.1 + B p.2 q.2 := by
  have hp := (P.mem_orthogonalComplement p.2).mp p.2.property
  have hq := (P.mem_orthogonalComplement q.2).mp q.2.property
  have hp₁ := (hS.eq (p.2 : V) P.x).trans hp.1
  have hp₂ := (hS.eq (p.2 : V) P.y).trans hp.2
  have hyx := (hS.eq P.y P.x).trans P.xy
  simp only [split_apply, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, P.xx, P.yy,
    P.xy, hp₁, hp₂, hq.1, hq.2, hyx, smul_eq_mul, mul_zero, zero_add, add_zero, mul_one]
  ac_rfl

/-- Restricting to the orthogonal complement preserves nondegeneracy. -/
theorem nondegenerate_restrict (hS : B.IsSymm) (hB : B.Nondegenerate) :
    (B.restrict P.orthogonalComplement).Nondegenerate := by
  have hLeft : (B.restrict P.orthogonalComplement).SeparatingLeft := by
    intro z hz
    apply Subtype.ext
    apply hB.1
    intro v
    obtain ⟨p, rfl⟩ := (P.split hS).surjective v
    have he : P.split hS ((0, 0), z) = (z : V) := by simp
    rw [← he, P.split_pairing]
    simpa using hz p.2
  refine ⟨hLeft, fun z hz => hLeft z fun w => ?_⟩
  change B (z : V) w = 0
  rw [hS.eq]
  exact hz w

/-- Extend a complement basis by the ordered hyperbolic pair. -/
def splitBasis {J : Type w} (hS : B.IsSymm) (b : Module.Basis J K P.orthogonalComplement) :
    Module.Basis (Fin 2 ⊕ J) K V := ((Module.Basis.finTwoProd K).prod b).map (P.split hS)

/-- The hyperbolic plane contributes a factor of negative one to the Gram determinant. -/
theorem det_splitBasis {J : Type w} [Fintype J] [DecidableEq J] (hS : B.IsSymm)
    (b : Module.Basis J K P.orthogonalComplement) :
    (LinearMap.BilinForm.toMatrix (P.splitBasis hS b) B).det = -(LinearMap.BilinForm.toMatrix b (B.restrict P.orthogonalComplement)).det := by
  let A : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]
  let C := LinearMap.BilinForm.toMatrix b (B.restrict P.orthogonalComplement)
  have hM : LinearMap.BilinForm.toMatrix (P.splitBasis hS b) B = Matrix.fromBlocks A 0 0 C := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    all_goals
      rw [LinearMap.BilinForm.toMatrix_apply, splitBasis, Module.Basis.map_apply, Module.Basis.map_apply,
        P.split_pairing]
      simp only [Module.Basis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, LinearMap.inl_apply,
        LinearMap.inr_apply]
    · fin_cases i <;> fin_cases j <;> simp [A, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
    · simp
    · simp
    · simp [C, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply]
  rw [hM, Matrix.det_fromBlocks_zero₂₁, show A.det = -1 by simp [A, Matrix.det_fin_two], neg_one_mul]

end HyperbolicPair

end Langlands.SymmetricBilinear
