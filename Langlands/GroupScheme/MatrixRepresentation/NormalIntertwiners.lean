import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentation.NormalCharacterSpan

/-! # Linear operations and normal-subgroup conjugation of actual intertwiners -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The zero matrix is an actual intertwiner. -/
theorem intertwines_zero (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) :
    Intertwines ρ σ (0 : Matrix m n k) := by
  intro A x
  simp

/-- Sums of actual intertwiners remain equivariant on every affine test. -/
theorem Intertwines.add {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C D : Matrix m n k} (hC : Intertwines ρ σ C) (hD : Intertwines ρ σ D) :
    Intertwines ρ σ (C + D) := by
  intro A x
  rw [Matrix.map_add _ (map_add _), Matrix.add_mul, Matrix.mul_add, hC A x, hD A x]

/-- Scalar multiples of actual intertwiners remain equivariant. -/
theorem Intertwines.smul {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {C : Matrix m n k} (hC : Intertwines ρ σ C) (a : k) :
    Intertwines ρ σ (a • C) := by
  intro A x
  have hs : (a • C).map (algebraMap k A) =
      algebraMap k A a • C.map (algebraMap k A) := by
    ext r s
    change algebraMap k A (a * C r s) = algebraMap k A a * algebraMap k A (C r s)
    exact map_mul _ _ _
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, hC A x]

/-- Actual all-test intertwiners form a ground-field subspace of matrices. -/
def intertwinerSubmodule (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m) :
    Submodule k (Matrix m n k) where
  carrier := {C | Intertwines ρ σ C}
  zero_mem' := intertwines_zero ρ σ
  add_mem' := fun hC hD => hC.add hD
  smul_mem' := fun a _ hC => hC.smul a

@[simp]
theorem mem_intertwinerSubmodule (ρ : MatrixRepresentation G n)
    (σ : MatrixRepresentation G m) (C : Matrix m n k) :
    C ∈ intertwinerSubmodule ρ σ ↔ Intertwines ρ σ C := Iff.rfl

/-- Finite sums of actual intertwiners remain equivariant. -/
theorem intertwines_sum {ρ : MatrixRepresentation G n} {σ : MatrixRepresentation G m}
    {J : Type*} (s : Finset J) (C : J → Matrix m n k)
    (hC : ∀ j ∈ s, Intertwines ρ σ (C j)) :
    Intertwines ρ σ (∑ j ∈ s, C j) :=
  (intertwinerSubmodule ρ σ).sum_mem hC

/-- Conjugating an actual normal-subgroup intertwiner by a rational ambient point
preserves its actual subgroup equivariance, including on nonreduced tests. -/
theorem Intertwines.normalConjugate
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (i : H ⟶ G) [Mono i.hom.hom] (hN : (SubgroupFunctor.range i).IsNormal)
    {C : Matrix m n k} (hC : Intertwines (ρ.restrict i) (σ.restrict i) C)
    (g : rationalPoints G) :
    Intertwines (ρ.restrict i) (σ.restrict i)
      ((σ.rationalMatrix g : Matrix m m k) * C *
        (ρ.rationalMatrix g⁻¹ : Matrix n n k)) := by
  intro A x
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let U := σ.affineMatrix A (G.constantPoint g T)
  let V := ρ.affineMatrix A (G.constantPoint g T)
  let M := (ρ.restrict i).affineMatrix A x
  let N := (σ.restrict i).affineMatrix A x
  have hconst : G.constantPoint g⁻¹ T = (G.constantPoint g T)⁻¹ := by
    unfold constantPoint
    rw [GrpObj.comp_inv]
  have h₀ := hC A (x ≫ (SubgroupFunctor.normalInnerIso i hN g⁻¹).hom.hom.hom)
  rw [affineMatrix_restrict, affineMatrix_restrict,
    SubgroupFunctor.comp_normalInnerIso_hom_comp,
    hconst, map_mul, map_mul, map_inv, inv_inv,
    map_mul, map_mul, map_inv] at h₀
  have h : C.map (algebraMap k A) *
      ((V⁻¹ : GL n A) : Matrix n n A) * (M : Matrix n n A) *
        (V : Matrix n n A) =
    ((U⁻¹ : GL m A) : Matrix m m A) * (N : Matrix m m A) *
      (U : Matrix m m A) * C.map (algebraMap k A) := by
    dsimp only [M, N, U, V]
    rw [affineMatrix_restrict, affineMatrix_restrict]
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_assoc] using h₀
  have hUV : (U : Matrix m m A) * ((U⁻¹ : GL m A) : Matrix m m A) = 1 := by
    exact Units.mul_inv U
  have hVV : (V : Matrix n n A) * ((V⁻¹ : GL n A) : Matrix n n A) = 1 := by
    exact Units.mul_inv V
  have he :
      ((U : Matrix m m A) * C.map (algebraMap k A) *
        ((V⁻¹ : GL n A) : Matrix n n A)) * (M : Matrix n n A) =
      (N : Matrix m m A) * ((U : Matrix m m A) * C.map (algebraMap k A) *
        ((V⁻¹ : GL n A) : Matrix n n A)) := by
    calc
      _ = (U : Matrix m m A) *
          (C.map (algebraMap k A) * ((V⁻¹ : GL n A) : Matrix n n A) *
            (M : Matrix n n A) * (V : Matrix n n A)) *
          ((V⁻¹ : GL n A) : Matrix n n A) := by
        simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
      _ = (U : Matrix m m A) *
          (((U⁻¹ : GL m A) : Matrix m m A) * (N : Matrix m m A) *
            (U : Matrix m m A) * C.map (algebraMap k A)) *
          ((V⁻¹ : GL n A) : Matrix n n A) := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U : Matrix m m A)
          ((U⁻¹ : GL m A) : Matrix m m A), hUV, Matrix.one_mul]
  have hU : (σ.rationalMatrix g : Matrix m m k).map (algebraMap k A) =
      (U : Matrix m m A) := by
    exact (congrArg Units.val (σ.affineMatrix_constantPoint g A)).symm
  have hV : (ρ.rationalMatrix g⁻¹ : Matrix n n k).map (algebraMap k A) =
      ((V⁻¹ : GL n A) : Matrix n n A) := by
    have h' := congrArg Units.val (ρ.affineMatrix_constantPoint g⁻¹ A)
    change (ρ.affineMatrix A (G.constantPoint g⁻¹ T) : Matrix n n A) =
      (ρ.rationalMatrix g⁻¹ : Matrix n n k).map (algebraMap k A) at h'
    rw [hconst, map_inv] at h'
    exact h'.symm
  simpa only [Matrix.map_mul, hU, hV] using he

/-- Every finite linear combination of rational conjugates of an actual
normal-subgroup intertwiner is still an actual subgroup intertwiner. This is
the all-test preservation input for normalized quotient averaging. -/
theorem Intertwines.normalConjugate_sum
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (i : H ⟶ G) [Mono i.hom.hom] (hN : (SubgroupFunctor.range i).IsNormal)
    {C : Matrix m n k} (hC : Intertwines (ρ.restrict i) (σ.restrict i) C)
    {J : Type*} (s : Finset J) (g : J → rationalPoints G) (a : J → k) :
    Intertwines (ρ.restrict i) (σ.restrict i)
      (∑ j ∈ s, a j • ((σ.rationalMatrix (g j) : Matrix m m k) * C *
        (ρ.rationalMatrix (g j)⁻¹ : Matrix n n k))) := by
  apply intertwines_sum
  intro j _
  exact (hC.normalConjugate ρ σ i hN (g j)).smul (a j)

end Langlands.GroupScheme.MatrixRepresentation
