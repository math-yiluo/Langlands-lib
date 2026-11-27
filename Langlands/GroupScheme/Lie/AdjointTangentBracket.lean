import Langlands.GroupScheme.Lie.AffineBracketAdjoint
import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.UnipotentTangent

/-! # The adjoint action at a dual-number point is the bracket, over every test algebra

For an affine group `G` of finite type over a field `k`, finite Lie coordinates `c` and a
`k`-algebra `A`, the coordinate matrix of `Ad` at a point `1 + ε y` of `G(A[ε])` is
`1 + ε N(y)`, and `N(y)` is the matrix of `ad y = ⁅y, ·⁆` on the Lie algebra over `A`. Over the
base field this is the Library's `adjointDifferentialLieHom_apply_bracket`; the general case
follows by scalar extension. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme.Lie

open GeneralLinear.DualNumber

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] {d : ℕ} (c : FiniteCoordinates G d)

local instance kernelLieRingOfField (A : Type u) [CommRing A] [Algebra k A] :
    LieRing (Additive (lieKernel G A)) :=
  instAffineKernelLieRing (R := CommRingCat.of k) G (A := A)

local instance kernelLieAlgebraOfField (A : Type u) [CommRing A] [Algebra k A] :
    LieAlgebra A (Additive (lieKernel G A)) :=
  instAffineKernelLieAlgebra (R := CommRingCat.of k) G (A := A)

set_option maxRecDepth 8192 in
/-- Over the base field, the tangent matrix of the coordinate adjoint representation at `y`
acts on coordinates as `ad y`. -/
theorem adjointKernelDifferential_mulVec_base
    (y x : Additive (lieKernel G (CommRingCat.of k))) :
    (adjointRepresentation c).kernelDifferential (CommRingCat.of k) y *ᵥ
        c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) x =
      c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
        (⁅y, x⁆ : Additive (lieKernel G (CommRingCat.of k))) :=
  adjointDifferentialLieHom_apply_bracket c y x

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The finite Lie coordinates over a `k`-algebra `A`, as an `A`-linear equivalence onto
`Fin d → A`. -/
def coordinateEquiv : Additive (lieKernel G A) ≃ₗ[A] (Fin d → A) :=
  c.equiv (CommAlgCat.of (CommRingCat.of k) A)

/-- Over every `k`-algebra `A`, the tangent matrix of the coordinate adjoint representation at
`y` acts on coordinates as `ad y`. -/
theorem adjointKernelDifferential_mulVec (y x : Additive (lieKernel G A)) :
    (adjointRepresentation c).kernelDifferential A y *ᵥ coordinateEquiv c A x =
      coordinateEquiv c A ⁅y, x⁆ := by
  have hK (y₀ : Additive (lieKernel G (CommRingCat.of k))) :
      (adjointRepresentation c).kernelDifferential A
          (lieKernelMapLinear G (Algebra.ofId k A) y₀) =
        ((adjointRepresentation c).kernelDifferential (CommRingCat.of k) y₀).map
          (algebraMap k A) := by
    rw [MatrixRepresentation.kernelDifferential_apply,
      MatrixRepresentation.kernelDifferential_apply, lieKernelMapLinear_toMul,
      (adjointRepresentation c).tangentMatrix_naturality]
    rfl
  have he (z : Additive (lieKernel G (CommRingCat.of k))) :
      coordinateEquiv c A (lieKernelMapLinear G (Algebra.ofId k A) z) = fun i => algebraMap k A
        (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) z i) :=
    c.naturality (A := CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
      (CommAlgCat.ofHom (Algebra.ofId k A)) z
  have hbase (y₀ x₀ : Additive (lieKernel G (CommRingCat.of k))) :
      (adjointRepresentation c).kernelDifferential A
          (lieKernelMapLinear G (Algebra.ofId k A) y₀) *ᵥ
        coordinateEquiv c A (lieKernelMapLinear G (Algebra.ofId k A) x₀) =
      coordinateEquiv c A (lieKernelMapLinear G (Algebra.ofId k A) ⁅y₀, x₀⁆) := by
    rw [hK, he, he, ← adjointKernelDifferential_mulVec_base c y₀ x₀]
    funext i
    exact (RingHom.map_mulVec (algebraMap k A) _ _ i).symm
  have hx (y₀ : Additive (lieKernel G (CommRingCat.of k))) (x : Additive (lieKernel G A)) :
      (adjointRepresentation c).kernelDifferential A
          (lieKernelMapLinear G (Algebra.ofId k A) y₀) *ᵥ coordinateEquiv c A x =
        coordinateEquiv c A ⁅lieKernelMapLinear G (Algebra.ofId k A) y₀, x⁆ := by
    obtain ⟨t, rfl⟩ := (kernelScalarExtension G A).surjective x
    induction t using TensorProduct.inductionOn with
    | tmul b x₀ =>
        rw [kernelScalarExtension_tmul, map_smul, Matrix.mulVec_smul, hbase, lie_smul,
          map_smul, lieKernelMapLinear_lie]
    | add t t' ht ht' =>
        rw [map_add, map_add, Matrix.mulVec_add, ht, ht', lie_add, map_add]
  obtain ⟨s, rfl⟩ := (kernelScalarExtension G A).surjective y
  induction s using TensorProduct.inductionOn with
  | tmul a y₀ =>
      rw [kernelScalarExtension_tmul, map_smul, Matrix.smul_mulVec, hx, smul_lie, map_smul]
  | add s s' hs hs' =>
      rw [map_add, map_add, Matrix.add_mulVec, hs, hs', add_lie, map_add]

omit [LocallyOfFiniteType G.X.hom] in
/-- The `ε`-part of the coordinate matrix of `Ad` at the dual-number point of `y` is the
tangent matrix of the coordinate adjoint representation at `y`. -/
theorem coordinateMatrix_conjugation_snd (y : lieKernel G A) :
    ((AutomorphicAction.conjugation (𝟙 G)).coordinateMatrix c
        (CommAlgCat.of (CommRingCat.of k) (DualNumber A)) y.val).val.map
          (TrivSqZeroExt.snd : DualNumber A → A) =
      (adjointRepresentation c).kernelDifferential A (Additive.ofMul y) := by
  rw [← AutomorphicAction.finiteRepresentation_affineMatrix]
  change ((adjointRepresentation c).affineMatrix _ y.val).val.map _ = _
  rw [affineMatrix_lieKernel_eq, matrixUnit_val, MatrixRepresentation.kernelDifferential_apply]
  ext i j
  simp [epsilonMatrix, Matrix.one_apply]
  split_ifs <;> simp

/-- The trace of `ad y` on the Lie algebra over `A` is the trace of the tangent matrix of the
coordinate adjoint representation at `y`. -/
theorem trace_toEnd_eq_trace_kernelDifferential (y : Additive (lieKernel G A)) :
    LinearMap.trace A (Additive (lieKernel G A))
        (LieModule.toEnd A (Additive (lieKernel G A)) (Additive (lieKernel G A)) y) =
      Matrix.trace ((adjointRepresentation c).kernelDifferential A y) := by
  classical
  let b := Module.Basis.ofEquivFun (coordinateEquiv c A)
  rw [LinearMap.trace_eq_matrix_trace A b]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply, LieModule.toEnd_apply_apply,
    ← adjointKernelDifferential_mulVec, Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_single_one, Matrix.col_apply]

end Langlands.GroupScheme.Lie
