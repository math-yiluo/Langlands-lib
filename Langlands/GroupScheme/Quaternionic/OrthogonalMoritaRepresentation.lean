import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpaceUniversal
import Langlands.GroupScheme.OrthogonalMatrix.Basic
import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # A Morita comparison retaining the actual row representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {m : Type} [Fintype m] [DecidableEq m]

/-- The actual inverse-right action on the tensor extension of the row module. -/
def isometryTensorRowAction (q : σ.QuadraticForms m)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (a : (σ.isometryGroup q).affinePoints R) :
    Module.End R (R ⊗[K] (m → D)) :=
  (TensorProduct.piRight K R R (fun _ : m => D)).symm.toLinearMap.comp
    (((σ.isometryRowActionOver q R a).restrictScalars R).comp
      (TensorProduct.piRight K R R (fun _ : m => D)).toLinearMap)

theorem piRight_isometryTensorRowAction (q : σ.QuadraticForms m)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (a : (σ.isometryGroup q).affinePoints R) (z : R ⊗[K] (m → D)) :
    TensorProduct.piRight K R R (fun _ : m => D)
        (σ.isometryTensorRowAction q R a z) =
      σ.isometryRowActionOver q R a
        (TensorProduct.piRight K R R (fun _ : m => D) z) :=
  (TensorProduct.piRight K R R (fun _ : m => D)).apply_symm_apply _

end FirstKindInvolution

namespace OrthogonalMorita

variable {K L D : Type u} [Field K] [Field L] [Algebra K L]
  [DivisionRing D] [Algebra K D]
  {m n degree : ℕ}

/-- Extend a fixed comparison of row modules over `L` canonically to every
commutative coefficient `L`-algebra. -/
def rowEquivOver
    (e : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)))
    (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] :
    R ⊗[K] (Fin m → D) ≃ₗ[R] (Fin degree → (Fin n ⊕ Fin n → R)) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange K L R R (Fin m → D)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R) e ≪≫ₗ
      TensorProduct.piRight L R R (fun _ : Fin degree => Fin n ⊕ Fin n → L) ≪≫ₗ
        LinearEquiv.piCongrRight (fun _ =>
          TensorProduct.piRight L R R (fun _ : Fin n ⊕ Fin n => L) ≪≫ₗ
            LinearEquiv.piCongrRight (fun _ => TensorProduct.AlgebraTensorModule.rid L R R))

theorem rowEquivOver_tmul
    (e : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)))
    (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (r : R) (v : Fin m → D) (j : Fin degree) (x : Fin n ⊕ Fin n) :
    rowEquivOver e R (r ⊗ₜ[K] v) j x =
      algebraMap L R (e ((1 : L) ⊗ₜ[K] v) j x) * r := by
  simp [rowEquivOver, Algebra.smul_def]

/-- The extended comparison commutes with every coefficient-algebra map. -/
theorem rowEquivOver_naturality
    (e : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)))
    {R S : Type u} [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    [CommRing S] [Algebra K S] [Algebra L S] [IsScalarTower K L S]
    (φ : R →ₐ[L] S) (z : R ⊗[K] (Fin m → D)) :
    rowEquivOver e S
        (TensorProduct.map (φ.restrictScalars K).toLinearMap (LinearMap.id) z) =
      fun j x => φ (rowEquivOver e R z j x) := by
  induction z with
  | tmul r v =>
    funext j x
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      rowEquivOver_tmul, map_mul, AlgHom.commutes]
    rfl
  | add z w hz hw =>
    simp only [_root_.map_add, hz, hw, Pi.add_apply]
    rfl

variable [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  (q : σ.QuadraticForms (Fin m))

/-- Read an original isometry point in the split orthogonal group through
an actual isomorphism after base change. -/
def splitPoint
    (iota : (GroupScheme.baseChange (Spec.algebraMap K L)).obj (σ.isometryGroup q) ≅
      OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))
    (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
    (a : (σ.isometryGroup q).affinePoints (CommAlgCat.of (CommRingCat.of K) R)) :
    (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).affinePoints
      (CommAlgCat.of (CommRingCat.of L) R) :=
  affinePointsBaseChangeMulEquiv K L R (σ.isometryGroup q) a ≫ iota.hom.hom.hom

end OrthogonalMorita

open OrthogonalMorita

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {m : ℕ} (q : σ.QuadraticForms (Fin m))
  (L : Type u) [Field L] [Algebra K L] (degree n : ℕ)

/-- A group-scheme Morita comparison together with an identification of the
actual extended row representation with `degree` copies of inverse-right
row multiplication on the split orthogonal module. -/
structure OrthogonalMoritaComparison where
  groupIso : (GroupScheme.baseChange (Spec.algebraMap K L)).obj (σ.isometryGroup q) ≅
    OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)
  rowEquiv : L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L))
  intertwines :
    ∀ (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]
      (a : (σ.isometryGroup q).affinePoints (CommAlgCat.of (CommRingCat.of K) R))
      (z : R ⊗[K] (Fin m → D)),
      rowEquivOver rowEquiv R
          (σ.isometryTensorRowAction q (CommAlgCat.of (CommRingCat.of K) R) a z) =
        fun j => Matrix.vecMul (rowEquivOver rowEquiv R z j)
          ((MatrixRepresentation.affineMatrix
            (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
            (CommAlgCat.of (CommRingCat.of L) R)
            (splitPoint σ q groupIso R a))⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

end Langlands.GroupScheme.Quaternionic
