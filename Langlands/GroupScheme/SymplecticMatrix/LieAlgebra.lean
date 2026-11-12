import Langlands.GroupScheme.SymplecticMatrix.Reductive
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.Functoriality

/-! # Matrix coordinates on the Lie algebra of the split symplectic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Dual-number symplectic matrices -/

section DualNumber

open GeneralLinear.DualNumber

variable {A : Type u} [CommRing A]

omit [Fintype l] in
theorem J_dualNumber :
    Matrix.J l (DualNumber A) = (Matrix.J l A).map (TrivSqZeroExt.inlHom A A) :=
  (Matrix.map_J l _).symm

/-- `(1 + εY) J (1 + εY)ᵀ = J + ε (Y J + J Yᵀ)`. -/
theorem one_add_epsilonMatrix_mul_J_mul_transpose (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    (1 + epsilonMatrix Y) * Matrix.J l (DualNumber A) * (1 + epsilonMatrix Y).transpose =
      Matrix.J l (DualNumber A) +
        epsilonMatrix (Y * Matrix.J l A + Matrix.J l A * Y.transpose) := by
  have hT : (epsilonMatrix Y).transpose = epsilonMatrix Y.transpose := rfl
  rw [J_dualNumber, Matrix.transpose_add, Matrix.transpose_one, hT]
  simp only [add_mul, mul_add, one_mul, mul_one, epsilonMatrix_mul_constantMatrix,
    constantMatrix_mul_epsilonMatrix, epsilonMatrix_mul, add_zero, epsilonMatrix_add]
  abel

omit [Fintype l] [DecidableEq l] in
theorem epsilonMatrix_eq_zero_iff (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    epsilonMatrix Y = 0 ↔ Y = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := congrArg (fun M : Matrix (l ⊕ l) (l ⊕ l) (DualNumber A) =>
      TrivSqZeroExt.snd (M i j)) h
    simpa using h1
  · rintro rfl
    exact epsilonMatrix_zero

/-- `1 + εY` is symplectic exactly when `Y J + J Yᵀ = 0`. -/
theorem one_add_epsilonMatrix_mem_iff (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    1 + epsilonMatrix Y ∈ Matrix.symplecticGroup l (DualNumber A) ↔
      Y * Matrix.J l A + Matrix.J l A * Y.transpose = 0 := by
  rw [SymplecticGroup.mem_iff, one_add_epsilonMatrix_mul_J_mul_transpose, add_eq_left,
    epsilonMatrix_eq_zero_iff]

end DualNumber

/-! ### Affine points -/

section AffinePoints

variable (l) (R : CommRingCat.{u})

/-- Points on affine test schemes are symplectic matrices over the test algebra. -/
def affinePointsEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ (groupScheme l R).X) ≃* Matrix.symplecticGroup l S :=
  Corepresented.affinePointsEquiv (functor l R) (corepresentableBy l R) S

variable {l R}

/-- Affine points are natural in the test algebra. -/
theorem affinePointsEquiv_naturality {S T : CommAlgCat.{u} R} (g : S ⟶ T)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme l R).X) :
    affinePointsEquiv l R T ((algSpec R).map g.op ≫ f) =
      map l g.hom.toRingHom (affinePointsEquiv l R S f) :=
  Corepresented.affinePointsEquiv_naturality _ _ g f

/-- On affine points, the inclusion into `GL_{l ⊕ l}` is the inclusion of matrices. -/
theorem affinePointsEquiv_inclusion (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme l R).X) :
    GeneralLinear.affinePointsEquiv (l ⊕ l) R S (f ≫ (inclusion l R).hom.hom) =
      toGL (affinePointsEquiv l R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

end AffinePoints

/-! ### Lie coordinates -/

section Lie

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- The matrix coordinates of the Lie algebra of `Sp`, through the inclusion into
`GL_{l ⊕ l}` and the published coordinates of the Lie algebra of `GL`. -/
def lieMatrix : Additive (lieKernel (groupScheme l R) A) →ₗ[A]
    Matrix (l ⊕ l) (l ⊕ l) A :=
  (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).symm.toLinearMap ∘ₗ
    Lie.targetMapLinear (inclusion l R) A

theorem pointKernelLinearEquiv_lieMatrix (X : Additive (lieKernel (groupScheme l R) A)) :
    pointKernelLinearEquiv (lieMatrix X) = Lie.targetMapLinear (inclusion l R) A X :=
  LinearEquiv.apply_symm_apply _ _

/-- The inclusion of `Sp` into `GL` is a monomorphism of schemes. -/
instance mono_inclusion : Mono (inclusion l R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (pointsEquiv l R Z).injective
  have h1 := congrArg (GeneralLinear.pointsEquiv (l ⊕ l) R Z) hgh
  rw [pointsEquiv_inclusion, pointsEquiv_inclusion] at h1
  apply Subtype.ext
  exact congrArg (fun g : GL (l ⊕ l) Γ(Z.left, ⊤) => g.val) h1

theorem lieMatrix_injective :
    Function.Injective (lieMatrix (l := l) (R := R) (A := A)) :=
  (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective (inclusion l R) A)

/-- The affine dual-number matrix of an element of the Lie kernel of `Sp` is `1 + εY` for
its coordinate matrix `Y`. -/
theorem affinePointsEquiv_lieKernel (X : Additive (lieKernel (groupScheme l R) A)) :
    ((affinePointsEquiv l R (CommAlgCat.of R (DualNumber A)) X.toMul.val :
        Matrix.symplecticGroup l (DualNumber A)) : Matrix (l ⊕ l) (l ⊕ l) (DualNumber A)) =
      1 + epsilonMatrix (lieMatrix X) := by
  have h1 := pointKernelLinearEquiv_lieMatrix X
  have h2 := congrArg (fun x : Additive (lieKernel (GeneralLinear.groupScheme (l ⊕ l) R) A) =>
    GeneralLinear.affinePointsEquiv (l ⊕ l) R (CommAlgCat.of R (DualNumber A)) x.toMul.val) h1
  simp only [pointKernelLinearEquiv_toMul, pointKernelEquiv_val, lieKernelHomLinear_val] at h2
  have h4 := affinePointsEquiv_inclusion (l := l) (R := R) (CommAlgCat.of R (DualNumber A))
    X.toMul.val
  have h5 := pointUnit_matrix (R := R) (lieMatrix X)
  have h6 := h4.symm.trans (h2.symm.trans h5)
  exact congrArg (fun g : GL (l ⊕ l) (DualNumber A) => g.val) h6

/-- The Lie algebra of `Sp` consists of matrices `Y` with `Y J + J Yᵀ = 0`. -/
theorem lieMatrix_mul_J_add (X : Additive (lieKernel (groupScheme l R) A)) :
    lieMatrix X * Matrix.J l A + Matrix.J l A * (lieMatrix X).transpose = 0 := by
  rw [← one_add_epsilonMatrix_mem_iff, ← affinePointsEquiv_lieKernel]
  exact (affinePointsEquiv l R (CommAlgCat.of R (DualNumber A)) X.toMul.val).property

/-- Conversely every matrix `Y` with `Y J + J Yᵀ = 0` is the coordinate matrix of an element of
the Lie algebra of `Sp`. -/
theorem exists_lieMatrix_eq (Y : Matrix (l ⊕ l) (l ⊕ l) A)
    (hY : Y * Matrix.J l A + Matrix.J l A * Y.transpose = 0) :
    ∃ X : Additive (lieKernel (groupScheme l R) A), lieMatrix X = Y := by
  let g : Matrix.symplecticGroup l (DualNumber A) :=
    ⟨1 + epsilonMatrix Y, (one_add_epsilonMatrix_mem_iff Y).mpr hY⟩
  let p := (affinePointsEquiv l R (CommAlgCat.of R (DualNumber A))).symm g
  have hp : p ≫ (inclusion l R).hom.hom = (pointUnit Y : GeneralLinear.DualNumber.AffinePoints
      (l ⊕ l) R (DualNumber A)) := by
    apply (GeneralLinear.affinePointsEquiv (l ⊕ l) R (CommAlgCat.of R (DualNumber A))).injective
    rw [affinePointsEquiv_inclusion, pointUnit_matrix]
    apply Units.ext
    change ((affinePointsEquiv l R _ p : Matrix.symplecticGroup l (DualNumber A)) :
      Matrix (l ⊕ l) (l ⊕ l) (DualNumber A)) = 1 + epsilonMatrix Y
    rw [MulEquiv.apply_symm_apply]
  have hred : Lie.reduction (groupScheme l R) p = 1 := by
    apply (cancel_mono (inclusion l R).hom.hom).mp
    rw [MonObj.one_comp]
    have h : Lie.reduction (groupScheme l R) p ≫ (inclusion l R).hom.hom =
        Lie.reduction (GeneralLinear.groupScheme (l ⊕ l) R) (p ≫ (inclusion l R).hom.hom) :=
      Category.assoc _ _ _
    rw [h, hp]
    exact pointReduction_pointUnit Y
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  apply (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).injective
  rw [pointKernelLinearEquiv_lieMatrix]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

end Lie

end Langlands.GroupScheme.SymplecticMatrix
