import Langlands.GroupScheme.Lie.AdjointDifferentialCentralizer
import Langlands.GroupScheme.Lie.ActionBaseChange
import Langlands.LinearAlgebra.NonnilpotentLocus

/-! # Scalar extension of the actual adjoint differential -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The standard finite-coordinate comparison after scalar extension. -/
def coordinateTensorEquiv (d : ℕ) :
    K ⊗[k] (Fin d → k) ≃ₗ[K] (Fin d → K) :=
  ((Pi.basisFun k (Fin d)).baseChange K).equivFun

@[simp]
theorem coordinateTensorEquiv_tmul {d : ℕ} (a : K) (v : Fin d → k) :
    coordinateTensorEquiv (k := k) d (a ⊗ₜ[k] v) =
      fun i => a * algebraMap k K (v i) := by
  ext i
  simp [coordinateTensorEquiv, Algebra.smul_def, mul_comm]

/-- The coordinate comparison intertwines a scalar-extended matrix operator. -/
theorem coordinateTensorEquiv_baseChange {d : ℕ} (M : Matrix (Fin d) (Fin d) k)
    (w : K ⊗[k] (Fin d → k)) :
    coordinateTensorEquiv (k := k) d ((Matrix.toLin' M).baseChange K w) =
      Matrix.toLin' (M.map (algebraMap k K))
        (coordinateTensorEquiv (k := k) d w) := by
  induction w using TensorProduct.inductionOn with
  | tmul a v =>
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {d : ℕ} (c : FiniteCoordinates G d)

local instance adjointDifferentialBaseChangeKernelCommGroup : CommGroup (lieKernel G k) := lieKernelCommGroup G
local instance adjointDifferentialBaseChangeKernelModule : Module k (Additive (lieKernel G k)) := lieKernelModule G

/-- Simultaneous scalar extension of the adjoint family is the actual
coefficient-extended tangent matrix, through standard target coordinates. -/
theorem adjointDifferentialFamily_scalarExtension
    (z : K ⊗[k] Additive (lieKernel G k)) (w : K ⊗[k] (Fin d → k)) :
    coordinateTensorEquiv (k := k) d
        (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) K z w) =
      Matrix.toLin' ((adjointRepresentation c).tangentMatrix K
        (kernelScalarExtension G K z).toMul)
        (coordinateTensorEquiv (k := k) d w) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearAlgebra.endomorphismFamilyBaseChange, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearMap.tensorProduct,
      TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul,
      LinearMap.coe_restrictScalars, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, LinearMap.baseChangeHom_apply,
      kernelScalarExtension_tmul]
    change coordinateTensorEquiv (k := k) d
        (a • (Matrix.toLin' ((adjointRepresentation c).tangentMatrix k x.toMul)).baseChange K w) =
      Matrix.toLin' ((adjointRepresentation c).tangentMatrix K
        (lieKernelScale G a (lieKernelMap G (Algebra.ofId k K) x.toMul)))
        (coordinateTensorEquiv (k := k) d w)
    rw [map_smul, coordinateTensorEquiv_baseChange,
      MatrixRepresentation.tangentMatrix_scale,
      MatrixRepresentation.tangentMatrix_naturality]
    simp only [map_smul, LinearMap.smul_apply]
    rfl
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]
    change _ = Matrix.toLin' ((adjointRepresentation c).tangentMatrix K
      ((kernelScalarExtension G K x).toMul * (kernelScalarExtension G K y).toMul)) _
    rw [MatrixRepresentation.tangentMatrix_mul, map_add, LinearMap.add_apply]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

local instance adjointDifferentialBaseChangeAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual adjoint actions have identical matrices in pulled-back coordinates. -/
theorem adjointRepresentation_baseChange_affineAction
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (g : AffinePoints G_K A) (v : Fin d → A) :
    (adjointRepresentation (c.baseChange k K)).affineAction (.of (CommRingCat.of K) A) g v =
      (adjointRepresentation c).affineAction (.of (CommRingCat.of k) A)
        (affineBaseChangeEquiv k K G A g) v := by
  have hA : ‹Algebra k A› = Algebra.compHom A (algebraMap k K) := by
    apply Algebra.algebra_ext
    intro r
    exact congrArg (fun f : k →+* A => f r) (IsScalarTower.algebraMap_eq k K A)
  cases hA
  let : Algebra k A := Algebra.compHom A (algebraMap k K)
  let : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨x, rfl⟩ := ((c.baseChange k K).equiv (.of (CommRingCat.of K) A)).surjective v
  rw [adjointRepresentation_affineAction]
  change c.equiv (.of (CommRingCat.of k) A)
      (kernelBaseChangeLinearEquiv k K G A (adjoint G_K A g x)) =
    (adjointRepresentation c).affineAction (.of (CommRingCat.of k) A)
      (affineBaseChangeEquiv k K G A g)
      (c.equiv (.of (CommRingCat.of k) A) (kernelBaseChangeLinearEquiv k K G A x))
  rw [kernelBaseChangeLinearEquiv_adjoint, adjointRepresentation_affineAction]

omit [LocallyOfFiniteType G.X.hom] in
/-- Tangent matrices of the actual adjoint representation agree under scheme pullback. -/
theorem adjointRepresentation_baseChange_tangentMatrix (X : lieKernel G_K K) :
    (adjointRepresentation (c.baseChange k K)).tangentMatrix K X =
      (adjointRepresentation c).tangentMatrix K (kernelBaseChangeEquiv k K G K X) := by
  have hm : (adjointRepresentation (c.baseChange k K)).affineMatrix
        (.of (CommRingCat.of K) (DualNumber K)) X.val =
      (adjointRepresentation c).affineMatrix
        (.of (CommRingCat.of k) (DualNumber K))
        (affineBaseChangeEquiv k K G (DualNumber K) X.val) := by
    apply Units.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact adjointRepresentation_baseChange_affineAction c X.val v
  rw [MatrixRepresentation.affineMatrix_lieKernel] at hm
  change GeneralLinear.DualNumber.matrixUnit _ =
    (adjointRepresentation c).affineMatrix (.of (CommRingCat.of k) (DualNumber K))
      (kernelBaseChangeEquiv k K G K X).val at hm
  rw [MatrixRepresentation.affineMatrix_lieKernel] at hm
  simpa only [GeneralLinear.DualNumber.coefficients_matrixUnit] using
    congrArg GeneralLinear.DualNumber.coefficients hm

/-- The scalar-extended family is conjugate to the actual extended tangent matrix. -/
theorem coordinateTensorEquiv_conj_adjointDifferentialFamily
    (z : K ⊗[k] Additive (lieKernel G k)) :
    (coordinateTensorEquiv (k := k) d).conjRingEquiv
        (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) K z) =
      Matrix.toLin' ((adjointRepresentation c).tangentMatrix K
        (kernelScalarExtension G K z).toMul) := by
  apply LinearMap.ext
  intro v
  change coordinateTensorEquiv (k := k) d
    (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) K z
      ((coordinateTensorEquiv (k := k) d).symm v)) = _
  rw [adjointDifferentialFamily_scalarExtension, LinearEquiv.apply_symm_apply]

/-- A nonnilpotent adjoint differential on the actual scheme pullback gives a
nonnilpotent member of the scalar-extended ground-field family. -/
theorem not_isNilpotent_adjointFamilyBaseChange
    {X : lieKernel G_K K}
    (hX : ¬ IsNilpotent
      (adjointDifferentialFamily (c.baseChange k K) (Additive.ofMul X))) :
    ¬ IsNilpotent
      (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) K
        ((kernelScalarExtension G K).symm
          (kernelBaseChangeLinearEquiv k K G K (Additive.ofMul X)))) := by
  intro hn
  have h := hn.map (coordinateTensorEquiv (k := k) d).conjRingEquiv
  rw [coordinateTensorEquiv_conj_adjointDifferentialFamily,
    LinearEquiv.apply_symm_apply] at h
  apply hX
  change IsNilpotent (Matrix.toLin'
    ((adjointRepresentation (c.baseChange k K)).tangentMatrix K X))
  rw [adjointRepresentation_baseChange_tangentMatrix]
  exact h

local instance adjointDifferentialBaseChangeLocallyOfFiniteType : LocallyOfFiniteType (G_K).X.hom := by
  change LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A geometric noncentral semisimple element supplies a nonnilpotent extended
member of the ground-field actual adjoint family. -/
theorem exists_nonnilpotent_adjointFamilyBaseChange
    (hgeo : ∃ X : lieKernel G_K K, IsSemisimpleElement G_K X ∧
      elementCentralizerLie G_K X ≠ ⊤) :
    ∃ z : K ⊗[k] Additive (lieKernel G k),
      ¬ IsNilpotent
        (LinearAlgebra.endomorphismFamilyBaseChange (adjointDifferentialFamily c) K z) := by
  obtain ⟨X, hX, hproper⟩ := hgeo
  exact ⟨(kernelScalarExtension G K).symm
    (kernelBaseChangeLinearEquiv k K G K (Additive.ofMul X)),
    not_isNilpotent_adjointFamilyBaseChange c
      (not_isNilpotent_adjointDifferential_of_semisimple (c.baseChange k K) hX hproper)⟩

/-- A geometric noncentral semisimple element gives a polynomial ground-field
locus on which the actual adjoint differential is nonnilpotent. -/
theorem exists_polynomial_nonnilpotent_adjoint_locus
    (b : Basis (Fin d) k (Additive (lieKernel G k)))
    (hgeo : ∃ X : lieKernel G_K K, IsSemisimpleElement G_K X ∧
      elementCentralizerLie G_K X ≠ ⊤) :
    ∃ p : MvPolynomial (Fin d) k, p ≠ 0 ∧
      ∀ X : lieKernel G k, MvPolynomial.eval (b.repr (Additive.ofMul X)) p ≠ 0 →
        ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X)) := by
  obtain ⟨p, hp, hdet⟩ := LinearAlgebra.exists_polynomial_nonnilpotent_locus
    (adjointDifferentialFamily c) b (exists_nonnilpotent_adjointFamilyBaseChange c hgeo)
  exact ⟨p, hp, fun X => hdet (Additive.ofMul X)⟩

/-- Over an infinite ground field, a geometric noncentral semisimple element
forces the actual nonnilpotent adjoint locus to be nonempty and span the Lie module. -/
theorem nonnilpotent_adjoint_locus_spans_of_geometric_semisimple [Infinite k]
    (hgeo : ∃ X : lieKernel G_K K, IsSemisimpleElement G_K X ∧
      elementCentralizerLie G_K X ≠ ⊤) :
    (∃ X : lieKernel G k, ¬ IsNilpotent (adjointDifferentialFamily c (Additive.ofMul X))) ∧
      Submodule.span k {x : Additive (lieKernel G k) |
        ¬ IsNilpotent (adjointDifferentialFamily c x)} = ⊤ := by
  let b : Basis (Fin d) k (Additive (lieKernel G k)) :=
    (Pi.basisFun k (Fin d)).map (c.equiv (.of (CommRingCat.of k) k)).symm
  obtain ⟨hex, hspan⟩ := LinearAlgebra.nonnilpotent_locus_spans_of_baseChange
    (adjointDifferentialFamily c) b (exists_nonnilpotent_adjointFamilyBaseChange c hgeo)
  exact ⟨by obtain ⟨x, hx⟩ := hex; exact ⟨x.toMul, hx⟩, hspan⟩

end Langlands.GroupScheme.Lie
