import Langlands.GroupScheme.Lie.ConjugationSemisimple
import Langlands.CommutativeAlgebra.DerivationBaseChange

/-! # Geometric eigenspaces for actual conjugation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  {n : Type} [Fintype n] [DecidableEq n]

/-- Representation-tested geometric semisimplicity applies to any finite
indexing type. -/
theorem IsSemisimpleElement.isGeometricallySemisimple_tangentMatrix
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (ρ : MatrixRepresentation G n) :
    IsGeometricallySemisimpleMatrix (ρ.tangentMatrix k X) := by
  let e := Fintype.equivFin n
  have h := hX _ (Chevalley.reindexRepresentation e (CommRingCat.of k) ρ)
  rw [MatrixRepresentation.tangentMatrix_reindex] at h
  change Module.End.IsSemisimple
    (Matrix.toLin' ((Matrix.reindex e e (ρ.tangentMatrix k X)).map
      (algebraMap k (AlgebraicClosure k)))) at h
  let E := LinearEquiv.funCongrLeft (AlgebraicClosure k) (AlgebraicClosure k) e.symm
  apply isSemisimple_of_injective_intertwiner E.toLinearMap E.injective _ h
  change E.toLinearMap ∘ₗ
      ((ρ.tangentMatrix k X).map (algebraMap k (AlgebraicClosure k))).mulVecLin =
    (Matrix.reindex e e
      ((ρ.tangentMatrix k X).map (algebraMap k (AlgebraicClosure k)))).mulVecLin ∘ₗ
        E.toLinearMap
  rw [Matrix.mulVecLin_reindex]
  apply LinearMap.ext
  intro v
  funext i
  change (((ρ.tangentMatrix k X).map (algebraMap k (AlgebraicClosure k))) *ᵥ v)
      (e.symm i) =
    (((ρ.tangentMatrix k X).map (algebraMap k (AlgebraicClosure k))) *ᵥ
      (fun j => v (e.symm (e j)))) (e.symm i)
  simp only [Equiv.symm_apply_apply]

variable [IsAffineHom G.X.hom]

/-- Coefficient sums after extending the coordinate algebra to the algebraic
closure. -/
def geometricCoefficientLinearMap (ρ : MatrixRepresentation G n) :
    (n × n → AlgebraicClosure k) →ₗ[AlgebraicClosure k]
      AlgebraicClosure k ⊗[k] coordinateAlgebra G :=
  Fintype.linearCombination (AlgebraicClosure k)
    (fun p : n × n =>
      (1 : AlgebraicClosure k) ⊗ₜ[k] representationCoefficients G ρ p.1 p.2)

/-- The scalar-extended coefficient map retains the actual conjugation
intertwiner. -/
theorem geometricCoefficientLinearMap_intertwines
    (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    geometricCoefficientLinearMap G ρ ∘ₗ
        (-Matrix.toLin' (((ρ.dual.tensor ρ).tangentMatrix k X).map
          (algebraMap k (AlgebraicClosure k)))) =
      (Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
        (conjugationDerivation G X)).toLinearMap ∘ₗ
          geometricCoefficientLinearMap G ρ := by
  apply (Pi.basisFun (AlgebraicClosure k) (n × n)).ext
  intro p
  have h := LinearMap.congr_fun (coefficientLinearMap_intertwines G ρ X)
    (Pi.basisFun k (n × n) p)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, Pi.basisFun_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one,
    coefficientLinearMap, Fintype.linearCombination_apply_single, one_smul] at h
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, Pi.basisFun_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one,
    geometricCoefficientLinearMap, Fintype.linearCombination_apply_single, one_smul]
  change _ = (1 : AlgebraicClosure k) ⊗ₜ[k]
    conjugationDerivation G X (representationCoefficients G ρ p.1 p.2)
  refine Eq.trans ?_
    (congrArg (fun a : coordinateAlgebra G => (1 : AlgebraicClosure k) ⊗ₜ[k] a) h)
  change (∑ q : n × n,
    -(algebraMap k (AlgebraicClosure k) ((ρ.dual.tensor ρ).tangentMatrix k X q p)) •
      ((1 : AlgebraicClosure k) ⊗ₜ[k] representationCoefficients G ρ q.1 q.2)) =
    (1 : AlgebraicClosure k) ⊗ₜ[k]
      (∑ q : n × n, (-((ρ.dual.tensor ρ).tangentMatrix k X q p)) •
        representationCoefficients G ρ q.1 q.2)
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [TensorProduct.tmul_smul]
  rw [← map_neg, IsScalarTower.algebraMap_smul (AlgebraicClosure k)]

/-- Extending a coefficient vector gives the corresponding pure tensor. -/
theorem geometricCoefficientLinearMap_algebraMap
    (ρ : MatrixRepresentation G n) (v : n × n → k) :
    geometricCoefficientLinearMap G ρ
        (fun p => algebraMap k (AlgebraicClosure k) (v p)) =
      (1 : AlgebraicClosure k) ⊗ₜ[k] coefficientLinearMap G ρ v := by
  change (∑ p : n × n, algebraMap k (AlgebraicClosure k) (v p) •
    ((1 : AlgebraicClosure k) ⊗ₜ[k] representationCoefficients G ρ p.1 p.2)) =
      (1 : AlgebraicClosure k) ⊗ₜ[k]
        (∑ p : n × n, v p • representationCoefficients G ρ p.1 p.2)
  rw [TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul (AlgebraicClosure k)]

/-- The geometric coefficient range is invariant under extended conjugation. -/
theorem geometricCoefficientLinearMap_range_invariant
    (ρ : MatrixRepresentation G n) (X : lieKernel G k) :
    ∀ y ∈ LinearMap.range (geometricCoefficientLinearMap G ρ),
      Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
        (conjugationDerivation G X) y ∈
          LinearMap.range (geometricCoefficientLinearMap G ρ) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨(-Matrix.toLin' (((ρ.dual.tensor ρ).tangentMatrix k X).map
      (algebraMap k (AlgebraicClosure k)))) v,
    LinearMap.congr_fun (geometricCoefficientLinearMap_intertwines G ρ X) v⟩

/-- Geometric semisimplicity of the actual dual-tensor representation descends
to the geometric coefficient range. -/
theorem IsSemisimpleElement.isSemisimple_geometricCoefficient_range
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (ρ : MatrixRepresentation G n) :
    Module.End.IsSemisimple
      ((Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
        (conjugationDerivation G X)).toLinearMap.restrict
          (geometricCoefficientLinearMap_range_invariant G ρ X)) := by
  apply isSemisimple_of_surjective_intertwiner
    (geometricCoefficientLinearMap G ρ).rangeRestrict
    (geometricCoefficientLinearMap G ρ).surjective_rangeRestrict
    (a := -Matrix.toLin' (((ρ.dual.tensor ρ).tangentMatrix k X).map
      (algebraMap k (AlgebraicClosure k))))
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (geometricCoefficientLinearMap_intertwines G ρ X) v
  · exact Module.End.isSemisimple_neg.mpr
      (hX.isGeometricallySemisimple_tangentMatrix G (ρ.dual.tensor ρ))

/-- A geometric coefficient range is contained in the span of the eigenspaces
of the extended conjugation derivation. -/
theorem IsSemisimpleElement.geometricCoefficient_range_le_eigenspaces
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (ρ : MatrixRepresentation G n) :
    LinearMap.range (geometricCoefficientLinearMap G ρ) ≤
      (⨆ a : AlgebraicClosure k, Module.End.eigenspace
        (Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
          (conjugationDerivation G X)).toLinearMap a) := by
  let V := LinearMap.range (geometricCoefficientLinearMap G ρ)
  let f := (Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
    (conjugationDerivation G X)).toLinearMap
  let hV := geometricCoefficientLinearMap_range_invariant G ρ X
  have hsem := hX.isSemisimple_geometricCoefficient_range G ρ
  calc
    V = (⊤ : Submodule (AlgebraicClosure k) V).map V.subtype := by simp
    _ = (⨆ a : AlgebraicClosure k,
        Module.End.eigenspace (f.restrict hV) a).map V.subtype := by
      rw [hsem.iSup_eigenspace_eq_top]
    _ = ⨆ a : AlgebraicClosure k,
        (Module.End.eigenspace (f.restrict hV) a).map V.subtype := by
      rw [Submodule.map_iSup]
    _ ≤ ⨆ a : AlgebraicClosure k, Module.End.eigenspace f a :=
      iSup_le fun a => (Module.End.eigenspace_restrict_le_eigenspace f hV a).trans
        (le_iSup _ a)

/-- After extension to an algebraic closure, the actual coordinate conjugation
derivation of a semisimple Lie element has spanning eigenspaces. -/
theorem IsSemisimpleElement.hasEigenDecomposition_conjugation_baseChange
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    Langlands.Algebra.SemisimpleDerivation.HasEigenDecomposition
      (Langlands.Algebra.SemisimpleDerivation.baseChange (AlgebraicClosure k)
        (conjugationDerivation G X)).toLinearMap := by
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul s c =>
    obtain ⟨N, ρ, hc⟩ := exists_representation_coefficient_span G c
    have hc' : c ∈ LinearMap.range (coefficientLinearMap G ρ) := by
      simpa only [coefficientLinearMap, Fintype.range_linearCombination] using hc
    obtain ⟨v, rfl⟩ := hc'
    have hp : (1 : AlgebraicClosure k) ⊗ₜ[k] coefficientLinearMap G ρ v ∈
        LinearMap.range (geometricCoefficientLinearMap G ρ) :=
      ⟨fun p => algebraMap k (AlgebraicClosure k) (v p),
        geometricCoefficientLinearMap_algebraMap G ρ v⟩
    have hs := (LinearMap.range (geometricCoefficientLinearMap G ρ)).smul_mem s hp
    apply hX.geometricCoefficient_range_le_eigenspaces G ρ
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hs
  | add z w hz hw => exact Submodule.add_mem _ hz hw

end Langlands.GroupScheme.Lie
