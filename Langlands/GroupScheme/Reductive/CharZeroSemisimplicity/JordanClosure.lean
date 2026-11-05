import Langlands.GroupScheme.Lie.TranslationJordan
import Langlands.GroupScheme.Lie.TangentSemisimplicity

/-! # Jordan semisimple parts of tangent matrices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped Matrix

namespace Langlands.LinearAlgebra

variable {k : Type*} [Field k] [PerfectField k]
  {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The Jordan semisimple part of a product endomorphism is the product of the
Jordan semisimple parts. -/
theorem jordanSemisimplePart_prodMap (f : End k V) (g : End k W) :
    jordanSemisimplePart (f.prodMap g) =
      (jordanSemisimplePart f).prodMap (jordanSemisimplePart g) := by
  have h₁ := jordanSemisimplePart_intertwines (f := f) (g := f.prodMap g)
    (LinearMap.inl k V W) (by ext <;> simp)
  have h₂ := jordanSemisimplePart_intertwines (f := g) (g := f.prodMap g)
    (LinearMap.inr k V W) (by ext <;> simp)
  apply LinearMap.prod_ext
  · rw [h₁]
    ext <;> simp
  · rw [h₂]
    ext <;> simp

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.MatrixRepresentation

open Lie Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]

/-- Reindexing a square matrix intertwines the two linear maps through the
coordinate change. -/
theorem toLin'_reindex_comp_funLeft {m : Type} [Fintype m] [DecidableEq m] (e : n ≃ m)
    (M : Matrix n n k) :
    (Matrix.toLin' (Matrix.reindex e e M)).comp (LinearMap.funLeft k k e.symm) =
      (LinearMap.funLeft k k e.symm).comp (Matrix.toLin' M) := by
  apply LinearMap.ext
  intro v
  change (M.submatrix e.symm e.symm) *ᵥ (v ∘ e.symm) = (M *ᵥ v) ∘ e.symm
  have hv : (v ∘ e.symm) ∘ e.symm.symm = v := by
    ext x
    simp
  rw [Matrix.submatrix_mulVec_equiv M (v ∘ e.symm) e.symm e.symm, hv]

variable [PerfectField k] [IsAffineHom G.X.hom]

/-- For every finite coordinate index, the tangent matrix of the semisimple
component of a Lie-kernel element is the Jordan semisimple part of its tangent
matrix. -/
theorem toLin'_tangentMatrix_semisimpleKernel (ρ : MatrixRepresentation G n)
    (X : lieKernel G k) :
    Matrix.toLin' (ρ.tangentMatrix k (semisimpleKernel G X)) =
      jordanSemisimplePart (Matrix.toLin' (ρ.tangentMatrix k X)) := by
  let e := Fintype.equivFin n
  let ρ₀ := Chevalley.reindexRepresentation e (CommRingCat.of k) ρ
  have h₀ := tangentMatrix_semisimpleKernel ρ₀ X
  rw [tangentMatrix_reindex, tangentMatrix_reindex] at h₀
  let T := LinearMap.funLeft k k e.symm
  have hT : Function.Injective T :=
    LinearMap.funLeft_injective_of_surjective _ _ _ e.symm.surjective
  have hint := jordanSemisimplePart_intertwines T
    (toLin'_reindex_comp_funLeft e (ρ.tangentMatrix k X))
  rw [← h₀, toLin'_reindex_comp_funLeft] at hint
  apply LinearMap.ext
  intro v
  exact hT (LinearMap.congr_fun hint v)

end Langlands.GroupScheme.MatrixRepresentation
