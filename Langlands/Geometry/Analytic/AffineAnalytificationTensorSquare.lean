import Langlands.Geometry.Analytic.AffineAnalytificationTensorLift
import Langlands.Geometry.Analytic.AffineAnalytificationFunctorialityStatement
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityStatement

/-! # Commutativity of the tensor-product analytification square -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w x

namespace Langlands.Analytic.AffineAnalytification.TensorLiftComparison

open CategoryTheory AffinoidAtlasPresentation TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {C : Type v} [CommRing C] [Algebra K C]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra C A] [IsScalarTower K C A]
  {B : Type x} [CommRing B] [Algebra K B] [Algebra C B] [IsScalarTower K C B]
  (PC : FinitePolynomialPresentation K C)
  (PA : FinitePolynomialPresentation K A) (PB : FinitePolynomialPresentation K B)
  (PT : FinitePolynomialPresentation K (A ⊗[C] B))

/-- The strong tensor-product square commutes by contravariant functoriality. -/
theorem strong_square
    (hFA : AffineAnalytificationFunctorialityStatement.{u, v, w, max w x})
    (hFB : AffineAnalytificationFunctorialityStatement.{u, v, x, max w x}) :
    (strongHom K PA PT (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B)).compOfDirected
        (strongHom K PC PA (IsScalarTower.toAlgHom K C A))
        (atlas_hasDirectedCharts K PA) (atlas_hasDirectedCharts K PC) =
      (strongHom K PB PT
          ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K)).compOfDirected
        (strongHom K PC PB (IsScalarTower.toAlgHom K C B))
        (atlas_hasDirectedCharts K PB) (atlas_hasDirectedCharts K PC) := by
  exact ((hFA K C A (A ⊗[C] B) PC PC PA PT _ _).2.1).symm.trans
    ((congrArg (fun f : C →ₐ[K] A ⊗[C] B =>
      (strongHom K PC PT f : StrongHom (presentation K PT) (presentation K PC)))
        (include_comp (K := K) (C := C) (A := A) (B := B))).trans
      (hFB K C B (A ⊗[C] B) PC PC PB PT _ _).2.1)

/-- The square commutes in the category of saturated atlas presentations. -/
theorem saturated_square
    (hFA : AffineAnalytificationLocalizedFunctorialityStatement.{u, v, w, max w x})
    (hFB : AffineAnalytificationLocalizedFunctorialityStatement.{u, v, x, max w x}) :
    saturatedHom K PA PT (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B) ≫
        saturatedHom K PC PA (IsScalarTower.toAlgHom K C A) =
      saturatedHom K PB PT
          ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K) ≫
        saturatedHom K PC PB (IsScalarTower.toAlgHom K C B) := by
  exact ((hFA K C A (A ⊗[C] B) PC PC PA PT _ _).2.1).symm.trans
    ((congrArg (fun f : C →ₐ[K] A ⊗[C] B =>
      (saturatedHom K PC PT f : saturated K PT ⟶ saturated K PC))
        (include_comp (K := K) (C := C) (A := A) (B := B))).trans
      (hFB K C B (A ⊗[C] B) PC PC PB PT _ _).2.1)

/-- The tensor-product square also commutes after localization. -/
theorem localized_square
    (hFA : AffineAnalytificationLocalizedFunctorialityStatement.{u, v, w, max w x})
    (hFB : AffineAnalytificationLocalizedFunctorialityStatement.{u, v, x, max w x}) :
    localizedHom K PA PT (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B) ≫
        localizedHom K PC PA (IsScalarTower.toAlgHom K C A) =
      localizedHom K PB PT
          ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).restrictScalars K) ≫
        localizedHom K PC PB (IsScalarTower.toAlgHom K C B) := by
  exact ((hFA K C A (A ⊗[C] B) PC PC PA PT _ _).2.2.2.1).symm.trans
    ((congrArg (fun f : C →ₐ[K] A ⊗[C] B =>
      (localizedHom K PC PT f : localized K PT ⟶ localized K PC))
        (include_comp (K := K) (C := C) (A := A) (B := B))).trans
      (hFB K C B (A ⊗[C] B) PC PC PB PT _ _).2.2.2.1)

end Langlands.Analytic.AffineAnalytification.TensorLiftComparison
