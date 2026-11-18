import Langlands.Geometry.Analytic.AffineAnalytificationChartAssembly
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSaturatedChartAssembly
import Langlands.Geometry.Analytic.AffineAnalytificationTensorSquare
import Langlands.Geometry.Analytic.LocalizedPullbackDescent

/-! # Affine analytification carries tensor products to fibre products -/

noncomputable section

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory ChartFamilyComparison SaturatedAtlasPresentation TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {C : Type v} [CommRing C] [Algebra K C]
  {A : Type w} [CommRing A] [Algebra K A] [Algebra C A] [IsScalarTower K C A]
  {B : Type x} [CommRing B] [Algebra K B] [Algebra C B] [IsScalarTower K C B]

/-- Take the relative tensor lift on every source chart. -/
private def tensorFamily {S : AffinoidAtlasPresentation.{u, u, u} K}
    (a : AlgebraFamily S A) (b : AlgebraFamily S B)
    (hab : ∀ i, (a.map i).comp (IsScalarTower.toAlgHom K C A) =
      (b.map i).comp (IsScalarTower.toAlgHom K C B)) :
    AlgebraFamily S (A ⊗[C] B) where
  map i := TensorLiftComparison.lift (a.map i) (b.map i) (hab i)
  naturality i j h := by
    apply TensorLiftComparison.lift_unique
    · rw [AlgHom.comp_assoc, TensorLiftComparison.lift_comp_includeLeft]
      exact a.naturality i j h
    · rw [AlgHom.comp_assoc, TensorLiftComparison.lift_comp_includeRight]
      exact b.naturality i j h

variable (PC : FinitePolynomialPresentation K C)
  (PA : FinitePolynomialPresentation K A) (PB : FinitePolynomialPresentation K B)
  (PT : FinitePolynomialPresentation K (A ⊗[C] B))

local notation "ιA" => (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[C] B)
local notation "ιB" => AlgHom.restrictScalars K (Algebra.TensorProduct.includeRight :
    B →ₐ[C] A ⊗[C] B)
local notation "cA" => (IsScalarTower.toAlgHom K C A)
local notation "cB" => (IsScalarTower.toAlgHom K C B)

/-- The strong pullback follows from reconstruction of the tensor-lift family. -/
private theorem tensor_isRefinedStrongPullback
    (realize : ∀ (S : SaturatedAtlasPresentation.{u, u, u} K)
      (d : AlgebraFamily S.presentation (A ⊗[C] B)),
      ∃ l : S ⟶ saturated K PT, ∀ i, (toAlgebraFamily PT l).map i = d.map i) :
    IsRefinedStrongPullback
      (saturatedHom K PA PT ιA) (saturatedHom K PB PT ιB)
      (saturatedHom K PC PA cA) (saturatedHom K PC PB cB) := by
  refine ⟨TensorLiftComparison.saturated_square PC PA PB PT
    affineAnalytificationLocalizedFunctoriality affineAnalytificationLocalizedFunctoriality,
    ?_, ?_⟩
  · intro S a b hab
    let aFamily := toAlgebraFamily PA a
    let bFamily := toAlgebraFamily PB b
    have h : ∀ i, (aFamily.map i).comp cA = (bFamily.map i).comp cB := by
      intro i
      have hi := congrArg (fun f : S ⟶ saturated K PC => (toAlgebraFamily PC f).map i) hab
      exact (toAlgebraFamily_comp_saturatedHom PC PA cA a i).symm.trans
        (hi.trans (toAlgebraFamily_comp_saturatedHom PC PB cB b i))
    obtain ⟨l, hl⟩ := realize S (tensorFamily aFamily bFamily h)
    refine ⟨S, 𝟙 S, quasiIsomorphisms.id_mem S, l, ?_, ?_⟩
    · rw [Category.id_comp]
      apply toAlgebraFamily_ext PA
      intro i
      rw [toAlgebraFamily_comp_saturatedHom PA PT ιA l i, hl i]
      exact TensorLiftComparison.lift_comp_includeLeft (aFamily.map i) (bFamily.map i) (h i)
    · rw [Category.id_comp]
      apply toAlgebraFamily_ext PB
      intro i
      rw [toAlgebraFamily_comp_saturatedHom PB PT ιB l i, hl i]
      exact TensorLiftComparison.lift_comp_includeRight (aFamily.map i) (bFamily.map i) (h i)
  · intro S l m ha hb
    apply toAlgebraFamily_ext PT
    intro i
    apply TensorLiftComparison.hom_ext
    · have hi := congrArg (fun f : S ⟶ saturated K PA => (toAlgebraFamily PA f).map i) ha
      exact (toAlgebraFamily_comp_saturatedHom PA PT ιA l i).symm.trans
        (hi.trans (toAlgebraFamily_comp_saturatedHom PA PT ιA m i))
    · have hi := congrArg (fun f : S ⟶ saturated K PB => (toAlgebraFamily PB f).map i) hb
      exact (toAlgebraFamily_comp_saturatedHom PB PT ιB l i).symm.trans
        (hi.trans (toAlgebraFamily_comp_saturatedHom PB PT ιB m i))

/-- Refined strong existence and uniqueness give the universal property for
arbitrary test objects in the localized category. -/
private theorem tensor_isPullback
    (realize : ∀ (S : SaturatedAtlasPresentation.{u, u, u} K)
      (d : AlgebraFamily S.presentation (A ⊗[C] B)),
      ∃ l : S ⟶ saturated K PT, ∀ i, (toAlgebraFamily PT l).map i = d.map i) :
    IsPullback (localizedHom K PA PT ιA) (localizedHom K PB PT ιB)
      (localizedHom K PC PA cA) (localizedHom K PC PB cB) :=
  (tensor_isRefinedStrongPullback PC PA PB PT realize).isPullback

/-- Affine analytification takes the relative tensor product to a pullback
in the localized category. -/
theorem affineAnalytificationFibreProduct :
    AffineAnalytificationFibreProductStatement.{u, v, w, x} := by
  intro K _ _ _ C _ _ A _ _ _ _ B _ _ _ _ PC PA PB PT
  apply tensor_isPullback PC PA PB PT
  intro S d
  let data := algebraFamilyData PT d
  exact ⟨saturatedChartHom PT data, fun i =>
    (toAlgebraFamily_saturatedChartHom PT data i).trans (algebraFamilyData_coordinate PT d i)⟩

end Langlands.Analytic.AffineAnalytification
