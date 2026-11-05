import Langlands.GroupScheme.MatrixRepresentationProductSmooth

/-! # The actual analytic differential of finite-product matrix representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped Classical Manifold ContDiff Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GeneralLinearProductDualNumber

variable {J : Type u} [Fintype J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

local instance factorMatrixComplete (j : J) : CompleteSpace (Matrix (n j) (n j) B) :=
  inferInstanceAs (CompleteSpace (n j → n j → B))

omit [NormedAlgebra ℝ B] in
/-- The original topology identifies invertible matrix families with an open
subset of all matrix families. -/
theorem isOpenEmbedding_matrixValues :
    IsOpenEmbedding (fun g : ∀ j, GL (n j) B => fun j => (g j : Matrix (n j) (n j) B)) :=
  .piMap (fun _ => Units.isOpenEmbedding_val)

/-- The actual finite family units chart. Its target is the open subset where
every component matrix is invertible. -/
def matrixUnitsChart : OpenPartialHomeomorph (∀ j, GL (n j) B)
    (∀ j, Matrix (n j) (n j) B) :=
  isOpenEmbedding_matrixValues.toOpenPartialHomeomorph _

local instance matrixFamilyChartedSpace :
    ChartedSpace (∀ j, Matrix (n j) (n j) B) (∀ j, GL (n j) B) :=
  isOpenEmbedding_matrixValues.singletonChartedSpace

private theorem contMDiff_matrixProjection (j : J) :
    ContMDiff 𝓘(ℝ, ∀ j, Matrix (n j) (n j) B)
      𝓘(ℝ, Matrix (n j) (n j) B) ∞ (fun g : ∀ j, GL (n j) B => g j) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact (ContinuousLinearMap.proj j : (∀ j, Matrix (n j) (n j) B) →L[ℝ]
    Matrix (n j) (n j) B).contDiff.contMDiff.comp
      (contMDiff_isOpenEmbedding isOpenEmbedding_matrixValues)

end Langlands.GroupScheme.GeneralLinearProductDualNumber

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinearProductDualNumber

variable {J : Type u} [Fintype J]
  {n : J → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  {R : CommRingCat.{u}}
  {B : Type u} [NormedCommRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [Algebra R B]
  {m : Type} [Fintype m] [DecidableEq m]
  (ρ : MatrixRepresentation (groupScheme n R) m)

local instance factorMatrixComplete (j : J) : CompleteSpace (Matrix (n j) (n j) B) :=
  inferInstanceAs (CompleteSpace (n j → n j → B))
local instance analyticOutputMatrixComplete : CompleteSpace (Matrix m m B) :=
  inferInstanceAs (CompleteSpace (m → m → B))
local instance matrixFamilyChartedSpace :
    ChartedSpace (∀ j, Matrix (n j) (n j) B) (∀ j, GL (n j) B) :=
  isOpenEmbedding_matrixValues.singletonChartedSpace

/-- The evaluated genuine scheme representation in the actual open units
chart. Values outside the chart target play no role in its differential. -/
def productMatrixCoordinateExtension (A : ∀ j, Matrix (n j) (n j) B) : Matrix m m B :=
  ρ.productMatrixPointsHom B ((matrixUnitsChart (n := n) (B := B)).symm A)

omit [NormedAlgebra ℝ B] in
@[simp]
theorem productMatrixCoordinateExtension_apply (g : ∀ j, GL (n j) B) :
    ρ.productMatrixCoordinateExtension (fun j => (g j : Matrix (n j) (n j) B)) =
      (ρ.productMatrixPointsHom B g : Matrix m m B) := by
  simp only [productMatrixCoordinateExtension, matrixUnitsChart,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- The actual extension is real smooth on the open set of invertible families. -/
theorem productMatrixCoordinateExtension_contDiffOn :
    ContDiffOn ℝ ∞ ρ.productMatrixCoordinateExtension
      (Set.range (fun g : ∀ j, GL (n j) B => fun j => (g j : Matrix (n j) (n j) B))) := by
  have h := ρ.contMDiff_productMatrixPointsHom
    𝓘(ℝ, ∀ j, Matrix (n j) (n j) B) id contMDiff_matrixProjection
  have hval := Units.contMDiff_val.comp h
  exact (hval.comp_contMDiffOn
    (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ, ∀ j, Matrix (n j) (n j) B))
      isOpenEmbedding_matrixValues)).contDiffOn

theorem productMatrixCoordinateExtension_contDiffAt (g : ∀ j, GL (n j) B) :
    ContDiffAt ℝ ∞ ρ.productMatrixCoordinateExtension
      (fun j => (g j : Matrix (n j) (n j) B)) :=
  ρ.productMatrixCoordinateExtension_contDiffOn.contDiffAt
    (isOpenEmbedding_matrixValues.isOpen_range.mem_nhds ⟨g, rfl⟩)

/-- The real analytic differential at the identity of the actual scheme-point
matrix homomorphism, constructed using its genuine open units chart. -/
def analyticProductDifferential :
    (∀ j, Matrix (n j) (n j) B) →L[ℝ] Matrix m m B :=
  fderiv ℝ ρ.productMatrixCoordinateExtension 1

/-- This is an actual Fréchet derivative, not only the total `fderiv` operator. -/
theorem hasFDerivAt_analyticProductDifferential :
    HasFDerivAt (𝕜 := ℝ) (ρ.productMatrixCoordinateExtension (B := B))
      (ρ.analyticProductDifferential (B := B)) 1 :=
  (ρ.productMatrixCoordinateExtension_contDiffAt (B := B) 1).differentiableAt
    (by simp) |>.hasFDerivAt

omit [NormedAlgebra ℝ B] in
@[simp]
theorem productMatrixCoordinateExtension_one :
    ρ.productMatrixCoordinateExtension (B := B) 1 = 1 := by
  change ρ.productMatrixCoordinateExtension
    (fun j => (1 : Matrix (n j) (n j) B)) = (1 : Matrix m m B)
  have h := ρ.productMatrixCoordinateExtension_apply (B := B) 1
  simpa only [Pi.one_apply, Units.val_one, map_one] using h

/-- Any ambient extension agreeing on actual invertible families has the same
derivative. No regularity away from those families is required. -/
theorem analyticProductDifferential_eq_of_extension
    (f : (∀ j, Matrix (n j) (n j) B) → Matrix m m B)
    (hf : ∀ g : ∀ j, GL (n j) B,
      f (fun j => (g j : Matrix (n j) (n j) B)) =
        (ρ.productMatrixPointsHom B g : Matrix m m B)) :
    ρ.analyticProductDifferential (B := B) = fderiv ℝ f 1 := by
  have heq : ρ.productMatrixCoordinateExtension (B := B) =ᶠ[𝓝 1] f := by
    filter_upwards [isOpenEmbedding_matrixValues.isOpen_range.mem_nhds
      (show (1 : ∀ j, Matrix (n j) (n j) B) ∈
        Set.range (fun g : ∀ j, GL (n j) B => fun j => (g j : Matrix (n j) (n j) B))
        from ⟨1, rfl⟩)] with A hA
    obtain ⟨g, rfl⟩ := hA
    rw [ρ.productMatrixCoordinateExtension_apply, hf]
  exact heq.fderiv_eq

/-- The genuine trivial representation has zero analytic differential. -/
@[simp]
theorem analyticProductDifferential_trivial :
    (trivial (groupScheme n R) m).analyticProductDifferential (B := B) = 0 := by
  rw [analyticProductDifferential_eq_of_extension _ (fun _ => 1)]
  · exact fderiv_const_apply (𝕜 := ℝ) (c := (1 : Matrix m m B)) (x := 1)
  · intro g
    rw [productMatrixPointsHom_apply, trivial_affineMatrix]
    rfl

end Langlands.GroupScheme.MatrixRepresentation
