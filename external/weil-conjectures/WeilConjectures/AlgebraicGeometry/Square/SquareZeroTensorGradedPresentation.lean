/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedDegreeData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedKernelSquareZero

/-! # Algebraic graded presentation of the tensor ideal sequences

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum over degrees.
(blueprint: lem-sc-square-zero-tensor-graded-presentation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

/-- A graded algebra presentation, before taking cohomology. All its data are supplied
explicitly; this structure does not select an object from an existence theorem.
The kernel cofan expresses its graded direct sum, and the degree maps are projections.
Source: Stacks Project, Tag 09MS, the direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation). -/
structure TensorGradedPresentation {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  I : SheafOfModules.{u} (moduleRings X.toRingedSpace)
  i : I ⟶ commAlgebraSheafModule X.sheaf B
  hw : i ≫ tensorGradedAlgebraMap p = 0
  shortExact : (ShortComplex.mk i (tensorGradedAlgebraMap p)
    hw).ShortExact
  squareZero : ∀ (U : X.Opens) (a b : B.right.obj.obj (op U)),
    p.right.hom.app (op U) a = 0 → p.right.hom.app (op U) b = 0 → a * b = 0
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  k : ∀ d : ℕ,
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶ I
  degree : ∀ d : ℕ,
    ShortComplex.mk i (tensorGradedAlgebraMap p) hw ⟶
      ShortComplex.kernelSequence
        (tensorGradedUnit j (L.tensorPow d))
  q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf C ⟶
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d))
  degree_quotient : ∀ d : ℕ, (degree d).τ₃ = q d
  k_colimit : IsColimit (Cofan.mk I k)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  k_inclusion : ∀ d : ℕ, k d ≫ i = kernel.ι _ ≫ b d
  c_projection : ∀ d : ℕ, c d ≫ q d = 𝟙 _
  k_projection : ∀ d : ℕ, k d ≫ (degree d).τ₁ = 𝟙 _
  k_orthogonal : ∀ a d : ℕ, a ≠ d → k a ≫ (degree d).τ₁ = 0
  b_multiply : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
    (t : Γ(L.tensorPow d, U)),
    tensorGradedAlgebraSection B U ((b a).app U s) *
      tensorGradedAlgebraSection B U ((b d).app U t) =
      tensorGradedAlgebraSection B U
        ((b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))

/-- The algebraic and exact data underlying the graded presentation, before the
multiplication compatibility is imposed.
Source: Stacks Project, Tag 09MS, the direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-presentation-core). -/
structure TensorGradedPresentationCore {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) where
  B : X.CommAlgebraSheaf
  C : X.CommAlgebraSheaf
  p : B ⟶ C
  I : SheafOfModules.{u} (moduleRings X.toRingedSpace)
  i : I ⟶ commAlgebraSheafModule X.sheaf B
  hw : i ≫ tensorGradedAlgebraMap p = 0
  shortExact : (ShortComplex.mk i (tensorGradedAlgebraMap p) hw).ShortExact
  squareZero : ∀ (U : X.Opens) (a b : B.right.obj.obj (op U)),
    p.right.hom.app (op U) a = 0 → p.right.hom.app (op U) b = 0 → a * b = 0
  b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B
  c : ∀ d : ℕ,
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d)) ⟶
      commAlgebraSheafModule X.sheaf C
  k : ∀ d : ℕ,
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶ I
  degree : ∀ d : ℕ,
    ShortComplex.mk i (tensorGradedAlgebraMap p) hw ⟶
      ShortComplex.kernelSequence (tensorGradedUnit j (L.tensorPow d))
  q : ∀ d : ℕ, commAlgebraSheafModule X.sheaf C ⟶
    (pushforward j).obj ((tensorPullback j).obj (L.tensorPow d))
  degree_quotient : ∀ d : ℕ, (degree d).τ₃ = q d
  k_colimit : IsColimit (Cofan.mk I k)
  b_quotient : ∀ d : ℕ, b d ≫ tensorGradedAlgebraMap p =
    tensorGradedUnit j (L.tensorPow d) ≫ c d
  k_inclusion : ∀ d : ℕ, k d ≫ i = kernel.ι _ ≫ b d
  c_projection : ∀ d : ℕ, c d ≫ q d = 𝟙 _
  k_projection : ∀ d : ℕ, k d ≫ (degree d).τ₁ = 𝟙 _
  k_orthogonal : ∀ a d : ℕ, a ≠ d → k a ≫ (degree d).τ₁ = 0

/-- Assemble the canonical kernel data of a graded algebra quotient. -/
private def tensorGradedCore {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (A : TensorGradedAlgebraData j L)
    (D : TensorGradedDegreeData j L A)
    (hsq : ∀ (U : X.Opens) (a b : A.B.right.obj.obj (op U)),
      A.p.right.hom.app (op U) a = 0 → A.p.right.hom.app (op U) b = 0 → a * b = 0) :
    TensorGradedPresentationCore j L where
  B := A.B
  C := A.C
  p := A.p
  I := kernel (tensorGradedAlgebraMap A.p)
  i := kernel.ι (tensorGradedAlgebraMap A.p)
  hw := kernel.condition (tensorGradedAlgebraMap A.p)
  shortExact := D.shortExact
  squareZero := hsq
  b := A.b
  c := A.c
  k := D.k
  degree := D.degree
  q := D.q
  degree_quotient := D.degree_quotient
  k_colimit := D.k_colimit
  b_quotient := A.b_quotient
  k_inclusion := D.k_inclusion
  c_projection := D.c_projection
  k_projection := D.k_projection
  k_orthogonal := D.k_orthogonal

theorem tensorGradedPresentation_exists {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥) :
    Nonempty (TensorGradedPresentation j L) := by
  obtain ⟨A⟩ := tensorGradedAlgebraData_exists j L
  obtain ⟨D⟩ := tensorGradedDegreeData_exists j L A
  let T := tensorGradedCore j L A D (tensorGradedKernel_squareZero j L A hI)
  have m : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
      (t : Γ(L.tensorPow d, U)),
      tensorGradedAlgebraSection T.B U ((T.b a).app U s) *
        tensorGradedAlgebraSection T.B U ((T.b d).app U t) =
        tensorGradedAlgebraSection T.B U
          ((T.b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t))) :=
    A.b_multiply
  exact ⟨{
    B := T.B, C := T.C, p := T.p, I := T.I, i := T.i, hw := T.hw,
    shortExact := T.shortExact, squareZero := T.squareZero, b := T.b, c := T.c,
    k := T.k, degree := T.degree, q := T.q, degree_quotient := T.degree_quotient,
    k_colimit := T.k_colimit, b_quotient := T.b_quotient,
    k_inclusion := T.k_inclusion, c_projection := T.c_projection,
    k_projection := T.k_projection, k_orthogonal := T.k_orthogonal,
    b_multiply := m }⟩

end
end AlgebraicGeometry.Scheme.Modules
