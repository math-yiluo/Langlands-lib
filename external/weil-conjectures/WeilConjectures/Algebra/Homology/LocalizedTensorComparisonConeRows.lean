/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.TensorConeFiveTermExact
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyTriangleRows
import WeilConjectures.Algebra.Homology.TensorCoefficientConeBoundary
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated

/-! # Exact tensor-comparison rows for a chain-level mapping cone

Source: Stacks Project, Tags 06Y6, 0BYJ and 0DJA(1).
(blueprint: lem-pc-localized-tensor-comparison-cone-rows).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two cohomology rows for a chain map and its actual mapping cone
have an exact source row, and the coefficient comparison commutes with all
four row arrows.
The first, second and fourth target arrows are the homology maps of the chain
map and the cone inclusion; its connecting arrow is the homology boundary of the
concrete extended and tensored triangle.

Source: Stacks Project, Tags 06Y6 (exact derived tensor), 0BYJ (associativity)
and 0DJA(1) (canonical tensor comparison); the parent diagram proof, steps 2--4.

Proof: tensor the cone triangle of f with Q, restrict to R, and apply derived
extension to B. The fixed-second-factor derived tensor functor is exact. The
commuting A-action makes its cohomology sequence E=A tensor_R B-linear. Identify
these objects with the cohomology of the three prescribed universal models:
uniqueness of the derived counit fixes these identifications, including their
A-actions and comparison maps. Extend to C. Flatness of C over E preserves
exactness, giving s0,s1,s2,s3 and the first displayed exact row.
Extend the original cone triangle from A to C. Additive scalar extension
commutes with the mapping cone, and tensoring with arbitrary N gives another
cone triangle. The homology boundary of this concrete triangle gives d2; the other target
maps are precisely the displayed homology maps. Target exactness is proved
separately in `tensorConeTriangle_five_term_exact`. The scalar-extension unit,
derived counit, monoidal tensorator and t
commute with f and the cone inclusion by naturality. On the cone's P2 and
shifted P1 summands they commute with projection as well: the same Koszul sign
occurs on both sides. Thus taking homology gives the four displayed squares,
including the connecting square. This argument concerns an actual chain map
and its cone, not unrelated exact rows or arbitrary derived representatives.
Zero rings, zero maps, split cones and unbounded complexes require no changes.
(blueprint: lem-pc-localized-tensor-comparison-cone-rows). -/
theorem exists_localizedTensorComparison_cone_rows
    (hC : Module.Flat (A ⊗[R] B) C)
    (P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ) (f : P₁ ⟶ P₂)
    (m₁ : BaseDerivedTensorCohomologyModel R A B (P₁ ⊗ Q) C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B (P₂ ⊗ Q) C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B (CochainComplex.mappingCone f ⊗ Q) C)
    (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let E := extendScalars (algebraMap (A ⊗[R] B) C)
    let P₃ := CochainComplex.mappingCone f
    let cmp := fun (V : CochainComplex (ModuleCat.{u} A) ℤ)
      (m : BaseDerivedTensorCohomologyModel R A B (V ⊗ Q) C) (j : ℤ) ↦
        m.localizedComparison j ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)) j
    let d₀ := HomologicalComplex.homologyMap (F.map f ▷ N) i
    let d₁ := HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f) ▷ N) i
    let d₂ := CochainComplex.homologyδOfTriangle
      (tensorConeTriangle
        ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))) f N) i (i + 1)
    let d₃ := HomologicalComplex.homologyMap (F.map f ▷ N) (i + 1)
    ∃ (s₀ : E.obj (m₁.cohomology i) ⟶ E.obj (m₂.cohomology i))
      (s₁ : E.obj (m₂.cohomology i) ⟶ E.obj (m₃.cohomology i))
      (s₂ : E.obj (m₃.cohomology i) ⟶ E.obj (m₁.cohomology (i + 1)))
      (s₃ : E.obj (m₁.cohomology (i + 1)) ⟶ E.obj (m₂.cohomology (i + 1))),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ cmp P₂ m₂ i = cmp P₁ m₁ i ≫ d₀ ∧
      s₁ ≫ cmp P₃ m₃ i = cmp P₂ m₂ i ≫ d₁ ∧
      s₂ ≫ cmp P₁ m₁ (i + 1) = cmp P₃ m₃ i ≫ d₂ ∧
      s₃ ≫ cmp P₂ m₂ (i + 1) = cmp P₁ m₁ (i + 1) ≫ d₃ := by
  dsimp only
  let ρ := (algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B))
  let F := (extendScalars ρ).mapHomologicalComplex (.up ℤ)
  let H := (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.obj Q
  let T := H.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let a := fun V ↦ (Functor.Monoidal.μIso F V Q).inv ≫ (F.obj V ◁ t)
  have hT : DerivedCategory.Q.mapTriangle.obj T ∈
      Pretriangulated.distinguishedTriangles := by
    let e : T ≅ CochainComplex.mappingCone.triangle (f ▷ Q) :=
      CochainComplex.map₂CochainComplexFlipObjMapMappingConeTriangleIso
        (curriedTensor (ModuleCat.{u} A)) f Q
    exact Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (f ▷ Q)) _
      (DerivedCategory.Q.mapTriangle.mapIso e)
  obtain ⟨s₀, s₁, s₂, s₃, hs, w₀, w₁, w₂, w₃⟩ :=
    exists_baseDerivedTensorCohomologyModel_triangle_rows
      R A B C hC T hT m₁ m₂ m₃ i
  change s₀ ≫ m₂.localizedComparison i = m₁.localizedComparison i ≫
    HomologicalComplex.homologyMap (F.map (f ▷ Q)) i at w₀
  change s₁ ≫ m₃.localizedComparison i = m₂.localizedComparison i ≫
    HomologicalComplex.homologyMap (F.map (CochainComplex.mappingCone.inr f ▷ Q)) i at w₁
  change s₃ ≫ m₂.localizedComparison (i + 1) = m₁.localizedComparison (i + 1) ≫
    HomologicalComplex.homologyMap (F.map (f ▷ Q)) (i + 1) at w₃
  have naturality {U V : CochainComplex (ModuleCat.{u} A) ℤ} (g : U ⟶ V) (j : ℤ) :
      HomologicalComplex.homologyMap (F.map (g ▷ Q)) j ≫
          HomologicalComplex.homologyMap (a V) j =
        HomologicalComplex.homologyMap (a U) j ≫
          HomologicalComplex.homologyMap (F.map g ▷ N) j := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    dsimp only [a]
    symm
    rw [Category.assoc, whisker_exchange, ← Category.assoc]
    change (Functor.OplaxMonoidal.δ F U Q ≫ F.map g ▷ F.obj Q) ≫ _ = _
    rw [Functor.OplaxMonoidal.δ_natural_left]
    rfl
  have boundary := tensorCoefficient_cone_boundary A C ρ Q N t P₁ P₂ f i
  refine ⟨s₀, s₁, s₂, s₃, hs, ?_, ?_, ?_, ?_⟩
  · change s₀ ≫ (m₂.localizedComparison i ≫ _) = _
    rw [← Category.assoc, w₀, Category.assoc, naturality f i, Category.assoc]
  · change s₁ ≫ (m₃.localizedComparison i ≫ _) = _
    rw [← Category.assoc, w₁, Category.assoc,
      naturality (CochainComplex.mappingCone.inr f) i, Category.assoc]
  · change s₂ ≫ (m₁.localizedComparison (i + 1) ≫ _) = _
    rw [← Category.assoc, w₂, Category.assoc, boundary, Category.assoc]
  · change s₃ ≫ (m₂.localizedComparison (i + 1) ≫ _) = _
    rw [← Category.assoc, w₃, Category.assoc, naturality f (i + 1), Category.assoc]

end ModuleCat
