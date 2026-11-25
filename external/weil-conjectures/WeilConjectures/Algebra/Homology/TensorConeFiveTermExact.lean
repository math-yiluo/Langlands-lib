/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated

/-! # Exact cohomology of the extended and tensored cone triangle

Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-tensor-cone-five-term-exact).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable {A C : Type u} [CommRing A] [CommRing C]
  (ρ : A →+* C) {P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ}
  (f : P₁ ⟶ P₂) (N : CochainComplex (ModuleCat.{u} C) ℤ)

/-- The concrete triangle obtained by scalar extension and tensoring the cone triangle.
Source: Stacks Project, Tag 06Y6.
(blueprint: lem-pc-tensor-cone-five-term-exact). -/
noncomputable def tensorConeTriangle :
    Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} C) ℤ) :=
  (((extendScalars ρ).mapHomologicalComplex (.up ℤ)).mapTriangle ⋙
    ((curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj N).mapTriangle).obj
      (CochainComplex.mappingCone.triangle f)

/-- The five consecutive homology terms of the extended and tensored cone are exact.
Source: Stacks Project, Tag 06Y6.

Proof: an additive scalar-extension functor identifies the image of a mapping-cone
triangle with the cone of the extended chain map. Tensoring with N identifies this
triangle with the cone of the tensored map. These are chain isomorphisms, so no
flatness of the ring map or N is necessary. The cone triangle is distinguished;
its long exact homology sequence is exact at each of the three interior terms.
Truncate it after the second term in degree i+1.
(blueprint: lem-pc-tensor-cone-five-term-exact). -/
theorem tensorConeTriangle_five_term_exact (i : ℤ) :
    let T := tensorConeTriangle ρ f N
    (ComposableArrows.mk₄ (HomologicalComplex.homologyMap T.mor₁ i)
      (HomologicalComplex.homologyMap T.mor₂ i)
      (CochainComplex.homologyδOfTriangle T i (i + 1))
      (HomologicalComplex.homologyMap T.mor₁ (i + 1))).Exact := by
  let : HasDerivedCategory (ModuleCat.{u} C) := HasDerivedCategory.standard _
  let F := (extendScalars ρ).mapHomologicalComplex (.up ℤ)
  let H := (curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj N
  let T := tensorConeTriangle ρ f N
  let e : T ≅ CochainComplex.mappingCone.triangle (F.map f ▷ N) :=
    H.mapTriangle.mapIso (CochainComplex.mappingCone.mapTriangleIso f (extendScalars ρ)) ≪≫
      CochainComplex.map₂CochainComplexFlipObjMapMappingConeTriangleIso
        (curriedTensor (ModuleCat.{u} C)) (F.map f) N
  have hT : DerivedCategory.Q.mapTriangle.obj T ∈
      Pretriangulated.distinguishedTriangles :=
    Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (F.map f ▷ N)) _
      (DerivedCategory.Q.mapTriangle.mapIso e)
  exact ComposableArrows.exact_of_δ₀
    (CochainComplex.homologyMap_exact₂_of_distTriang T hT i).exact_toComposableArrows
    (ComposableArrows.exact_of_δ₀
      (CochainComplex.homologyMap_exact₃_of_distTriang T hT i (i + 1)).exact_toComposableArrows
      (CochainComplex.homologyMap_exact₁_of_distTriang T hT i (i + 1)).exact_toComposableArrows)

end ModuleCat
