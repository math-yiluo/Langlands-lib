/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryTriangleRows
import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.Algebra.Homology.ScalarCoefficientTriangleBoundary

/-! # Universal base-change counits on distinguished triangles

Source: Stacks Project, Tag 06Y6, exactness and independence of derived change of rings.
(blueprint: lem-pc-base-derived-tensor-cohomology-triangle-rows). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct
namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
private theorem extend_exact_row
    {E C : Type u} [CommRing E] [CommRing C] (g : E →+* C)
    [Limits.PreservesFiniteLimits (extendScalars.{u, u, u} g)]
    {X₀ X₁ X₂ X₃ X₄ : ModuleCat.{u} E}
    (s₀ : X₀ ⟶ X₁) (s₁ : X₁ ⟶ X₂) (s₂ : X₂ ⟶ X₃) (s₃ : X₃ ⟶ X₄)
    (h : (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact) :
    (ComposableArrows.mk₄ ((extendScalars g).map s₀) ((extendScalars g).map s₁)
      ((extendScalars g).map s₂) ((extendScalars g).map s₃)).Exact := by
  let F := extendScalars.{u, u, u} g
  have h₀ := (h.exact 0).map F
  have h₁ := (h.exact 1).map F
  have h₂ := (h.exact 2).map F
  apply ComposableArrows.exact_of_δ₀
  · exact ComposableArrows.exact₂_mk _ _ h₀
  · apply ComposableArrows.exact_of_δ₀
    · exact ComposableArrows.exact₂_mk _ _ h₁
    · exact ComposableArrows.exact₂_mk _ _ h₂

set_option backward.isDefEq.respectTransparency false in
private theorem transpose_square
    {E C : Type u} [CommRing E] [CommRing C] (g : E →+* C)
    {M N X Y : ModuleCat.{u} E} {XL YL : ModuleCat.{u} C}
    (s : M ⟶ N) (a : M ⟶ X) (b : N ⟶ Y) (t : X ⟶ Y)
    (kX : X ⟶ (restrictScalars g).obj XL) (kY : Y ⟶ (restrictScalars g).obj YL)
    (aL : (extendScalars g).obj M ⟶ XL) (bL : (extendScalars g).obj N ⟶ YL)
    (tL : XL ⟶ YL)
    (ha : (extendRestrictScalarsAdj g).unit.app M ≫ (restrictScalars g).map aL = a ≫ kX)
    (hb : (extendRestrictScalarsAdj g).unit.app N ≫ (restrictScalars g).map bL = b ≫ kY)
    (hab : s ≫ b = a ≫ t)
    (hk : t ≫ kY = kX ≫ (restrictScalars g).map tL) :
    (extendScalars g).map s ≫ bL = aL ≫ tL := by
  let adj := extendRestrictScalarsAdj g
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  change s ≫ (adj.unit.app N ≫ (restrictScalars g).map bL) =
    (adj.unit.app M ≫ (restrictScalars g).map aL) ≫ (restrictScalars g).map tL
  rw [ha, hb, ← Category.assoc, hab, Category.assoc, hk, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
private theorem coefficient_naturality
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ Q)
    (M : BaseDerivedTensorCohomologyModel R A B P C)
    (N : BaseDerivedTensorCohomologyModel R A B Q C) :
    let E := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let G := (restrictScalars.{u} (algebraMap (A ⊗[R] B) C)).mapHomologicalComplex (.up ℤ)
    E.map f ≫ N.ordinaryToLocalized = M.ordinaryToLocalized ≫ G.map (F.map f) := by
  dsimp only
  apply HomologicalComplex.Hom.ext
  funext j
  apply ExtendScalars.hom_ext
  intro q
  change N.ordinaryToLocalized.f j
      ((extendScalars (algebraMap A (A ⊗[R] B))).map (f.f j)
        ((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q)) =
    (extendScalars ((algebraMap (A ⊗[R] B) C).comp
      (algebraMap A (A ⊗[R] B)))).map (f.f j)
        (M.ordinaryToLocalized.f j ((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] q))
  rw [ExtendScalars.map_tmul, N.ordinaryToLocalized_tmul, M.ordinaryToLocalized_tmul,
    ExtendScalars.map_tmul]


set_option backward.isDefEq.respectTransparency false in
private theorem localized_arrow_square
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    {P Q : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ Q)
    (M : BaseDerivedTensorCohomologyModel R A B P C)
    (N : BaseDerivedTensorCohomologyModel R A B Q C) (i : ℤ)
    (s : M.cohomology i ⟶ N.cohomology i)
    (hs : s ≫ N.comparison i = M.comparison i ≫ HomologicalComplex.homologyMap
      (((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).map f) i) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    (extendScalars (algebraMap (A ⊗[R] B) C)).map s ≫ N.localizedComparison i =
      M.localizedComparison i ≫ HomologicalComplex.homologyMap (F.map f) i := by
  dsimp only
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let J := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let G := restrictScalars.{u} (algebraMap (A ⊗[R] B) C)
  apply transpose_square (algebraMap (A ⊗[R] B) C) s (M.comparison i) (N.comparison i)
    (HomologicalComplex.homologyMap (J.map f) i)
    (HomologicalComplex.homologyMap M.ordinaryToLocalized i ≫
      (((F.obj P).sc i).mapHomologyIso G).hom)
    (HomologicalComplex.homologyMap N.ordinaryToLocalized i ≫
      (((F.obj Q).sc i).mapHomologyIso G).hom)
    (M.localizedComparison i) (N.localizedComparison i)
    (HomologicalComplex.homologyMap (F.map f) i)
    (M.localized_eq i) (N.localized_eq i) hs
  have h := congrArg (fun k ↦ HomologicalComplex.homologyMap k i)
    (coefficient_naturality R A B C f M N)
  simp only [HomologicalComplex.homologyMap_comp] at h
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map (F.map f)) G
  rw [← Category.assoc, h, Category.assoc]
  change HomologicalComplex.homologyMap
      ((G.mapHomologicalComplex (.up ℤ)).map (F.map f)) i ≫
        (((F.obj Q).sc i).mapHomologyIso G).hom =
      (((F.obj P).sc i).mapHomologyIso G).hom ≫
        G.map (HomologicalComplex.homologyMap (F.map f) i) at hn
  simpa only [Category.assoc] using
    congrArg (fun k ↦ HomologicalComplex.homologyMap M.ordinaryToLocalized i ≫ k) hn

/-- Universal base-change models give an exact localized row and a morphism to the
ordinary extended triangle's homology row. No tensor coefficient complex is involved.

Source: Stacks Project, Tag 06Y6 (exact derived change of rings and universal counit).
Proof: restrict T to R and apply the exact derived extension functor to B. Identify
its three cohomology objects with the prescribed models by uniqueness of left derived
functors, with the counit commuting under these identifications. Naturality at
multiplication by each a in A identifies the A-actions. B-linearity and tensor
induction therefore make all three sequence maps A tensor_R B-linear. Restriction
of scalars is exact and reflects exactness, so the resulting five-term row is exact.
Extend this row to C; flatness preserves exactness. The universal counit commutes
with shifts and sends the third triangle map to the ordinary third triangle map.
Its naturality gives the first, second and fourth squares; shift compatibility and
naturality of the homology shift isomorphism give the boundary square. Transpose
these squares under extension/restriction adjunction; comparison_eq and localized_eq
identify their vertical arrows with the specified localizedComparison maps. This
construction uses only a distinguished localized triangle, not termwise exactness
of its scalar extension. Zero rings and unbounded or zero complexes are included.
(blueprint: lem-pc-base-derived-tensor-cohomology-triangle-rows). -/
theorem exists_baseDerivedTensorCohomologyModel_triangle_rows
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (hC : Module.Flat (A ⊗[R] B) C)
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (hT : DerivedCategory.Q.mapTriangle.obj T ∈ Pretriangulated.distinguishedTriangles)
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₂ : BaseDerivedTensorCohomologyModel R A B T.obj₂ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let E := extendScalars (algebraMap (A ⊗[R] B) C)
    ∃ (s₀ : E.obj (m₁.cohomology i) ⟶ E.obj (m₂.cohomology i))
      (s₁ : E.obj (m₂.cohomology i) ⟶ E.obj (m₃.cohomology i))
      (s₂ : E.obj (m₃.cohomology i) ⟶ E.obj (m₁.cohomology (i + 1)))
      (s₃ : E.obj (m₁.cohomology (i + 1)) ⟶ E.obj (m₂.cohomology (i + 1))),
      (ComposableArrows.mk₄ s₀ s₁ s₂ s₃).Exact ∧
      s₀ ≫ m₂.localizedComparison i =
        m₁.localizedComparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₁) i ∧
      s₁ ≫ m₃.localizedComparison i =
        m₂.localizedComparison i ≫ HomologicalComplex.homologyMap (F.map T.mor₂) i ∧
      s₂ ≫ m₁.localizedComparison (i + 1) = m₃.localizedComparison i ≫
        CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1) ∧
      s₃ ≫ m₂.localizedComparison (i + 1) = m₁.localizedComparison (i + 1) ≫
        HomologicalComplex.homologyMap (F.map T.mor₁) (i + 1) := by
  dsimp only
  let E := extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let := preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr hC)
  obtain ⟨s₀, s₁, s₂, s₃, hex, h₀, h₁, h₂, h₃⟩ :=
    exists_baseDerivedTensorCohomologyModel_ordinary_triangle_rows R A B C T hT m₁ m₂ m₃ i
  refine ⟨E.map s₀, E.map s₁, E.map s₂, E.map s₃,
    extend_exact_row _ s₀ s₁ s₂ s₃ hex,
    localized_arrow_square R A B C T.mor₁ m₁ m₂ i s₀ h₀,
    localized_arrow_square R A B C T.mor₂ m₂ m₃ i s₁ h₁, ?_,
    localized_arrow_square R A B C T.mor₁ m₁ m₂ (i + 1) s₃ h₃⟩
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  let J := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let G := restrictScalars.{u} (algebraMap (A ⊗[R] B) C)
  apply transpose_square (algebraMap (A ⊗[R] B) C) s₂ (m₃.comparison i)
    (m₁.comparison (i + 1))
    (CochainComplex.homologyδOfTriangle (J.mapTriangle.obj T) i (i + 1))
    (HomologicalComplex.homologyMap m₃.ordinaryToLocalized i ≫
      (((F.obj T.obj₃).sc i).mapHomologyIso G).hom)
    (HomologicalComplex.homologyMap m₁.ordinaryToLocalized (i + 1) ≫
      (((F.obj T.obj₁).sc (i + 1)).mapHomologyIso G).hom)
    (m₃.localizedComparison i) (m₁.localizedComparison (i + 1))
    (CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1))
    (m₃.localized_eq i) (m₁.localized_eq (i + 1)) h₂
  exact scalarCoefficient_triangle_boundary (algebraMap A (A ⊗[R] B))
    (algebraMap (A ⊗[R] B) C) T m₁.ordinaryToLocalized m₃.ordinaryToLocalized
    m₁.ordinaryToLocalized_tmul m₃.ordinaryToLocalized_tmul i

end ModuleCat
