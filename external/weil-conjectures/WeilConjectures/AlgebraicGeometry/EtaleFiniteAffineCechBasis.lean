/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Finite affine covers for the étale Čech criterion
Source: Stacks Project, Tags 0218 and 03F9.
(blueprint: new-etale-finite-affine-cech-basis).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The finite affine covering families over affine objects of the small étale site.
Source: Stacks Project, Tag 03F9; the collection used in the affine Tag 03P2 proof.
(blueprint: new-etale-finite-affine-cech-basis). -/
def finiteAffineEtaleCechCover (X : Scheme.{u}) (U : X.Etale)
    (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U) : Prop :=
  IsAffine U.left ∧ Finite I ∧ (∀ i : I, IsAffine (V i).left) ∧
    Sieve.ofArrows V f ∈ X.smallEtaleTopology U

/-- Finite affine covers form a fibre-product-stable cofinal collection over affine objects.
Source: Stacks Project, Topologies Tag 0218; Schemes Tags 01I4 and 01JQ;
Cohomology on Sites Tag 03F9, hypotheses (1) and (2).
(blueprint: new-etale-finite-affine-cech-basis)

Proof: a finite fibre product of affine schemes over an affine scheme is affine,
by the tensor-product description of affine fibre products; apply this repeatedly
in the over category to obtain every indicated product. For cofinality, regard
the original family as a jointly surjective étale cover of U. Every member is
covered by affine opens, whose maps to U are étale and open. Their images cover U.
The affine scheme U is quasi-compact, so finitely many of these images cover U.
Use their affine opens as W, with their original structure maps to X. Each map
to U factors through a member of the original cover. This also handles empty U:
the empty finite family is a covering and all nonempty iterated products are affine. -/
theorem finiteAffineEtaleCechCover_basis (X : Scheme.{u}) :
    (∀ (U : X.Etale) (I : Type (u + 1)) (V : I → X.Etale)
      (f : ∀ i : I, V i ⟶ U), finiteAffineEtaleCechCover X U I V f →
      IsAffine U.left ∧ (∀ i : I, IsAffine (V i).left) ∧
      ∀ (p : ℕ) (a : Fin (p + 1) → I),
        IsAffine (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left.left) ∧
    (∀ (U : X.Etale), IsAffine U.left →
      ∀ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i : I, V i ⟶ U),
        Sieve.ofArrows V f ∈ X.smallEtaleTopology U →
        ∃ (K : Type (u + 1)) (W : K → X.Etale) (g : ∀ k : K, W k ⟶ U),
          finiteAffineEtaleCechCover X U K W g ∧
            ∀ k : K, ∃ (i : I) (t : W k ⟶ V i), t ≫ f i = g k) := by
  classical
  constructor
  · intro U I V f hf
    refine ⟨hf.1, hf.2.2.1, ?_⟩
    intro p a
    let D := Discrete.functor (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))
    let c := (Over.ConstructProducts.conesEquiv U D).inverse.obj (limit.cone D)
    have hc : IsLimit c := IsLimit.ofRightAdjoint
      (Over.ConstructProducts.conesEquiv U D).toAdjunction (limit.isLimit D)
    let S := Etale.forget X ⋙ Over.forget X
    let : ∀ j, IsAffine
        (((Over.ConstructProducts.widePullbackDiagramOfDiagramOver U D) ⋙ S).obj j) := by
      intro j
      cases j with
      | none => exact hf.1
      | some j => exact hf.2.2.1 (a j)
    exact Scheme.isAffine_of_isLimit (S.mapCone c) (isLimitOfPreserves S hc)
  · intro U hU I V f hf
    let : IsAffine U.left := hU
    have hc : ∀ x : U.left, ∃ i y, (f i).left y = x := by
      intro x
      have hx : x ∈ ⋃ i, Set.range (f i).left := by
        rw [(ofArrows_mem_smallEtaleTopology_iff f).mp hf]
        trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hx
    let C : U.left.Cover (Scheme.precoverage @AlgebraicGeometry.Etale) :=
      Cover.mkOfCovers I (fun i ↦ (V i).left) (fun i ↦ (f i).left) hc
    let : QuasiCompactCover C.toPreZeroHypercover :=
      QuasiCompactCover.of_isOpenMap (fun i ↦ (C.f i).isOpenMap)
    obtain ⟨A, t, hfinite, _⟩ := QuasiCompactCover.exists_hom C
    let : Finite A.I₀ := hfinite
    let : ∀ k, AlgebraicGeometry.Etale (A.f k) := A.map_prop
    let W : A.I₀ → X.Etale := fun k ↦ Etale.mk (A.f k ≫ U.hom)
    let g : ∀ k, W k ⟶ U := fun k ↦ MorphismProperty.Over.homMk (A.f k)
    refine ⟨A.I₀, W, g, ⟨hU, hfinite, fun k ↦ ?_, ?_⟩, ?_⟩
    · change IsAffine (Spec (A.X k))
      infer_instance
    · rw [ofArrows_mem_smallEtaleTopology_iff]
      exact A.cover.iUnion_range
    · intro k
      refine ⟨t.s₀ k, MorphismProperty.Over.homMk (t.h₀ k) ?_, ?_⟩
      · change t.h₀ k ≫ (V (t.s₀ k)).hom = A.f k ≫ U.hom
        rw [← MorphismProperty.Over.w (f (t.s₀ k)), ← Category.assoc]
        exact congrArg (fun z ↦ z ≫ U.hom) (t.w₀ k)
      · apply MorphismProperty.Over.Hom.ext
        exact t.w₀ k

end AlgebraicGeometry.Scheme
