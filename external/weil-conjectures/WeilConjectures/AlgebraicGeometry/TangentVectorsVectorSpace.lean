/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.DualNumberSchemePushout
import WeilConjectures.AlgebraicGeometry.TangentVectorsVectorSpaceCore
import WeilConjectures.AlgebraicGeometry.TangentVectorsVectorSpaceOperations

/-!
# The vector space of dual-number tangent vectors

Source: Stacks Project, Tag 0B2B, Lemma 33.16.2 and its proof, with base `Spec k`
(blueprint: lem-sc-tangent-space-vector-space).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The dual-number tangent vectors at a point of a scheme over a field form a vector space.
Source: Stacks Project, Tag 0B2B (blueprint: lem-sc-tangent-space-vector-space).

Proof:
1. Apply lem-sc-dual-number-scheme-pushout with `K = X.residueField x` and two copies.
   The coordinate projections identify the square-zero algebra with the fiber product of
   two dual-number rings over `K`. The local-ring description of maps into arbitrary schemes
   gives the scheme pushout. The two tangent vectors have the same restriction, so glue
   uniquely to `Θ`. Uniqueness with target `Spec k` shows that `Θ` is over `k`.
2. The sum map and each scaling map preserve the common closed point and the structure map
   to `Spec k`. Thus precomposition gives elements of the displayed subtype `T`. The map
   factoring through `Spec K` is the zero vector.
3. Apply the same pushout lemma to three copies for associativity: both parenthesizations
   send all three infinitesimals to epsilon. Swapping two coordinates gives commutativity.
   Gluing a vector with the constant map gives the original vector after precomposition.
   Gluing the two scalar multiples uses epsilon mapping to `λ ε₁ + μ ε₂`, proving scalar
   additivity. Scaling both coordinates proves distributivity over vector addition.
   Composition of scaling maps proves multiplicativity and the identity scalar law.
   Scaling by minus one supplies additive inverses, since epsilon then maps to zero.
   These identities give an additive commutative group and a `K`-module, with exactly the
   addition, scalar multiplication and zero described in the conclusion.
-/
theorem exists_tangentVectors_vectorSpace
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) :
    let K := X.residueField x
    let D := Spec (.of (DualNumber K))
    let E := Spec (.of (TrivSqZeroExt K (Fin 2 → K)))
    let b := X.fromSpecResidueField x
    let c : Spec K ⟶ D :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
    let q : D ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
    let r : E ⟶ Spec K :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K (Fin 2 → K)))
    let j : Fin 2 → (D ⟶ E) := fun i =>
      Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → K) →ₗ[K] K)).toRingHom)
    let s : D ⟶ E := Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K) + LinearMap.proj 1)).toRingHom)
    let m : K → (D ⟶ D) := fun t => Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (t • (LinearMap.id : K →ₗ[K] K))).toRingHom)
    let T := {θ : D ⟶ X // c ≫ θ = b ∧ θ ≫ p = q ≫ b ≫ p}
    IsPushout c c (j 0) (j 1) ∧
      (∀ θ₁ θ₂ : T, ∃! Θ : E ⟶ X, j 0 ≫ Θ = θ₁.val ∧ j 1 ≫ Θ = θ₂.val) ∧
      (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
        j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → Θ ≫ p = r ≫ b ≫ p) ∧
      (∃ a : AddCommGroup T, letI := a;
        ∃ v : Module K T, letI := v;
          (0 : T).val = q ≫ b ∧
          (∀ θ₁ θ₂ : T, ∀ Θ : E ⟶ X,
            j 0 ≫ Θ = θ₁.val → j 1 ≫ Θ = θ₂.val → (θ₁ + θ₂).val = s ≫ Θ) ∧
          (∀ (t : K) (θ : T), (t • θ).val = m t ≫ θ.val)) := by
  dsimp
  have hc := tangentVectors_core k X p x
  have ho := tangentVectors_operations k X p x
  rcases hc with ⟨hpush, huniq, hover⟩
  rcases ho with ⟨a, ha⟩
  let _ := a
  rcases ha with ⟨v, hv⟩
  let _ := v
  exact ⟨hpush, huniq, hover, a, v, hv⟩

end AlgebraicGeometry
