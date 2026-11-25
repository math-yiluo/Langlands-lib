/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Étale hypercovers without finiteness or splitting

Source: Stacks Project, Hypercoverings, Definition 01G5 and Lemma 01GI;
matching schemes as in blueprint `corollary-cohomology-pro-etale-affine`.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The all-degree hypercover condition, without splitting or finiteness requirements.
The matching projections and their universal property use exactly the lower-simplex
matching diagram of `FiniteSplitEtaleHypercover`. Tests range over all schemes over `X`.
At degree zero the diagram is empty and its limit is `X`; at degree one it is the
product of the two vertices. Morphisms in `X.Etale` are automatically étale, so the
covering condition is precisely surjectivity of the underlying matching arrow.
Source: Stacks Project, Hypercoverings, Definition 01G5, and the matching-scheme clause
of blueprint `corollary-cohomology-pro-etale-affine`.
(auxiliary; not a blueprint node) -/
def IsEtaleHypercover {X : Scheme.{u}} (U : SimplicialObject X.Etale) : Prop :=
  ∀ n : ℕ, ∃ (M : X.Etale)
    (π : ∀ (Δ : SimplexCategory), Δ.len < n →
      (Δ ⟶ SimplexCategory.mk n) → (M ⟶ U.obj (op Δ)))
    (μ : U.obj (op (SimplexCategory.mk n)) ⟶ M),
    (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      π Δ h θ ≫ U.map α.op = π Δ' h' (α ≫ θ)) ∧
    (∀ (T : Over X)
      (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ SimplexCategory.mk n) →
        (T ⟶ (Scheme.Etale.forget X).obj (U.obj (op Δ)))),
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
        (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
        p Δ h θ ≫ (Scheme.Etale.forget X).map (U.map α.op) = p Δ' h' (α ≫ θ)) →
      ∃! f : T ⟶ (Scheme.Etale.forget X).obj M,
        ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
          f ≫ (Scheme.Etale.forget X).map (π Δ h θ) = p Δ h θ) ∧
    (∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
      μ ≫ π Δ h θ = U.map θ.op) ∧ Surjective μ.left

end AlgebraicGeometry
