/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonicalCollapse

/-! # Pairings of the canonical Godement iterates -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical iterates admit pairings compatible with unit and multiplication insertions.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR,
the construction of the Godement resolution.
(blueprint: lem-sc-module-cup-godement-iterate-pairings)
Proof: write T for the product of stalk skyscrapers. For each point x, project
T(F) and T(G) to the x-coordinate, take their tensor, and use the stalk tensor
map to the skyscraper of the stalk of F tensor G. The bilinear maps on opens
commute with restriction; the sheaf tensor universal property gives beta(F,G).
Product projections detect equality. On germ sections the coordinate of beta
is the tensor of the two germs, so beta commutes with the germ unit. To check
monad multiplication, represent both outer stalk sections on a common open
neighbourhood of x. Both orders of evaluation give the tensor of their inner
x-coordinates. Thus beta also commutes with multiplication.
Set p(0) to the identity of F tensor G, and recursively set p(n+1) to
beta(T^n F,T^n G) followed by T(p(n)). Induct on n for the insertion identities.
For position zero use unit naturality and the unit identity for beta. For a
positive position use the induction hypothesis, functoriality of T, and
naturality of beta. For collapses, position zero uses multiplication naturality
and the multiplication identity for beta; positive positions use the same
induction with T and beta naturality. These arguments apply to arbitrary module
sheaves, including zero sheaves. On the empty scheme there are no coordinates,
and product uniqueness proves each identity. No model or augmentation is used. -/
theorem moduleCup_godement_iterate_pairings (X : Scheme.{u}) (F G : X.Modules) :
    ∃ p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
        moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n,
      p 0 = 𝟙 (F ⊗ G) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementInsert X F n i ⊗ₘ moduleCup_godementInsert X G n i) ≫
          p (n + 1) = p n ≫ moduleCup_godementInsert X (F ⊗ G) n i) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementCollapse X F n i ⊗ₘ moduleCup_godementCollapse X G n i) ≫
          p (n + 1) = p (n + 2) ≫ moduleCup_godementCollapse X (F ⊗ G) n i) := by
  obtain ⟨β, p, hp0, hprec, hpδ⟩ :=
    moduleCup_godement_iterate_pairings_canonical_exists X F G
  have hpσ := moduleCup_godement_iterate_pairings_collapse_of_canonical
    X F G β p hp0 hprec
  exact ⟨p, hp0, hpδ, hpσ⟩

end
end AlgebraicGeometry.Scheme.Modules
