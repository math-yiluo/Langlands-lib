/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Finite lisse partitions of subsets of a scheme

Source: finite pushforward constructibility blueprint, steps 2 and 3.
(blueprint: lem-weil-pbc-constructible-etale-lisse-partition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite partition of a subset of `X` by images of immersed schemes, with lisse
pullback of `F` on every part. The support need not be all of `X`, so this records the
induction claim for closed subsets without changing the ambient sheaf.

Source: blueprint `lemma-detection-proper-direct-image--1`, steps 2--3.
(blueprint: lem-weil-pbc-constructible-etale-lisse-partition). -/
structure EtaleLissePartition {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (T : Set X) where
  /-- The number of parts, including the possibility of zero parts. -/
  n : ℕ
  /-- The schemes realizing the parts. -/
  domain : Fin n → Scheme.{u}
  /-- Their immersions into the fixed ambient scheme. -/
  immersion : ∀ i, domain i ⟶ X
  /-- Every part is locally closed. -/
  isImmersion : ∀ i, IsImmersion (immersion i)
  /-- The images cover exactly the support. -/
  covers : (⋃ i, Set.range (immersion i)) = T
  /-- The images are pairwise disjoint. -/
  disjoint : Pairwise (fun i j ↦ Disjoint (Set.range (immersion i)) (Set.range (immersion j)))
  /-- The ambient sheaf becomes lisse on each part. -/
  lisse : ∀ i, IsLisseEtaleSheafOfSets ((etaleSetPullback (immersion i)).obj F)

end AlgebraicGeometry.Scheme
