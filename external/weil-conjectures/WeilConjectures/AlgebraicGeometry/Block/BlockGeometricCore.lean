/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystem

/-! # Reindexed ordinary geometric cores

Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
This is the local construction before assembling the system adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (t : SystemBlockMap)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  (A : Data.{c, v, r} J B τ)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
  (RX : SystemBlockRepetition J' G.coefficients G.coefficientTransition t)
  (RY : SystemBlockRepetition J B τ t)

end WeilConjectures.SemilinearSections
