/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechSectionsMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechTotalMap

/-! # Naturality of the restriction augmentation

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-abelian-cech-alpha-square)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The restriction augmentation commutes with every resolution cochain map.
Source: Stacks Project, Tags 01EQ and 01FD, alpha square.
(blueprint: lem-pc-abelian-cech-alpha-square)

Proof: Compare each degree after the total-complex summand inclusion.
Naturality of the resolution morphism as a presheaf morphism commutes with
restriction from the whole space to each finite intersection. -/
theorem abelianCechAlpha_square
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    abelianCechAlpha U I ≫ abelianCechTotalMap U φ =
      abelianCechSectionsMap φ ≫ abelianCechAlpha U J := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [abelianCechAlpha, abelianCechTotalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  apply congrArg (fun k ↦ k ≫ (abelianCechDouble U J).ιTotal (.up ℕ) 0 n n (by simp))
  ext s
  funext y
  exact NatTrans.naturality_apply (φ.f n).hom
    (homOfLE (le_top (a := ⨅ l, U (y l)))).op s

end AlgebraicGeometry.Scheme.Modules
