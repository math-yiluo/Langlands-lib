/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechTotalMap

/-! # Naturality of the coefficient augmentation

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-abelian-cech-beta-square)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The coefficient augmentation commutes with a lift of a coefficient morphism.
Source: Stacks Project, Tags 01EQ and 01FD, beta square.
(blueprint: lem-pc-abelian-cech-beta-square)

Proof: Compare each degree using naturality of the total-complex summand
inclusion. The resolution lifting equation identifies the two coefficient
morphisms into the zeroth resolution term; apply the Čech functor to it. -/
theorem abelianCechBeta_square
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {f : F ⟶ G}
    (φ : InjectiveResolution.Hom I J f) :
    abelianCechBeta U I ≫ abelianCechTotalMap U φ.hom =
      (TopCat.Sheaf.cechComplexFunctor U).map f ≫ abelianCechBeta U J := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [abelianCechBeta, abelianCechTotalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (((TopCat.Sheaf.cechComplexFunctor U).map (I.ι.f 0)).f n ≫
    ((TopCat.Sheaf.cechComplexFunctor U).map (φ.hom.f 0)).f n) ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    φ.ι_f_zero_comp_hom_f_zero]
  simp only [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.Modules
