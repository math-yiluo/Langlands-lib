/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumStalks
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback

set_option linter.privateModule false

/-! # Normalization of the étale projection comparison

Source: Stacks Project, Tag 0GKF.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped DirectSum TensorProduct

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma projection_tensor_unit (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
    letI := adj.rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ R M N ≫
        (tensorIso (asIso (adj.counit.app M)).symm
          (asIso (adj.counit.app N)).symm ≪≫
            Functor.Monoidal.μIso L M.obj N.obj).hom.hom =
      toSheafify X.smallEtaleTopology (M.obj ⊗ N.obj) := by
  dsimp only
  let adj := sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
  change adj.unit.app (M.obj ⊗ N.obj) ≫
    R.map (Functor.OplaxMonoidal.δ L _ _ ≫
      (adj.counit.app M ⊗ₘ adj.counit.app N)) ≫
    R.map (inv (adj.counit.app M) ⊗ₘ inv (adj.counit.app N)) ≫
    R.map (Functor.LaxMonoidal.μ L M.obj N.obj) = adj.unit.app (M.obj ⊗ N.obj)
  rw [← R.map_comp, ← R.map_comp]
  have he : (Functor.OplaxMonoidal.δ L M.obj N.obj ≫
      (adj.counit.app M ⊗ₘ adj.counit.app N)) ≫
      ((inv (adj.counit.app M) ⊗ₘ inv (adj.counit.app N)) ≫
        Functor.LaxMonoidal.μ L M.obj N.obj) = 𝟙 _ := by
    rw [Category.assoc, ← Category.assoc (adj.counit.app M ⊗ₘ adj.counit.app N),
      tensorHom_comp_tensorHom, IsIso.hom_inv_id, IsIso.hom_inv_id, id_tensorHom_id,
      Category.id_comp, Functor.Monoidal.δ_μ]
  rw [he, R.map_id]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
