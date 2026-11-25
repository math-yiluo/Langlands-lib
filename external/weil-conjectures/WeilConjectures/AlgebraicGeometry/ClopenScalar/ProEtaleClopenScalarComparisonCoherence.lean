/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData

import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarCompositionModel
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenScalarIdentityModel

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  computation

private theorem tensor_ext {Z : Scheme.{t}} {p : Presentations.{t, u} Z}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (hD := derived.{t, u} Z) @p)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (M : Mods.{t, u} R) (N : Mods.{t, u} S)
    (f g : (ext (p a)).obj M ⟶ N)
    (h : ∀ (W : Z.ProEtᵒᵖ) (x : M.val.obj W),
      f.val.app W (sectionTensor (p a) M W 1 x) =
        g.val.app W (sectionTensor (p a) M W 1 x)) : f = g := by
  apply ((n.ordinaryAdjunction a).homEquiv M N).injective
  ext W x
  change f.val.app W (((n.ordinaryAdjunction a).unit.app M).val.app W x) =
    g.val.app W (((n.ordinaryAdjunction a).unit.app M).val.app W x)
  rw [n.ordinary_unit]
  exact h W x

private theorem tensor_transport {Z : Scheme.{t}} (p : Presentations.{t, u} Z)
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}}
    (a b : R ⟶ S) (h : a = b) (M : Mods.{t, u} R) (W : Z.ProEtᵒᵖ)
    (s : S.obj.obj W) (x : M.val.obj W) :
    (eqToHom (congrArg (fun f ↦ (ext (p f)).obj M) h)).val.app W
      (sectionTensor (p a) M W s x) = sectionTensor (p b) M W s x := by
  cases h
  rfl

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
