/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.CategoryTheory.RingedToposMorphism
import Mathlib.Order.Category.Preord
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms

/-! # The constant/limit ringed sequence projection

Source: Stacks, sites-cohomology.tex, Tags 0940 and 06YY; Zheng, Construction 4.1,
printed p. 21 (auxiliary; not a blueprint node).

The index `n : ℕ` denotes the positive level `n+1`. All systems retain their actual
horizontal section maps. The record below specifies the geometric morphism, its
ordinary module adjunction, and its simultaneous K-flat derived comparison.

## Main definitions

- `CategoryTheory.RingedToposMorphismOfUniverses`: the same ringed-topos fields
  as the recorded interface, with independent site universes.
- `completionSystemEquivalence`: the equivalence in the recorded systems realization.
- `SequenceSetProjection`: the constant/limit geometric morphism and ring map.
- `SequenceModuleRestriction`: exact scalar restriction with the actual transitions.
- `SequenceOrdinaryPullback`: the normalized simultaneous ordinary tensor model.
- `SequenceDerivedPullback`: the unbounded derived functor and representative comparison.
- `SequenceCompletionProjection`: the preceding compatible canonical data.

## Main statements

- `sequenceSiteCompletionProjection`: exactness of the canonical equivalence and
  existence of the compatible constant/limit projection data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe c d v w r
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Forgetting ring structure preserves sheaves in the selected coefficient universe.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
instance (priority := 1100) ringedToposRingForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget RingCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget RingCat.{r})

attribute [-instance] ringedToposRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposRingForgetCompose

/-- Forgetting abelian-group structure preserves sheaves in the coefficient universe.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
instance (priority := 1100) ringedToposAbelianForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) : J.HasSheafCompose (forget AddCommGrpCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget AddCommGrpCat.{r})

attribute [-instance] ringedToposAbelianForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposAbelianForgetCompose

/-- Forgetting commutativity preserves sheaves in the selected coefficient universe.
Source: Stacks 03CZ (auxiliary; not a blueprint node). -/
instance (priority := 1100) ringedToposCommRingForgetCompose
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
  (equivSmallModel.{r} C).hasSheafCompose J
    ((equivSmallModel.{r} C).inverse.inducedTopology J) (forget₂ CommRingCat.{r} RingCat.{r})

attribute [-instance] ringedToposCommRingForgetCompose
scoped[CategoryTheory] attribute [instance 1100] ringedToposCommRingForgetCompose

/-- A geometric morphism with a structural ring map and the induced direct image on modules.

Source: Stacks Project, Sites, Definition 00XA, and Modules on Sites, pushforward of modules
(auxiliary; not a blueprint node).

The ring identities test every generalized element of the target topos. Left exactness
identifies the inverse image of products and the terminal object, so these are precisely
the identities for a morphism of ring objects. The last identity specifies addition and
scalar multiplication on the module direct image under the sheaf adjunction. It includes
zero by taking all three module elements zero. Thus the supplied module direct image is
the usual induced one, up to its displayed natural identification, not an arbitrary lift.
No exactness of the tensor module pullback or preservation of K-injectives is assumed. -/
structure RingedToposMorphismOfUniverses
    {C : Type c} {D : Type d} [Category.{v} C] [Category.{w} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J RingCat.{r}) (B : Sheaf K RingCat.{r}) where
  /-- Inverse image of sheaves of sets. -/
  inverse : Sheaf K (Type r) ⥤ Sheaf J (Type r)
  /-- Direct image of sheaves of sets. -/
  direct : Sheaf J (Type r) ⥤ Sheaf K (Type r)
  /-- The geometric adjunction. -/
  adj : inverse ⊣ direct
  /-- Left exactness is required only for the underlying inverse image. -/
  leftExact : PreservesFiniteLimits inverse
  /-- The structural map, with ring structure specified by generalized elements below. -/
  ringMap : inverse.obj ((sheafCompose K (forget RingCat.{r})).obj B) ⟶
    (sheafCompose J (forget RingCat.{r})).obj A
  /-- Preservation of zero. -/
  ring_zero : ∀ (T : Sheaf K (Type r))
    (z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Zero.zero (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @Zero.zero (A.obj.obj U) inferInstance
  /-- Preservation of one. -/
  ring_one : ∀ (T : Sheaf K (Type r))
    (z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @One.one (B.obj.obj U) inferInstance) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t = @One.one (A.obj.obj U) inferInstance
  /-- Preservation of add. -/
  ring_add : ∀ (T : Sheaf K (Type r))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Add.add (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- Preservation of mul. -/
  ring_mul : ∀ (T : Sheaf K (Type r))
    (x y z : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Mul.mul (B.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((inverse.map z) ≫ ringMap).hom.app U t =
        @Mul.mul (A.obj.obj U) inferInstance
          (((inverse.map x) ≫ ringMap).hom.app U t)
          (((inverse.map y) ≫ ringMap).hom.app U t)
  /-- The induced direct image on module sheaves. -/
  modules : ringedSiteModules.{r} A ⥤ ringedSiteModules.{r} B
  /-- Additivity of the induced direct image. -/
  additive : modules.Additive
  /-- The underlying direct image of sheaves of sets, naturally in the module. -/
  underlying :
    modules ⋙ SheafOfModules.toSheaf B ⋙ sheafCompose K (forget AddCommGrpCat.{r}) ≅
      (SheafOfModules.toSheaf A ⋙ sheafCompose J (forget AddCommGrpCat.{r})) ⋙ direct
  /-- Addition and the structural-map-induced scalar action, under adjunction. -/
  module_linear : ∀ (M : ringedSiteModules.{r} A) (T : Sheaf K (Type r))
    (a : T ⟶ (sheafCompose K (forget RingCat.{r})).obj B)
    (x y z : T ⟶ (sheafCompose K (forget AddCommGrpCat.{r})).obj
      ((SheafOfModules.toSheaf B).obj (modules.obj M))),
    (∀ (U : Dᵒᵖ) (t : T.obj.obj U),
      z.hom.app U t = @Add.add ((modules.obj M).val.obj U) inferInstance
        (@SMul.smul (B.obj.obj U) ((modules.obj M).val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) →
    ∀ (U : Cᵒᵖ) (t : (inverse.obj T).obj.obj U),
      ((adj.homEquiv T _).symm (z ≫ underlying.hom.app M)).hom.app U t =
        @Add.add (M.val.obj U) inferInstance
          (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
            (((inverse.map a) ≫ ringMap).hom.app U t)
            (((adj.homEquiv T _).symm (x ≫ underlying.hom.app M)).hom.app U t))
          (((adj.homEquiv T _).symm (y ≫ underlying.hom.app M)).hom.app U t)

attribute [instance] RingedToposMorphismOfUniverses.additive

end CategoryTheory

open scoped CategoryTheory

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C)
  (B : ℕ → Sheaf J CommRingCat.{r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

attribute [local instance 30000] CategoryTheory.ringedToposRingForgetCompose
  CategoryTheory.ringedToposAbelianForgetCompose CategoryTheory.ringedToposCommRingForgetCompose

private instance seqSetHasLimit (F : ℕᵒᵖ ⥤ Sheaf J (Type r)) : HasLimit F :=
  inferInstance

private instance seqModHasLimit (R : Sheaf J CommRingCat.{r})
    (F : ℕᵒᵖ ⥤ Mod.{c, v, r} J R) : HasLimit F := inferInstance

attribute [local instance 30000] seqSetHasLimit seqModHasLimit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.hasSheafCompose_of_preservesMulticospan
