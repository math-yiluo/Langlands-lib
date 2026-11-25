/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.RingTheory.Flat.Basic
import all WeilConjectures.Algebra.Homology.RingedSitePointTensor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Flat module stalks at a topos point -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.RingedSitePoint

/-- Geometric module inverse image preserves flat objects at a point.
Source: Stacks Project, Modules on Sites, Tag 05VD.
(auxiliary; not a blueprint node)

Proof: present the point as a morphism to the bottom-topology one-object site,
using its prescribed ring and module operation graphs. The algebraic inverse-image
flatness theorem applies to this presentation. Evaluation on the one-object site
is an equivalence of module categories, compatible with tensor. Consequently its
image of the exact tensor functor is the ordinary exact tensor functor with the
stalk module, which is the categorical criterion for flatness over its ring. -/
theorem flat
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p)
    (M : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (hM : SheafOfModules.IsFlatOnSite.{u, v, w, w} (J := J) (R := R) M) :
    Module.Flat s.ring (s.modules.obj M) := by
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : (constant (Type w)).IsEquivalence := setEquivalence.isEquivalence_inverse
  have : PreservesFiniteLimits (p.inverse ⋙ constant (Type w)) :=
    comp_preservesFiniteLimits _ _
  let adj : (p.inverse ⋙ constant (Type w)) ⊣ (setEquivalence.functor ⋙ p.direct) :=
    p.adj.comp setEquivalence.symm.toAdjunction
  let I := pointInverse s
  have hflat := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u, v, w, w, w, w}
    (p.inverse ⋙ constant (Type w)) _ adj
    (SheafOfModules.inverseImageOfUniverses_adapted I) M hM
  let S := pointRing s.ring
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.symmetricCategory S
  let N := I.modules.obj M
  have hN : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso S N) hflat
  have : PreservesFiniteLimits (tensorRight N) := (exactFunctor_iff _).1 hN |>.1
  have : PreservesFiniteLimits (tensorLeft N) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have : (moduleConstant s.ring).IsEquivalence := (moduleEquivalence s.ring).isEquivalence_inverse
  let e : moduleConstant s.ring ⋙ tensorLeft N ⋙ moduleEval s.ring ≅
      tensorLeft ((moduleEval s.ring).obj N) :=
    (Functor.isoWhiskerLeft (moduleConstant s.ring) ((evalTensorNatIso s.ring).app N)).symm
  have : PreservesFiniteLimits (moduleConstant s.ring ⋙ tensorLeft N ⋙ moduleEval s.ring) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (tensorLeft ((moduleEval s.ring).obj N)) :=
    preservesFiniteLimits_of_natIso e
  change Module.Flat s.ring ((moduleEval s.ring).obj N)
  exact (ModuleCat.flat_iff_flat _).1
    ((ObjectProperty.flat_iff_preservesFiniteLimits _).2 inferInstance)

end CategoryTheory.RingedSitePoint
