/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientEtaleDerivedStalk
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Sites.Point.Monoidal
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Flat coefficient module sheaves have flat geometric stalks

Source: Stacks Project, Modules on Sites, Tag 05VC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

private instance coefficientModuleLocallyBijective
    {C : Type*} [Category C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) (B : Type w) [CommRing B] :
    J.WEqualsLocallyBijective (ModuleCat.{w} B) := by
  have : ∀ V : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (equivSmallModel.{w} C).inverse.op)
        (ModuleCat.{w} B) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    J (A := ModuleCat.{w} B)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private instance etaleSheafify
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B] :
    HasSheafify X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B) := by
  have : HasSheafify ((equivSmallModel.{max v (u + 1)} X.Etale).inverse.inducedTopology
      X.smallEtaleTopology) (ModuleCat.{max v (u + 1)} B) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact hasSheafifyEssentiallySmallSite.{u, max v (u + 1), u + 1, max v (u + 1) + 1, max v (u + 1)}
    X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem geometric_fiber_flat
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B))
    (hF : ObjectProperty.flat F) :
    Module.Flat B (((pointSmallEtale x).sheafFiber
      (A := ModuleCat.{max v (u + 1)} B)).obj F) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    ModuleCat.hasLimitsOfSize.{u, u, max v (u + 1), max v (u + 1)}
  have : AB5OfSize.{u, u} (ModuleCat.{max v (u + 1)} B) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{max v (u + 1)} B)) :=
    preservesFilteredColimitsOfSize_shrink.{u, max v (u + 1), u, max v (u + 1)} _
  have : HasProducts.{u} (ModuleCat.{max v (u + 1)} B) :=
    fun _ ↦ ModuleCat.hasLimitsOfShape
  have (M : ModuleCat.{max v (u + 1)} B) :
      PreservesFilteredColimitsOfSize.{u, u} (tensorLeft M) :=
    preservesFilteredColimitsOfSize_shrink.{u, max v (u + 1), u, max v (u + 1)} _
  have (M : ModuleCat.{max v (u + 1)} B) :
      PreservesFilteredColimitsOfSize.{u, u} (tensorRight M) :=
    preservesFilteredColimitsOfSize_shrink.{u, max v (u + 1), u, max v (u + 1)} _
  let Φ := pointSmallEtale x
  have : (Φ.sheafFiber (A := ModuleCat.{max v (u + 1)} B)).Monoidal := inferInstance
  have hm {M N : ModuleCat.{max v (u + 1)} B} (f : M ⟶ N) [Mono f] :
      Mono (Φ.sheafFiber.obj F ◁ f) := by
    have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
    have : Mono (F ◁ (constantSheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)).map f) :=
      (tensorLeft F).map_mono _
    have : Mono (Φ.sheafFiber.obj F ◁ Φ.sheafFiber.map
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)).map f)) := by
      rw [(IsIso.eq_inv_comp _).2 (Functor.OplaxMonoidal.δ_natural_right Φ.sheafFiber F _)]
      infer_instance
    have h : f = (Φ.sheafFiberConstantSheafIso M).inv ≫
        Φ.sheafFiber.map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)).map f) ≫
        (Φ.sheafFiberConstantSheafIso N).hom := by
      simp [Φ.sheafFiber_map_constantSheaf_map]
    rw [h, whiskerLeft_comp, whiskerLeft_comp]
    infer_instance
  apply (ModuleCat.flat_iff_flat _).mp
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  refine ((Functor.preservesFiniteLimits_tfae _).out 1 4).1 fun S hS ↦ ?_
  have := hS.mono_f
  refine ⟨?_, hm S.f⟩
  exact ((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1
    inferInstance S hS).1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Flatness survives the normalized coefficient geometric stalk.
Source: Stacks Project, Modules on Sites, Tag 05VC, only-if direction.
(auxiliary; not a blueprint node).

Proof: constant-scalar restriction is an exact symmetric monoidal equivalence.
Consequently it takes the exact right-tensor functor of the given module sheaf to
an exact right-tensor functor on fixed-coefficient sheaves. The AsSmall equivalence
has the same property. At the geometric point, test a monomorphism of B-modules by
its constant sheaf. Constant sheafification preserves this monomorphism, tensoring
with the flat sheaf preserves it, and the exact strong monoidal fiber functor
preserves it. The fiber of a constant sheaf is its original module, so this proves
that tensoring with the stalk preserves every monomorphism. Tensor is right exact,
hence the stalk is flat. These comparisons preserve the B-action induced by the
constant-ring unit; no identification with an unrelated stalk ring is chosen.
The argument includes the zero sheaf and zero coefficient ring and uses neither
Noetherianity nor local constancy. -/
theorem coefficientEtaleModuleStalk_flat
    (X : Scheme.{u}) (B : Type (max v (u + 1))) [CommRing B]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : ConstantCompletion.Mod
      (ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B))
    (hF : SheafOfModules.IsFlat
      (R := ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X) B) F) :
    Module.Flat B ((coefficientEtaleModuleStalk X B x).obj F) := by
  let J := smallModelComparisonEtaleTopology.{u, v} X
  let e : X.Etale ≌ smallModelComparisonEtaleSite.{u, v} X := AsSmall.equiv
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite J X.smallEtaleTopology := by
    change (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      (AsSmall.down.inducedTopology X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  let R := ConstantCompletion.constant J B
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have hflat : ObjectProperty.flat F :=
    (ConstantScalarRestriction.rightFlat_iff F).mpr hF
  let T := ConstantScalarRestriction.restriction J B
  have hT : ObjectProperty.flat (T.obj F) :=
    (ConstantScalarRestriction.flat_equivalence T F).mp hflat
  have hfixed : ObjectProperty.flat ((coefficientModelFixedScalars J B).obj F) :=
    ObjectProperty.prop_of_iso _ ((CategoryTheory.restrictionIso J B).app F) hT
  let G := e.functor.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} B)
    X.smallEtaleTopology J
  have : G.IsEquivalence := by
    change (e.sheafCongr X.smallEtaleTopology J (ModuleCat.{max v (u + 1)} B)).inverse.IsEquivalence
    infer_instance
  let H := (Functor.whiskeringLeft _ _ (ModuleCat.{max v (u + 1)} B)).obj e.functor.op ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{max v (u + 1)} B)
  let : Localization.Lifting (presheafToSheaf J (ModuleCat.{max v (u + 1)} B))
      J.W H G := ⟨(e.functor.pushforwardContinuousSheafificationCompatibility
        (ModuleCat.{max v (u + 1)} B) X.smallEtaleTopology J).symm⟩
  let : G.Monoidal := Localization.Monoidal.functorMonoidalOfComp
    (presheafToSheaf J (ModuleCat.{max v (u + 1)} B)) J.W G H
  let : G.PreservesFlat := G.preservesFlat_of_isEquivalence
  exact geometric_fiber_flat X B x (G.obj ((coefficientModelFixedScalars J B).obj F))
    (Functor.PreservesFlat.flat_obj hfixed)

end AlgebraicGeometry.Scheme
