/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The closed-support Hom sequence

The ordinary injective-sheaf exact sequence used in the derived closed-support comparison.
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The standard sheafification property, named before constructing the support maps.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasSheafify

/-- The same weak sheafification instance, with its proof fixed once on the site.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasWeakSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasWeakSheafify

/-- Existence of the standard global-section adjunction, named once on the site.
Source: Stacks, Tag 009F (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasGlobalSections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasGlobalSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasGlobalSections

/-- The canonical abelian structure, with pointwise addition on sheaf morphisms exposed.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleAbelian (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  { (inferInstance : Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) with
    toPreadditive := @Preadditive.fullSubcategory _ _
      (CategoryTheory.functorCategoryPreadditive (C := T.Etaleᵒᵖ)
        (D := ModuleCat.{u + 1} A)) _ }

attribute [local instance 200000] closedSupportEtaleAbelian

/-- The existing linear structure on module sheaves, named for use in Hom functors.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleLinear (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Linear A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

end AlgebraicGeometry.Etale

attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

namespace CategoryTheory
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def adjunctionHomLinearEquiv
    (R : Type*) [Ring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Linear R]
    (adj : F ⊣ G) (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
    rw [Functor.map_smul, Linear.comp_smul]

end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def rankOneSectionsEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj J := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  have : ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (⊤_ T.Etale))).Linear A := adj.right_adjoint_linear
  let e : (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (ModuleCat.of A A ⟶ ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).obj J) :=
    CategoryTheory.adjunctionHomLinearEquiv A adj (ModuleCat.of A A) J
  exact (e.trans (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf A A _))).trans
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).app J).symm.toLinearEquiv

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
lemma rankOneSectionsEquiv_naturality (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {J J' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : J ⟶ J') (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    rankOneSectionsEquiv A T J' (f ≫ k) =
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
        (rankOneSectionsEquiv A T J f) := by
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).inv.app J'
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).homEquiv _ _ (f ≫ k)) (1 : A)) =
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).inv.app J
        (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
          terminalIsTerminal).homEquiv _ _ f) (1 : A)))
  rw [Adjunction.homEquiv_naturality_right]
  exact congrArg (fun g ↦ g
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ f) (1 : A)))
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality k)

private lemma unit_app_upperStarConstantSheafIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) (a : ModuleCat.{u + 1} A) :
    (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} A) v).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.app _ =
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v))
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit] at this
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at this
  rw [← this, Scheme.upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.naturality]
  rfl

end AlgebraicGeometry.Etale

namespace CategoryTheory
universe v u' w
variable {C : Type u'} [Category.{v} C] [Abelian C]
  (R : Type w) [Ring R] [Linear R C]
end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- The closed constant sheaf from which supported Hom is taken.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomSource (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The ordinary Hom functor used by the canonical closed-support sequence.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op (closedSupportHomSource A i))

/-- The closed-support Hom functor is additive.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
instance closedSupportHomFunctor_additive (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) : (closedSupportHomFunctor A i).Additive := by
  dsimp only [closedSupportHomFunctor]
  infer_instance

/-- The canonical left map of the closed-support Hom sequence.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomToSections (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    closedSupportHomFunctor A i ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let g := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom
  exact
    { app J := ModuleCat.ofHom ((rankOneSectionsEquiv A T J).toLinearMap.comp
        (Linear.leftComp A J g))
      naturality J J' k := by
        ext f
        change rankOneSectionsEquiv A T J' (g ≫ f ≫ k) = _
        rw [← Category.assoc, rankOneSectionsEquiv_naturality]
        rfl }

end AlgebraicGeometry.Etale
