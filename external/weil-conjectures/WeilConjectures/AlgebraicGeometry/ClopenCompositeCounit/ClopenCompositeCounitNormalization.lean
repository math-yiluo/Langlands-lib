/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-!
# Clopen projection and composite derived counit

Source: blueprint main-20261015, prop-sf-pf-coherence.proof.md,
compactification-independence and open-restriction/counit calculation; Stacks
04TS, 015F, 0037 and 0DV0 (blueprint: lem-sf-clopen-composite-counit-normalization).

All maps below use the existing constant-module sheaves on the small pro-etale site.
The projector is the localization of the sheaf-level clopen component projection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace AlgebraicGeometry.ProEtale.ClopenCompositeCounit

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The specified inverse-image/direct-image adjunction, written with exact termwise
inverse image. Source: Stacks 015F, 0037
(blueprint: lem-sf-clopen-composite-counit-normalization). -/
def adjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)

/-- The identity-on-open unit, localized from the normalized sheaf adjunction.
Source: Stacks 03DI, 015F (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def openUnit {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] :
    𝟭 (DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))) ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The stipulated adjunct of the inverse open unit, as a natural transformation.
Source: Stacks 0037 (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def comparison {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategory ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor :=
  ((adjunction Λ s).whiskerRight _).homEquiv _ _ (openUnit Λ s).inv

/-- The canonical sheaf comparison is invertible on a clopen immersion.
This is the published comparison, with its existing invertibility proof.
Source: Stacks 04TS (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def sheafComparison {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s ≅
      lowerStar (ModuleCat.{u + 1} Λ) s :=
  letI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s)

/-- The sheaf reverse adjunction. Its unit is identity on the selected clopen piece
and zero on the complementary open: restrict a section, then insert it by zero.
Source: Stacks 04TS, 0037 (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def reverseSheafAdjunction {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    upperStar (ModuleCat.{u + 1} Λ) s ⊣ openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).ofNatIsoRight
    (sheafComparison Λ s).symm

/-- The specified degreewise clopen projector, obtained by localizing its exact
sheaf adjunction; no identification with the derived direct-image unit is assumed.
Source: Stacks 04TS, 015F (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def projector {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategory :=
  (exactDerivedAdjunction (reverseSheafAdjunction Λ s)).unit

/-- Canonical pullback composition, with the orientation P_s P_q to P_(s;q).
Source: Stacks 0037 (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def pullbackComposition {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W) :
    (upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} Λ) (s ≫ q)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) s q).symm

/-- Direct-image composition is the conjugate of inverse pullback composition for
the pasted adjunction, fixing the unit and counit normalization.
Source: Stacks 0037, 0DV0 (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def directComposition {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W) :
    (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor ≅
      (lowerStar (ModuleCat.{u + 1} Λ) (s ≫ q)).rightDerivedFunctor :=
  conjugateIsoEquiv ((adjunction Λ q).comp (adjunction Λ s)) (adjunction Λ (s ≫ q))
    (pullbackComposition Λ s q).symm

/-- The specified a = c composed with S_q(t_s).
Source: Stacks 0037, 0DV0 (blueprint: lem-sf-clopen-composite-counit-normalization). -/
def compositeComparison {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W)
    [IsOpenImmersion s] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) (s ≫ q)).rightDerivedFunctor :=
  Functor.whiskerRight (comparison Λ s)
    (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor ≫ (directComposition Λ s q).hom

/-- The whole stipulated composite, with the pullback identification inserted explicitly.
Source: blueprint prop-sf-pf-coherence.proof.md, open-restriction/counit calculation
(blueprint: lem-sf-clopen-composite-counit-normalization). -/
def cancellation {U X W : Scheme.{u}} (s : U ⟶ X) (q : X ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (M : DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))) :=
  (adjunction Λ q).unit.app
      ((lowerStar (ModuleCat.{u + 1} Λ) (s ≫ q)).rightDerivedFunctor.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor.map
      ((projector Λ s).app
        ((upperStar (ModuleCat.{u + 1} Λ) q).mapDerivedCategory.obj
          ((lowerStar (ModuleCat.{u + 1} Λ) (s ≫ q)).rightDerivedFunctor.obj M))) ≫
    (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctor.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategory.map
        ((pullbackComposition Λ s q).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) (s ≫ q)).rightDerivedFunctor.obj M) ≫
          (adjunction Λ (s ≫ q)).counit.app M)) ≫
    (compositeComparison Λ s q).app M

private theorem exact_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.counit] :
    a.mapExactDerivedCategory.counit =
      (Functor.mapDerivedCategoryCompIso G F).hom ≫
        (Functor.mapDerivedCategoryNatIso (asIso a.counit)).hom ≫
          (Functor.mapDerivedCategoryIdIso D).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
  intro K
  simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app,
    NatTrans.comp_app, Iso.symm_inv]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Q_obj,
    Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors G F K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rfl

omit [Finite Λ] in
private theorem sheaf_counit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    (reverseSheafAdjunction Λ s).counit =
      inv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit := by
  let A := ModuleCat.{u + 1} Λ
  let α := upperStarIsoOpenImmersionRestriction A s
  let a := openImmersionLowerShriekAdjunction A s
  let b := openImmersionRestrictionLowerStarAdjunction A s
  apply NatTrans.ext
  funext N
  apply (cancel_epi
    ((openImmersionLowerShriekUpperStarAdjunction A s).unit.app N)).mp
  rw [NatIso.isIso_inv_app, IsIso.hom_inv_id]
  change (a.unit.app N ≫ α.inv.app _) ≫
    ((upperStar A s).map ((openImmersionLowerShriekToLowerStar A s).app N) ≫
      (upperStarLowerStarAdjunction A s).counit.app N) = 𝟙 _
  rw [Category.assoc, ← α.inv.naturality_assoc]
  rw [← Category.assoc,
    openImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar_app]
  change inv (b.counit.app N) ≫ α.inv.app _ ≫
    (upperStarLowerStarAdjunction A s).counit.app N = 𝟙 _
  rw [← Adjunction.leftAdjointUniq_hom_app_counit
    (upperStarLowerStarAdjunction A s) b N]
  change inv (b.counit.app N) ≫ α.inv.app _ ≫ (α.hom.app _ ≫ b.counit.app N) = 𝟙 _
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, IsIso.inv_hom_id]

omit [Finite Λ] in
private theorem derived_counit {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    (exactDerivedAdjunction (reverseSheafAdjunction Λ s)).counit = (openUnit Λ s).inv := by
  have hc := sheaf_counit Λ s
  have : IsIso (reverseSheafAdjunction Λ s).counit := by
    rw [hc]
    infer_instance
  rw [exactDerivedAdjunction, exact_counit]
  have he : asIso (reverseSheafAdjunction Λ s).counit =
      (asIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit).symm := by
    apply Iso.ext
    exact hc
  rw [he]
  simp only [openUnit, Iso.trans_inv, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

omit [Finite Λ] in
private theorem comparison_eq {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    comparison Λ s = ((exactDerivedAdjunction (reverseSheafAdjunction Λ s)).rightAdjointUniq
      (adjunction Λ s)).hom := by
  ext N
  simp only [comparison, Adjunction.homEquiv_unit, NatTrans.comp_app,
    Adjunction.whiskerRight_unit_app_app, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app]
  change (adjunction Λ s).unit.app _ ≫
    (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctor.map ((openUnit Λ s).inv.app N) = _
  change (adjunction Λ s).homEquiv _ _ ((openUnit Λ s).inv.app N) = _
  apply (adjunction Λ s).homEquiv _ _ |>.symm.injective
  rw [Equiv.symm_apply_apply]
  exact (congr_app (derived_counit Λ s) N).symm.trans
    (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
      (exactDerivedAdjunction (reverseSheafAdjunction Λ s)) (adjunction Λ s) N).symm

end AlgebraicGeometry.ProEtale.ClopenCompositeCounit
