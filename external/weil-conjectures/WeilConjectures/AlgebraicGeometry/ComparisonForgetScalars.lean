/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
private theorem cachedAbSheafify (Z : Scheme.{u}) :
    HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
private theorem cachedModSheafify (Z : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance
attribute [local instance] cachedAbSheafify cachedModSheafify
attribute [local irreducible] comparisonUpperStar

/-- For a scheme Z and commutative ring A, there is a canonical natural isomorphism forget_A,et ⋙
ν*_Ab ≅ ν*_A ⋙ forget_A,pro
[proposition-comparison-morphism-inverse-image,
def-sbc-raw-module-scalar-pullback-comparison]. Its component is adjoint to the
coefficient-forgotten
comparison adjunction unit.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: Coefficient forgetting is left adjoint to coefficient coinduction. Compose this adjunction
with site comparison in the two orders. Their right adjoints agree, so uniqueness of left adjoints
gives the isomorphism. Apply the two Hom equivalences to its component; the left-adjoint uniqueness
unit equation and naturality of the coinduction unit identify the component with the stated mate. -/
def forgetComparisonIso (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    Etale.moduleAbelianForget A Z ⋙
        comparisonUpperStar AddCommGrpCat.{u + 1} Z ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) Z ⋙
        sheafCompose (Scheme.ProEt.topology Z)
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
  ((Sheaf.forget₂CoinduceAdj Z.smallEtaleTopology A).comp
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z)).leftAdjointUniq
      ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).comp
        (Sheaf.forget₂CoinduceAdj (Scheme.ProEt.topology Z) A))

theorem forgetComparisonIso_hom (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u})
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (forgetComparisonIso A Z).hom.app M =
      ((comparisonAdjunction AddCommGrpCat.{u + 1} Z).homEquiv _ _).symm
        ((Etale.moduleAbelianForget A Z).map
          ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app M)) := by
  apply ((comparisonAdjunction AddCommGrpCat.{u + 1} Z).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply ((Sheaf.forget₂CoinduceAdj Z.smallEtaleTopology A).homEquiv _ _).injective
  change (((Sheaf.forget₂CoinduceAdj Z.smallEtaleTopology A).comp
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z)).homEquiv _ _)
      ((forgetComparisonIso A Z).hom.app M) = _
  rw [forgetComparisonIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.comp_unit_app]
  rw [Adjunction.homEquiv_unit]
  ext W x
  exact ConcreteCategory.congr_hom
    ((ModuleCat.forget₂CoinduceAdj A).unit.naturality
      (((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app M).hom.app W)) x
end AlgebraicGeometry.ProEtale
