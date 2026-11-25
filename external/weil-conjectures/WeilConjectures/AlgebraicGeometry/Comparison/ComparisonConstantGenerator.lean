/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement

/-! # Cartier reduction and site comparison
Source: blueprint main-20261015, Cartier comparison proof
(blueprint: lem-sp-cartier-reduction-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierProIntegralGenerator cartierProRootMap cartierReducedEtale cartierReducedPro
  CartierEtaleReductionSpec CartierProReductionSpec cartierResidueReducedPro

/-- For a commutative ring A, scheme D and a∈A, the etale constant-presheaf generator a, followed by
the comparison adjunction unit and the canonical constant-sheaf comparison, equals the pro-etale
constant-presheaf generator a at the terminal object [def-weil-pbc-constant-sheaf,
proposition-comparison-morphism-inverse-image].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-comparison-constant-generator).
Proof: The canonical constant comparison is uniqueness of left adjoints between the composite of
constant-sheaf and comparison adjunctions and the pro-etale constant-sheaf adjunction. Their unit
compatibility equation, evaluated on the coefficient module and then on a, is precisely the
displayed formula. The section-functor comparison at the terminal object is definitionally the
identity. -/
theorem comparison_constant_generator (A : Type (u + 1)) [CommRing A]
    (D : Scheme.{u}) (a : A) :
    (((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom).hom.app
        (op (Scheme.ProEt.mk (𝟙 D)))
      (((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
        (Etale.ordinaryFiniteConstant A D)).hom.app (op (Scheme.Etale.mk (𝟙 D)))
        ((toSheafify D.smallEtaleTopology
          ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.Etale.mk (𝟙 D))) a)) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          (op (Scheme.ProEt.mk (𝟙 D))) a := by
  let adj1 := (((constantSheafAdj D.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.Etale.isTerminalMkId D)).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) D)).ofNatIsoRight
      ((Scheme.toProEt D).sheafPushforwardContinuousCompSheafSectionsObjIso
        (ModuleCat.{u + 1} A) D.smallEtaleTopology (Scheme.ProEt.topology D)
          (op (Scheme.Etale.mk (𝟙 D)))))
  let adj2 := constantSheafAdj (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId D)
  have hh := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 (ModuleCat.of A A)
  have hh' := ConcreteCategory.congr_hom hh a
  exact hh'
end AlgebraicGeometry.ProEtale
