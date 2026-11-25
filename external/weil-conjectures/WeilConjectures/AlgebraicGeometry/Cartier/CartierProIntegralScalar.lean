/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator

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

private theorem source_comparison_unit (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ≫
      (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map
        (geoCartierSourceComparison A i) =
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
          (Etale.ordinaryFiniteConstant A D) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) D).map
          ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom) ≫
      (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app
        (geoCartierConstant A D) := by
  have hm := unit_mateEquiv_symm
    (comparisonAdjunction (ModuleCat.{u + 1} A) D)
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z)
    (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv
    (Etale.ordinaryFiniteConstant A D)
  change _ = (comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ≫
    (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map
      ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
        (Etale.ordinaryFiniteConstant A D)) at hm
  unfold geoCartierSourceComparison
  rw [Functor.map_comp, ← Category.assoc]
  change _ ≫ (comparisonLowerStar (ModuleCat.{u + 1} A) Z).map _ = _
  rw [← hm]
  simp only [Functor.map_comp, Category.assoc]
  have hh := (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.naturality
    ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom
  simp only [Functor.comp_map] at hh
  erw [← hh]
  rfl

private theorem constant_generator_scalar {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (η : geoCartierConstant R D ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant A D))
    (hη : ∀ (W : D.ProEtᵒᵖ) (a : R), η.hom.app W
      ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app W (φ a)) :
    Etale.ordinaryFiniteIntegralGenerator R D ≫
      (Etale.RawModuleScalarComparison.forget R D).map
        ((comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
            (Etale.ordinaryFiniteConstant R D) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} R) D).map
            ((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} D).map ((cartierForget R D).map η) =
    Etale.ordinaryFiniteIntegralGenerator A D ≫
      (Etale.RawModuleScalarComparison.forget A D).map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
            (Etale.ordinaryFiniteConstant A D) ≫
          (comparisonLowerStar (ModuleCat.{u + 1} A) D).map
            ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom) := by
  let adj := constantSheafAdj D.smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.Etale.isTerminalMkId D)
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_naturality_right]
  unfold Etale.ordinaryFiniteIntegralGenerator
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext x
  change η.hom.app (op (Scheme.ProEt.mk (𝟙 D)))
      ((((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom).hom.app
          (op (Scheme.ProEt.mk (𝟙 D)))
        (((comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
          (Etale.ordinaryFiniteConstant R D)).hom.app (op (Scheme.Etale.mk (𝟙 D)))
            ((toSheafify D.smallEtaleTopology
              ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of R R))).app
                (op (Scheme.Etale.mk (𝟙 D))) (x.down : R)))) = _
  rw [comparison_constant_generator, hη, map_intCast]
  exact (comparison_constant_generator A D (x.down : A)).symm

/-- For commutative rings R,A, φ:R→A, a closed immersion i:D→Z and a coefficient map η:R_D→Res(A_D)
normalized on constant-presheaf generators, the normalized pro-etale supported integral generator
for R followed by forget(i_*η) equals the generator for A [def-sfb-cartier-reduction-data,
lemma-cycle-class-cartier-divisor].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-cartier-pro-integral-scalar).
Proof: Transpose the generator comparison under the abelian comparison adjunction. The unit equation
for the mate defining closed direct-image comparison reduces the supported maps to direct images of
the corresponding constant-sheaf maps. The direct-image/restriction comparison is the identity on
sections. For the constant maps, apply the integral constant-sections adjunction: the constant
comparison preserves a generator by its unit equation, and η sends each integral cast to its image
under φ. Since φ preserves integer casts, both maps agree. Evaluate this equality on each
base-changed etale object to finish the supported identity. -/
theorem pro_supported_generator_scalar {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (η : geoCartierConstant R D ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant A D))
    (hη : ∀ (W : D.ProEtᵒᵖ) (a : R), η.hom.app W
      ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app W (φ a)) :
    cartierProIntegralGenerator R i ≫ (cartierForget R Z).map
        ((lowerStar (ModuleCat.{u + 1} R) i).map η) =
      cartierProIntegralGenerator A i := by
  unfold cartierProIntegralGenerator
  simp only [Category.assoc]
  congr 1
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} Z
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_naturality_right]
  unfold cartierForgetComparison
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hR := congrArg (Etale.RawModuleScalarComparison.forget R Z).map
    (source_comparison_unit R i)
  have hA := congrArg (Etale.RawModuleScalarComparison.forget A Z).map
    (source_comparison_unit A i)
  simp only [Functor.map_comp, Category.assoc] at hR hA ⊢
  erw [reassoc_of% hR, hA]
  have hc := constant_generator_scalar φ i η hη
  ext W x
  have hcx := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app
      ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)) hc) x
  have ha (B : Type (u + 1)) [CommRing B] :
      ((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} B)).inv.app
        (geoCartierConstant B D)).hom.app W = 𝟙 _ := by
    dsimp [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso]
    change (𝟙 _) ≫ (geoCartierConstant B D).obj.map (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  let V := (MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W
  change η.hom.app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        ((Scheme.toProEt Z).obj W.unop)))
      (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} R)).inv.app
          (geoCartierConstant R D)).hom.app W
        (((comparisonLowerStar (ModuleCat.{u + 1} R) D).map
            ((comparisonUpperStarConstantSheafIso R D).app (ModuleCat.of R R)).hom).hom.app V
          (((comparisonAdjunction (ModuleCat.{u + 1} R) D).unit.app
              (Etale.ordinaryFiniteConstant R D)).hom.app V
            ((Etale.ordinaryFiniteIntegralGenerator R D).hom.app V x)))) =
    ((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app
        (geoCartierConstant A D)).hom.app W
      (((comparisonLowerStar (ModuleCat.{u + 1} A) D).map
          ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom).hom.app V
        (((comparisonAdjunction (ModuleCat.{u + 1} A) D).unit.app
            (Etale.ordinaryFiniteConstant A D)).hom.app V
          ((Etale.ordinaryFiniteIntegralGenerator A D).hom.app V x)))
  rw [ha R, ha A]
  exact hcx
end AlgebraicGeometry.ProEtale
