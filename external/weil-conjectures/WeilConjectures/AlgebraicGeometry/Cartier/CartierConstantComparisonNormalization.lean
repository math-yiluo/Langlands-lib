/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierClosedExchangeComparison

/-!
# Normalization and naturality of the Cartier constant comparison

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, opening comparison paragraph; Stacks Project, Sites and
Sheaves, Tags 0H7J and 00WX
(blueprint: lem-sfb-cartier-constant-comparison-normalization).

The inverse images below are the functors on fixed-coefficient module-valued sheaves.
The etale constant structure map is written as the adjunct of the sheafification extension
of the constant-presheaf unit. The pro-etale structure map is the published map with
that same definition. The commutation isomorphism is the conjugate of the canonical
commutation of direct images along base change and the inclusion of sites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- The Cartier constant comparison equals the uniqueness-of-left-adjoints isomorphism,
is invertible, and commutes with inverse image along every closed immersion.
Source: blueprint sk-lem-geo-cartier.proof.md, opening comparison paragraph;
Stacks Project, Sites and Sheaves, Tags 0H7J (example-constant-sheaf) and
00WX (lemma-adjoint-sheaves)
(blueprint: lem-sfb-cartier-constant-comparison-normalization).

Proof:
1. By def-weil-pbc-sheafification and def-weil-pbc-constant-sheaf, maps from a constant
   sheaf are maps from the constant presheaf. Such a map is determined by its component
   at the terminal object, with all other components obtained by restriction. This gives
   the constant-sheaf/sections adjunction with unit the sheafification unit at the terminal
   object. Compose it with the comparison adjunction using def-weil-pbc-composite-adjunction
   and proposition-comparison-morphism-inverse-image. The inclusion preserves the terminal object,
   so both right adjoints are pro-etale sections.
2. By situation-conventions, the left-adjoint uniqueness isomorphism
   corresponds to the pro-etale constant unit. The explicit definition of
   cartierConstantComparison first extends that presheaf unit by sheafification and then
   transposes under the comparison adjunction. Evaluating on the etale constant unit at
   the terminal object gives the pro-etale unit. Injectivity of the composite hom bijection
   identifies the maps. The comparison is therefore invertible.
3. For the closed immersion, def-weil-pbc-inverse-image and
   def-weil-proetale-inverse-image identify the adjuncts of both constant structure maps
   with the constant-section direct-image maps. Under the further constant/sections
   adjunction each is the constant unit at D. The base change of the terminal object is
   terminal, and its unique terminal isomorphism does not change the constant section.
4. Transpose the left side successively through pro-etale inverse image, the comparison
   inverse image, and the etale constant functor, using def-weil-pbc-composite-adjunction.
   The defining conjugate unit equation for the commutation isomorphism, supplied by
   situation-conventions, rewrites this as transposition through the
   etale inverse image and then the comparison at D. The remaining adjuncts from steps
   2 and 3 send a to its pro-etale constant section on D. The right-adjoint commutation
   identifies the two base-change objects; its terminal component changes no section.
5. Naturality of the inverse-image hom bijection transposes the right side to the same
   constant-section map. Injectivity of the bijection proves the displayed equation in
   diagrammatic order. The calculations also apply to the zero ring, empty schemes,
   empty support, and the identity immersion. No supported unit identity is asserted.
-/
theorem cartierConstantComparison_normalization (A : Type (u + 1)) [CommRing A] :
    (∀ T : Scheme.{u},
      cartierConstantComparison A T =
          ((ProEtale.comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom ∧
        IsIso (cartierConstantComparison A T)) ∧
    (∀ {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i],
      (ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A) i).hom.app
          (ordinaryFiniteConstant A Z) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) D).map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _).symm
            (((sheafificationAdjunction Z.smallEtaleTopology
                (ModuleCat.{u + 1} A)).homEquiv _ _).symm
              (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ i).op
                (toSheafify D.smallEtaleTopology
                  ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A)))))) ≫
        ((ProEtale.comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom =
      (Scheme.proEtaleSheafInverseImage i (ModuleCat.{u + 1} A)).map
          (cartierConstantComparison A Z) ≫
        Scheme.proEtaleConstantInverseImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A)) := by
  have hnorm (T : Scheme.{u}) :
      cartierConstantComparison A T =
        ((ProEtale.comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom := by
    exact (ProEtale.comparison_constant_inverse A T (ModuleCat.of A A)).symm
  constructor
  · intro T
    refine ⟨hnorm T, ?_⟩
    rw [hnorm T]
    infer_instance
  · intro D Z i _
    have hr : ProEtale.lowerStarComparisonLowerStarIso (ModuleCat.{u + 1} A) i =
        ProEtale.lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A) := by
      apply Iso.ext
      apply NatTrans.ext
      funext S
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext W
      dsimp only [ProEtale.lowerStarComparisonLowerStarIso,
        ProEtale.lowerStarCompComparisonLowerStarIso]
      change 𝟙 _ = (𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      exact (S.obj.map_id _).symm
    have hc : ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A) i =
        ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) i := by
      unfold ProEtale.comparisonUpperStarUpperStarIso
        ProEtale.comparisonUpperStarCompUpperStarIso
      rw [hr]
    rw [hnorm Z, hc]
    simpa only [Iso.app_hom, ProEtale.etale_constant_inverse,
      ProEtale.ConstantProof.constantInverse, ProEtale.ConstantProof.constantDirect,
      Scheme.Hom.Etale, lowerStar, ordinaryFiniteConstant, constantSheaf,
      Functor.comp_obj, ProEtale.upperStar, Scheme.proEtaleSheafInverseImage,
      Scheme.proEtaleBaseChange, Scheme.smallEtaleTopology] using
      (ProEtale.comparison_constants A i).symm

end AlgebraicGeometry.Etale
