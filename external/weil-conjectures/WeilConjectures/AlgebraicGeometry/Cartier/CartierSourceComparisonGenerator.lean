/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
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
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison
import WeilConjectures.AlgebraicGeometry.Cartier.CartierConstantComparisonNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit

/-!
# Supported generators under the Cartier source comparison

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator).

The general unit equation and its finite-coefficient generator consequence use the
specified comparison maps. They assert neither a Kummer class nor a scalar-unit property.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem constantDirect_section (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) (U : Z.ProEtᵒᵖ) (a : A) :
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
        (ModuleCat.of A A)).hom.app U
        ((toSheafify (Scheme.ProEt.topology Z)
          ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.proEtaleBaseChange i).op.obj U) a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Z)
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))
      ((Scheme.proEtaleSheafDirectImage i (ModuleCat.{u + 1} A)).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).apply_symm_apply
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U a) h

private theorem comparisonConstant_section (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (U : T.Etaleᵒᵖ) (a : A) :
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).symm
      (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))))).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.toProEt T).op.obj U) a := by
  have h := ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).apply_symm_apply
    (Functor.whiskerLeft (Scheme.toProEt T).op
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U a) h

private theorem normalizedIso_unit {C : Type*} [Category C]
    {P Q R S T : C} (u : P ⟶ Q) (γ : P ⟶ R) [Epi γ]
    (ρ : R ⟶ S) (α : Q ≅ S) (e : Q ⟶ T) (t : T ⟶ S)
    (hα : u ≫ α.hom = γ ≫ ρ) (he : u ≫ e ≫ t = γ ≫ ρ) :
    ρ ≫ (α.inv ≫ e ≫ t) = ρ := by
  apply (cancel_epi γ).1
  calc
    _ = (γ ≫ ρ) ≫ (α.inv ≫ e ≫ t) := (Category.assoc _ _ _).symm
    _ = (u ≫ α.hom) ≫ (α.inv ≫ e ≫ t) := by rw [hα]
    _ = u ≫ e ≫ t := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = γ ≫ ρ := he

/-- The specified source comparison transports the ordinary supported constant unit.
Source: blueprint sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator).

Proof: transpose the equation through the comparison adjunction at Z. The source
comparison is its defining mate followed by the constant comparison at D, identified
by part (1) of lem-sfb-cartier-constant-comparison-normalization. The mate-transpose
identity reduces the equation to the ordinary supported unit and the transposed
constant comparisons. Transpose once more through sheafification and evaluate on
constant presheaf sections. The source library's formula for the ordinary constant
unit, and the inverse laws of the sheafification Hom equivalence for both comparison
maps and the pro-etale direct-image map, send each coefficient to the same section.
The direct-image commutation isomorphism acts identically on section modules.
Injectivity of both Hom equivalences gives the equation. This uses no Cartier or
finite-coefficient hypothesis and does not need the inverse-image normalization square.
-/
theorem cartierSourceComparison_supportedConstantUnit
    (A : Type (u + 1)) [CommRing A] {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map
        (Etale.supportedConstantUnit A i) ≫ geoCartierSourceComparison A i =
      Etale.cartierConstantComparison A Z ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A) := by
  unfold geoCartierSourceComparison geoCartierConstant
  rw [← ((Etale.cartierConstantComparison_normalization A).1 D).1]
  apply ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  unfold lowerStarComparisonUpperStarBaseChange
  rw [adjunctionMate_transpose]
  rw [Etale.cartierConstantComparison, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rw [Etale.cartierConstantComparison, Equiv.apply_symm_apply]
  have hu : Etale.supportedConstantUnit A i =
      Etale.constantSheafUnit i (ModuleCat.of A A) := by
    unfold Etale.supportedConstantUnit Etale.constantSheafUnit
    rw [Adjunction.homEquiv_unit]
    rfl
  have hd (S : Sheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A))
      (W : Z.Etaleᵒᵖ) :
      (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app S).hom.app W) =
        𝟙 _ := by
    dsimp only [lowerStarCompComparisonLowerStarIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  apply ((sheafificationAdjunction Z.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let c (T : Scheme.{u}) :=
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).symm
      (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A)))))
  change (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app
      ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A))).hom.app W)
      ((c D).hom.app ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)
        ((Etale.supportedConstantUnit A i).hom.app W
          ((toSheafify Z.smallEtaleTopology
            ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))) =
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app ((Scheme.toProEt Z).op.obj W)
      ((c Z).hom.app W ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))
  rw [hd]
  change (c D).hom.app ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)
      ((Etale.supportedConstantUnit A i).hom.app W
        ((toSheafify Z.smallEtaleTopology
          ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a)) =
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app ((Scheme.toProEt Z).op.obj W)
      ((c Z).hom.app W ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))
  rw [hu, Etale.constantSheafUnit_app_toSheafify]
  dsimp only [c]
  erw [comparisonConstant_section, comparisonConstant_section, constantDirect_section]
  rfl

/-- The identity identification between the general supported constant and the published
finite-coefficient supported object. It only unfolds their definitions and has no choices.
Source: blueprint sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator). -/
def cartierSourceComparisonSupportIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (lowerStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) i).obj
        (geoCartierConstant (Scheme.finiteTateCoefficient l E n) D) ≅
      Etale.cartierSupported l E n i := by
  unfold Etale.cartierSupported geoCartierConstant
  exact Iso.refl _

/-- Every normalized finite-coefficient source isomorphism differs from the canonical
source comparison by an automorphism preserving the supported unit and its generators.
Source: blueprint sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator).

Proof: the preceding general equation and the assumed equation for `α` have the same
right-hand side. Postcompose the latter with `α.inv` and the canonical source comparison.
Cancel the invertible constant comparison, using part (1) of
lem-sfb-cartier-constant-comparison-normalization, to obtain the unit equation. The source
comparison is invertible by lem-sfb-geo-cartier-source-comparison, so `α.inv` followed by
it is an automorphism. Evaluate the unit equation on every pro-etale object and constant
section; the identity support identification and the definitions of `cartierSupportedUnit`
and `cartierSupportedGenerator` give the last clause. Associativity and the inverse
equations apply also to zero coefficients,
empty schemes, empty support, the identity immersion, and the canonical choice of `α`.
-/
theorem cartierSourceComparison_fixes_supportedGenerator
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (α : (comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Z).obj
          ((Etale.lowerStar
            (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) i).obj
              (Etale.ordinaryFiniteConstant (Scheme.finiteTateCoefficient l E n) D)) ≅
        Etale.cartierSupported l E n i)
    (hα : (comparisonUpperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) Z).map
          (Etale.supportedConstantUnit (Scheme.finiteTateCoefficient l E n) i) ≫ α.hom =
        Etale.cartierConstantComparison (Scheme.finiteTateCoefficient l E n) Z ≫
          Etale.cartierSupportedUnit l E n i) :
    IsIso (α.inv ≫ geoCartierSourceComparison (Scheme.finiteTateCoefficient l E n) i ≫
      (cartierSourceComparisonSupportIso l E n i).hom) ∧
      Etale.cartierSupportedUnit l E n i ≫
          (α.inv ≫ geoCartierSourceComparison (Scheme.finiteTateCoefficient l E n) i ≫
            (cartierSourceComparisonSupportIso l E n i).hom) =
        Etale.cartierSupportedUnit l E n i ∧
      ∀ (U : Z.ProEtᵒᵖ) (a : Scheme.finiteTateCoefficient l E n),
        (α.inv ≫ geoCartierSourceComparison (Scheme.finiteTateCoefficient l E n) i ≫
          (cartierSourceComparisonSupportIso l E n i).hom).hom.app U
            (Etale.cartierSupportedGenerator l E n i U a) =
          Etale.cartierSupportedGenerator l E n i U a := by
  have hγ := (Etale.cartierConstantComparison_normalization
    (Scheme.finiteTateCoefficient l E n)).1 Z |>.2
  have hbase := cartierSourceComparison_supportedConstantUnit
    (Scheme.finiteTateCoefficient l E n) i
  have hsupp : (Scheme.proEtaleConstantDirectImageMap i
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (ModuleCat.of (Scheme.finiteTateCoefficient l E n)
        (Scheme.finiteTateCoefficient l E n))) ≫
      (cartierSourceComparisonSupportIso l E n i).hom =
      Etale.cartierSupportedUnit l E n i := by
    unfold cartierSourceComparisonSupportIso Etale.cartierSupported Etale.cartierSupportedUnit
    simp only [id_eq, Iso.refl_hom, Category.comp_id]
    rfl
  have hbase' := congrArg
    (fun f ↦ f ≫ (cartierSourceComparisonSupportIso l E n i).hom) hbase
  rw [Category.assoc, Category.assoc, hsupp] at hbase'
  have hu := normalizedIso_unit _ _ _ α _ _ hα hbase'
  refine ⟨by infer_instance, hu, ?_⟩
  intro U a
  have hgen : (Etale.cartierSupportedUnit l E n i).hom.app U
      ((toSheafify (Scheme.ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj
          (ModuleCat.of (Scheme.finiteTateCoefficient l E n)
            (Scheme.finiteTateCoefficient l E n)))).app U a) =
      Etale.cartierSupportedGenerator l E n i U a := by
    unfold Etale.cartierSupportedUnit Etale.cartierSupportedGenerator Etale.cartierSupported
    simpa only [id_eq] using constantDirect_section (Scheme.finiteTateCoefficient l E n) i U a
  have hh := congrArg
    (fun f : (constantSheaf (Scheme.ProEt.topology Z)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))).obj
        (ModuleCat.of (Scheme.finiteTateCoefficient l E n)
          (Scheme.finiteTateCoefficient l E n)) ⟶
        Etale.cartierSupported l E n i ↦ f.hom.app U
          ((toSheafify (Scheme.ProEt.topology Z)
            ((Functor.const Z.ProEtᵒᵖ).obj
              (ModuleCat.of (Scheme.finiteTateCoefficient l E n)
                (Scheme.finiteTateCoefficient l E n)))).app U a)) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply] at hh
  rw [hgen] at hh
  exact hh

end AlgebraicGeometry.ProEtale
