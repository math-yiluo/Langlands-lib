/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

/-!
# Actual finite coefficient maps and their normalized restriction comparison

Source: blueprint main-20261015, prop-weil-pbc-scalar-extension, coefficient maps;
Bhatt--Scholze, Proposition 6.8.14; Stacks Tags 03EL and 0D6D
(blueprint: def-weil-pbc-actual-finite-coefficient-transport).

The integer inclusion is the existing restriction of the field embedding. Quotient
maps use the actual valuation rings and the recorded adic ideals. Finite projections
fix the completed map uniquely. Its restriction comparison specializes the existing
ordinary-adjunction and flat-term K-flat normalization, without new choices.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
-- Avoid underdetermined max-universe instances from the auxiliary operations framework.
-- The fixed-size PBC instances still provide the same canonical structures.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E F : Type (u + 1)) [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
  (i : E →ₐ[Padic l] F)

private theorem coefficientMap_comp (T : Scheme.{u})
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] (f : A →+* B) (g : B →+* C) :
    AdicCoefficients.coefficientMap T f ≫ AdicCoefficients.coefficientMap T g =
      AdicCoefficients.coefficientMap T (g.comp f) := by
  rw [AdicCoefficients.coefficientMap, AdicCoefficients.coefficientMap,
    ← Functor.map_comp]
  congr 1

-- The strict quotient systems use the same integer inclusion at every index.
private theorem levelConstantComparison_eq (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison T d n).hom =
      AdicCoefficients.constantComparison T (A ⧸ d.ideal ^ (n + 1)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings T d).obj (op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison T d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec U b

private theorem levelConstantComparison_naturality (T : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) ≫
        (pbcLevelConstantComparison T dB n).hom =
      (pbcLevelConstantComparison T dA n).hom ≫ AdicCoefficients.coefficientMap T q := by
  rw [levelConstantComparison_eq, levelConstantComparison_eq]
  change (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _ =
    (presheafToSheaf _ CommRingCat).map _ ≫
      (presheafToSheaf _ CommRingCat).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

private theorem completedCoefficientMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

private theorem finiteCoefficientMap_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y q) ≫ completedFiniteCoefficientMap g dB n =
      completedFiniteCoefficientMap g dA n ≫ AdicCoefficients.coefficientMap X q := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hinv : AdicCoefficients.coefficientMap Y q ≫
      (pbcLevelConstantComparison Y dB n).inv =
    (pbcLevelConstantComparison Y dA n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) := by
    apply (Iso.eq_inv_comp _).2
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq _).2
    exact (levelConstantComparison_naturality Y dA dB n q).symm
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = _
  rw [← L.map_comp_assoc, hinv, L.map_comp, Category.assoc]
  erw [reassoc_of% (proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom q))]
  simp only [Category.assoc]
  rw [levelConstantComparison_naturality]

end AlgebraicGeometry.Scheme
