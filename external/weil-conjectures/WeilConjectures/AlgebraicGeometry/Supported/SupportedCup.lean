/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedConstantPresentation
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedFlatness
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleClosedConstantTensor

import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction

/-!
# Cup product with closed supports

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
proposition-purity-vector-bundles, and its coefficient calculation in the DAG
(blueprint: proposition-purity-vector-bundles).

The ordinary coefficient map is uniquely specified by restriction and multiplication of
constants. Its derived comparison uses the actual localization tensor comparison. The cup
product acts on the supported-Hom representatives from lemma-sections-support-closed-subscheme--1.
Its target is a Hom group in the unbounded derived category, including when tensoring two
bounded-below inputs produces an unbounded complex.

## Main definitions

- `cupCoefficientRestriction`, `cupCoefficientMultiplication`, `cupCoefficientMap`: the
  normalized underived coefficient maps.
- `cupSingleTensorMap`, `cupDerivedCoefficientMap`: their canonical localization comparison.
- `cupTensorShiftIso`: the right-shift-first sign convention.
- `cupHasDerivedCategory`, `CupDerivedCategory`, `CupPlus`, `cupSingle`: shared references
  to the existing localization, bounded-below category, and degree-zero embedding.
- `cupMonoidal`, `cupTensorObject`: shared references to the upstream derived tensor.
- `cupSupportedHom`, `cupComposite`, `supportedCup`: the unbounded output group and cup composite.

## Main statements

- `cupCoefficientMap_existsUnique`, `cupCoefficientMap_isIso`, `cupCoefficient_flat`:
  the quotient and idempotent coefficient calculation attached to the node.
- `cupDerivedCoefficientMap_isIso`: degree-zero flatness identifies the derived coefficients.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u c v w u1 u2 u3 u4 v1 v2 v3 v4

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- A named reference to the existing canonical localization structure, shared by all
occurrences below. This is the upstream instance, not a new localization.
Source: proposition-purity-vector-bundles and definition-small-pro-etale-site--1
(blueprint: proposition-purity-vector-bundles). -/
@[reducible]
noncomputable def cupHasDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
  inferInstance

/-- The existing fixed-scalar derived category with its canonical structure explicitly
shared. Source: proposition-purity-vector-bundles (blueprint: proposition-purity-vector-bundles). -/
abbrev CupDerivedCategory (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  @DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    _ _ (cupHasDerivedCategory P X)

/-- The upstream derived monoidal structure, named once for this coefficient datum.
Source: proposition-purity-vector-bundles, derived tensor (blueprint:
proposition-purity-vector-bundles). -/
@[reducible]
noncomputable def cupMonoidal (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    MonoidalCategory (CupDerivedCategory P X) := inferInstance

/-- The object part of the existing derived tensor using the shared instance.
Source: proposition-purity-vector-bundles (blueprint: proposition-purity-vector-bundles). -/
noncomputable abbrev cupTensorObject (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u})
    (F G : CupDerivedCategory P X) : CupDerivedCategory P X :=
  ((@curriedTensor (CupDerivedCategory P X) _ (cupMonoidal P X)).obj F).obj G

/-- The existing bounded-below subcategory with that same shared localization.
Source: proposition-purity-vector-bundles (blueprint: proposition-purity-vector-bundles). -/
abbrev CupPlus (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  @DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    _ _ (cupHasDerivedCategory P X)

/-- The actual degree-zero embedding with the shared canonical localization structure.
Source: proposition-purity-vector-bundles (blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupSingle (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient) ⥤ CupDerivedCategory P X :=
  @DerivedCategory.singleFunctor _ _ _ (cupHasDerivedCategory P X) 0

/-- Compare the specified finite coefficient sheaf with the constant pro-etale sheaf.
Source: proposition-purity-vector-bundles, coefficient calculation, and the constant-sheaf
adjunction. Both functors are left adjoint to evaluation at the terminal pro-etale object;
uniqueness of left adjoints gives the comparison preserving constant sections.
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupConstantIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    P.constant X ≅ (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)).obj (ModuleCat.of P.Coefficient P.Coefficient) :=
  (comparisonUpperStarConstantSheafIso P.Coefficient X).app
    (ModuleCat.of P.Coefficient P.Coefficient)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the actual finite coefficient unit to a closed support. The map is
adjoint to the constant-presheaf sheafification unit at the base change of the terminal
object, so on local constants it restricts the same scalar.
Source: proposition-purity-vector-bundles, the map q_D in the coefficient calculation
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupCoefficientRestriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (c : D ⟶ X) :
    P.constant X ⟶ (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).obj (P.constant D) :=
  (cupConstantIso P X).hom ≫
    ((constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.ProEt.isTerminalMkId X)).homEquiv
      (ModuleCat.of P.Coefficient P.Coefficient)
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) c).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))).symm
        ((toSheafify (Scheme.ProEt.topology D)
          ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
            (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ c).obj
              (Scheme.ProEt.mk (𝟙 X))))) ≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).map (cupConstantIso P D).inv

/-- Multiplication on the specified coefficient sheaf, transported from the tensor unit.
Source: proposition-purity-vector-bundles, multiplication of local constant functions
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupCoefficientMultiplication (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) : P.constant X ⊗ P.constant X ⟶ P.constant X :=
  (tensorIso (cupConstantIso P X) (cupConstantIso P X)).hom ≫
    (λ_ (𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)))).hom ≫ (cupConstantIso P X).inv

/-- The intersection immersion, with its scheme-theoretic pullback structure.
Source: proposition-purity-vector-bundles, V=Z times_X W and h:V into X
(blueprint: proposition-purity-vector-bundles). -/
noncomputable abbrev cupIntersection {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) :
    pullback i j ⟶ X := pullback.fst i j ≫ i

set_option backward.isDefEq.respectTransparency false in
private theorem cupRestriction_eq_laxUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (c : D ⟶ X) :
    cupCoefficientRestriction P c = (cupConstantIso P X).hom ≫
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) c) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).map (cupConstantIso P D).inv := by
  unfold cupCoefficientRestriction
  congr 1
  congr 1
  apply ((constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c)
    (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology D) (op (Scheme.ProEt.mk (𝟙 X)))).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cupLaxUnit_comp (P : WeilConjectures.PurityFiniteSetting.{u})
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) (p ≫ g)) =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) g) ≫
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) g).map
          (Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) p)) ≫
        (lowerStarComp (ModuleCat.{u + 1} P.Coefficient) p g).hom.app (𝟙_ _) := by
  have := Scheme.ProEt.isContinuous_overPullback g
  have := Scheme.ProEt.isContinuous_overPullback p
  have := Scheme.ProEt.isContinuous_overPullback (p ≫ g)
  exact Functor.ε_sheafPushforwardContinuous_of_iso_comp
    (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology D) (Scheme.ProEt.topology V)
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) p g).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cupRestriction_comp (P : WeilConjectures.PurityFiniteSetting.{u})
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) :
    cupCoefficientRestriction P g ≫
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) g).map (cupCoefficientRestriction P p) ≫
        (lowerStarComp (ModuleCat.{u + 1} P.Coefficient) p g).hom.app (P.constant V) =
      cupCoefficientRestriction P (p ≫ g) := by
  rw [cupRestriction_eq_laxUnit, cupRestriction_eq_laxUnit, cupRestriction_eq_laxUnit]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [(lowerStarComp (ModuleCat.{u + 1} P.Coefficient) p g).hom.naturality
    (cupConstantIso P V).inv]
  rw [cupLaxUnit_comp]
  simp only [Category.assoc]
  rfl

private theorem cupLaxUnit_mul {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom =
        (λ_ (𝟙_ D)).hom ≫ Functor.LaxMonoidal.ε F := by
  rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
  simp only [← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  exact leftUnitor_naturality _

private theorem cupTransportedUnit_mul {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]
    {A : D} {B : C} (eA : A ≅ 𝟙_ D) (eB : B ≅ 𝟙_ C) :
    ((eA.hom ≫ Functor.LaxMonoidal.ε F ≫ F.map eB.inv) ⊗ₘ
        (eA.hom ≫ Functor.LaxMonoidal.ε F ≫ F.map eB.inv)) ≫
        Functor.LaxMonoidal.μ F B B ≫
        F.map ((eB ⊗ᵢ eB).hom ≫ (λ_ (𝟙_ C)).hom ≫ eB.inv) =
      (eA ⊗ᵢ eA).hom ≫ (λ_ (𝟙_ D)).hom ≫ eA.inv ≫
        eA.hom ≫ Functor.LaxMonoidal.ε F ≫ F.map eB.inv := by
  dsimp only [tensorIso]
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  simp only [← Functor.map_comp, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    tensorHom_id, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp]
  simp only [← tensorHom_comp_tensorHom, id_whiskerRight, F.map_id,
    Category.id_comp, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ (eA.hom ⊗ₘ eA.hom) ≫ f ≫ F.map eB.inv) (cupLaxUnit_mul F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cupRestriction_mul (P : WeilConjectures.PurityFiniteSetting.{u})
    {V X : Scheme.{u}} (h : V ⟶ X) :
    (cupCoefficientRestriction P h ⊗ₘ cupCoefficientRestriction P h) ≫
        Functor.LaxMonoidal.μ (lowerStar (ModuleCat.{u + 1} P.Coefficient) h)
          (P.constant V) (P.constant V) ≫
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) h).map
          (cupCoefficientMultiplication P V) =
      cupCoefficientMultiplication P X ≫ cupCoefficientRestriction P h := by
  rw [cupRestriction_eq_laxUnit]
  unfold cupCoefficientMultiplication
  exact cupTransportedUnit_mul (lowerStar (ModuleCat.{u + 1} P.Coefficient) h)
    (cupConstantIso P X) (cupConstantIso P V)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cupLaxUnit_eq_constantMap (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i) =
      Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (ModuleCat.of _ (ULift.{u + 1} A)) := by
  apply Sheaf.hom_ext_of_ε_comp
  erw [Functor.ε_sheafToPresheaf_comp_map_ε_sheafPushforwardContinuous]
  change Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op
      (toSheafify (Scheme.ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of _ (ULift.{u + 1} A)))) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of _ (ULift.{u + 1} A)))) ≫
      (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} A))
        (ModuleCat.of _ (ULift.{u + 1} A))).hom
  exact ((sheafificationAdjunction (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} (ULift.{u + 1} A))).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of _ (ULift.{u + 1} A)))
      ((Scheme.proEtaleSheafDirectImage i (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
        (Scheme.proEtaleFixedConstantModule Z A))).apply_symm_apply
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op
        (toSheafify (Scheme.ProEt.topology Z)
          ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of _ (ULift.{u + 1} A))))) |>.symm

set_option backward.isDefEq.respectTransparency false in
private theorem cupLaxUnit_epi (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i)) := by
  rw [cupLaxUnit_eq_constantMap]
  let E := Scheme.sfIntrinsicModuleEquivalence X A
  let AZ := Scheme.proEtaleFixedConstantModule Z A
  let q : E.functor.obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i).obj AZ) ≅
      (Scheme.proEtaleConstantModuleDirectImage i A).obj
        (Scheme.proEtaleConstantModule Z A) :=
    (Scheme.sfIntrinsicDirectImageComparison i A).symm.app AZ ≪≫
      (Scheme.proEtaleConstantModuleDirectImage i A).mapIso
        (Scheme.proEtaleConstantModuleUnit Z A)
  let ρ := Scheme.proEtaleConstantDirectImageMap i
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (ModuleCat.of _ (ULift.{u + 1} A))
  have hr : E.functor.map ρ ≫ q.hom =
      (Scheme.proEtaleConstantModuleUnit X A).hom ≫
        Scheme.proEtaleClosedConstantRestriction i A := by
    dsimp [q, Scheme.proEtaleClosedConstantRestriction]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  obtain ⟨h, ⟨hc⟩⟩ := Scheme.proEtale_supported_constant_presentation A i
  have : Epi (Scheme.proEtaleClosedConstantRestriction i A) := Cofork.IsColimit.epi hc
  have : Epi (E.functor.map ρ ≫ q.hom) := by rw [hr]; infer_instance
  have hρ : Epi (E.functor.map ρ) := (epi_comp_iff_of_isIso _ q.hom).mp inferInstance
  exact E.functor.epi_of_epi_map hρ

set_option backward.isDefEq.respectTransparency false in
private theorem cupRestriction_epi (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (cupCoefficientRestriction P i) := by
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  rw [cupRestriction_eq_laxUnit]
  have : IsIso ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
      (cupConstantIso P Z).inv) := Functor.map_isIso _ _
  apply (epi_comp_iff_of_epi _ _).2
  exact (epi_comp_iff_of_isIso _ _).2 (cupLaxUnit_epi P.Ring i)

private theorem cupRestriction_factor (P : WeilConjectures.PurityFiniteSetting.{u})
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X) (hp : p ≫ g = h) :
    ∃ r : (lowerStar (ModuleCat.{u + 1} P.Coefficient) g).obj (P.constant D) ⟶
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) h).obj (P.constant V),
      cupCoefficientRestriction P g ≫ r = cupCoefficientRestriction P h := by
  subst h
  exact ⟨(lowerStar (ModuleCat.{u + 1} P.Coefficient) g).map (cupCoefficientRestriction P p) ≫
    (lowerStarComp (ModuleCat.{u + 1} P.Coefficient) p g).hom.app (P.constant V),
    cupRestriction_comp P p g⟩

/-- The coefficient multiplication map is uniquely determined by multiplying restrictions
of local constants. Source: proposition-purity-vector-bundles, coefficient calculation
(blueprint: proposition-purity-vector-bundles).

Proof: identify the coefficient constants with the tensor unit. Restriction then equals
lax monoidal direct-image unit, and those units commute with composition. Restrict both
factors to the intersection, apply the direct-image tensor comparison, and multiply there.
The lax unit law verifies the required normalization. The supported-constant cokernel
presentation makes each restriction epic, including for empty supports and the zero ring;
tensoring preserves these epimorphisms because the sheaf tensor functors are left adjoints.
Cancellation of their tensor product gives uniqueness. -/
theorem cupCoefficientMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃! μ : (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⊗
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) ⟶
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
          (P.constant (pullback i j)),
      (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫ μ =
        cupCoefficientMultiplication P X ≫ cupCoefficientRestriction P (cupIntersection i j) := by
  obtain ⟨ri, hri⟩ := cupRestriction_factor P (pullback.fst i j) i (cupIntersection i j) rfl
  obtain ⟨rj, hrj⟩ := cupRestriction_factor P (pullback.snd i j) j (cupIntersection i j)
    pullback.condition.symm
  let μ := (ri ⊗ₘ rj) ≫
    Functor.LaxMonoidal.μ (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j))
      (P.constant (pullback i j)) (P.constant (pullback i j)) ≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).map
      (cupCoefficientMultiplication P (pullback i j))
  have hμ : (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫ μ =
      cupCoefficientMultiplication P X ≫ cupCoefficientRestriction P (cupIntersection i j) := by
    dsimp only [μ]
    rw [tensorHom_comp_tensorHom_assoc, hri, hrj]
    exact cupRestriction_mul P (cupIntersection i j)
  have := cupRestriction_epi P i
  have := cupRestriction_epi P j
  have h₁ : Epi (cupCoefficientRestriction P i ▷ P.constant X) :=
    (tensorRight (P.constant X)).map_epi _
  have h₂ : Epi ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z) ◁ cupCoefficientRestriction P j) := (tensorLeft _).map_epi _
  have : Epi (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) := by
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  exact ⟨μ, hμ, fun ν hν ↦ (cancel_epi
    (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j)).mp (hν.trans hμ.symm)⟩

/-- The specified underived map mu: restrict both factors to the intersection and multiply.
The unique characterization uses the quotient maps, so this selects no arbitrary map.
Source: proposition-purity-vector-bundles, displayed coefficient map mu
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupCoefficientMap (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⊗
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j)) :=
  (cupCoefficientMap_existsUnique P i j).exists.choose

section CoefficientComparison

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option backward.isDefEq.respectTransparency.types false

set_option backward.defeqAttrib.useBackward true in
private theorem monoidal_mate
    {C : Type u1} {D : Type u2} {E : Type u3} {F : Type u4}
    [Category.{v1} C] [Category.{v2} D] [Category.{v3} E] [Category.{v4} F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.LaxMonoidal] [H.LaxMonoidal] [L₁.Monoidal] [L₂.Monoidal]
    [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.IsMonoidal] [adj₂.IsMonoidal]
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) [NatTrans.IsMonoidal β] :
    NatTrans.IsMonoidal (((mateEquiv adj₁ adj₂).symm β)) := by
  change NatTrans.IsMonoidal (_ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem constant_iso_eta (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    (cupConstantIso P X).hom = Functor.OplaxMonoidal.η
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X) := by
  unfold cupConstantIso comparisonUpperStarConstantSheafIso
  apply (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.Etale.isTerminalMkId X)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)).ofNatIsoRight
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u + 1} P.Coefficient) X.smallEtaleTopology
      (Scheme.ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X))))).homEquiv _ _ |>.injective
  simp only [Iso.app_hom]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (constantSheafAdj (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.isTerminalMkId X)).unit.app _ ≫
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
      (op (Scheme.Etale.mk (𝟙 X)))).map
      ((comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X).unit.app _ ≫
        (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).map
          (Functor.OplaxMonoidal.η
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))) ≫
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u + 1} P.Coefficient) X.smallEtaleTopology
      (Scheme.ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X)))).hom.app _
  erw [Adjunction.unit_app_unit_comp_map_η]
  have hp : (constantSheafAdj (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf _ _)).app
        (op (Scheme.ProEt.mk (𝟙 X))) := by
    simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
    rw [Adjunction.homEquiv_unit]
    have : Functor.OplaxMonoidal.η
      (presheafToSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient)) = 𝟙 _ := rfl
    simp [this]
    rfl
  have he : (constantSheafAdj X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf _ _)).app
        (op (Scheme.Etale.mk (𝟙 X))) := by
    simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
    rw [Adjunction.homEquiv_unit]
    have : Functor.OplaxMonoidal.η
      (presheafToSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)) = 𝟙 _ := rfl
    simp [this]
    rfl
  rw [hp, he]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_monoidal (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    NatTrans.IsMonoidal
      (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient)) := by
  exact monoidal_mate
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Z)
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)
    (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} P.Coefficient)).inv

private theorem etale_transition (P : WeilConjectures.PurityFiniteSetting.{u})
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X) (hp : p ≫ g = h) :
    Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) g) ≫
      Etale.constantModulePushforwardMap P.Coefficient
        (ModuleCat.of P.Coefficient P.Coefficient) g h p hp =
    Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) h) := by
  unfold Etale.constantModulePushforwardMap
  erw [Etale.upperStarConstantSheafIso_hom_app_tensorUnit
    (ModuleCat.{u + 1} P.Coefficient) p]
  erw [Adjunction.unit_app_unit_comp_map_η]
  exact (Etale.ε_lowerStar_comp p g h hp.symm).symm

private theorem etale_multiplication (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) :
    Etale.constantModuleMultiplication P.Coefficient T =
      (λ_ (𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))).hom := by
  change (tensorIso (Iso.refl (𝟙_ (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} P.Coefficient)))) (Iso.refl _)).hom ≫
      (λ_ (𝟙_ _)).hom = _
  simp only [tensorIso_hom, Iso.refl_hom, tensorHom_id, id_whiskerRight, Category.id_comp]

private theorem etale_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i) ⊗ₘ
      Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) j)) ≫
      Etale.closedConstantTensorMap P.Coefficient i j =
    (λ_ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))).hom ≫
      Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (cupIntersection i j)) := by
  dsimp only [Etale.closedConstantTensorMap, Etale.closedConstantRestriction,
    Etale.closedConstantRestriction₂]
  erw [tensorHom_comp_tensorHom_assoc]
  erw [etale_transition P (pullback.fst i j) i (cupIntersection i j) rfl,
    etale_transition P (pullback.snd i j) j (cupIntersection i j) pullback.condition.symm]
  erw [etale_multiplication P (pullback i j)]
  exact cupLaxUnit_mul
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j))

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_restriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    cupCoefficientRestriction P i =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ≫
      (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient)).app
        (𝟙_ (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) := by
  have := comparison_monoidal P i
  have h := NatTrans.IsMonoidal.unit
    (τ := lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient))
  simp only [Functor.LaxMonoidal.comp_ε, Category.assoc] at h
  have hi : (cupConstantIso P Z).inv =
      Functor.LaxMonoidal.ε (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z) := by
    apply (cancel_mono (cupConstantIso P Z).hom).mp
    rw [Iso.inv_hom_id, constant_iso_eta, Functor.Monoidal.ε_η]
    rfl
  rw [cupRestriction_eq_laxUnit, constant_iso_eta, hi]
  apply (cancel_epi (Functor.LaxMonoidal.ε
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))).mp
  simp only [Functor.Monoidal.ε_η_assoc]
  exact h.symm

private theorem comparison_multiplication {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] :
    (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
      (λ_ (𝟙_ D)).hom ≫ inv (Functor.OplaxMonoidal.η F) =
    Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom := by
  apply (cancel_epi (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F)).mp
  simp only [tensorHom_comp_tensorHom_assoc, Functor.Monoidal.ε_η, tensorHom_id,
    id_whiskerRight, Category.id_comp]
  rw [cupLaxUnit_mul, Functor.Monoidal.inv_η]

private theorem comparison_normalization {C : Type*} [Category C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {L M N : C} {L' M' N' : D} (ei : F.obj L ≅ L') (ej : F.obj M ≅ M')
    (eh : F.obj N ≅ N') (qi : 𝟙_ C ⟶ L) (qj : 𝟙_ C ⟶ M) (qh : 𝟙_ C ⟶ N)
    (μ : L ⊗ M ⟶ N) (hμ : (qi ⊗ₘ qj) ≫ μ = (λ_ (𝟙_ C)).hom ≫ qh) :
    ((F.map qi ≫ ei.hom) ⊗ₘ (F.map qj ≫ ej.hom)) ≫
      ((ei.inv ⊗ₘ ej.inv) ≫ Functor.LaxMonoidal.μ F L M ≫ F.map μ ≫ eh.hom) =
    Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom ≫
      F.map qh ≫ eh.hom := by
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [← F.map_comp_assoc, hμ, F.map_comp, Category.assoc]

/-- The coefficient map is invertible. Source: proposition-purity-vector-bundles, coefficient
calculation (blueprint: proposition-purity-vector-bundles).
Proof: the existing etale closed-constant tensor map is invertible and preserves the
normalization by constant sections. The strong monoidal comparison inverse image preserves
this isomorphism, and base change identifies its three coefficients with the specified
pro-etale direct images. The comparison unit agrees with cupConstantIso, and the monoidal
mate identity identifies the restriction maps. The transported isomorphism therefore has
exactly the normalization characterizing cupCoefficientMap; uniqueness identifies them. -/
theorem cupCoefficientMap_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : IsIso (cupCoefficientMap P i j) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := comparisonUpperStar A X
  let Li := Etale.closedConstantModule P.Coefficient i
  let Lj := Etale.closedConstantModule P.Coefficient j
  have := isIso_lowerStarComparisonUpperStarBaseChange i A
  have := isIso_lowerStarComparisonUpperStarBaseChange j A
  have := isIso_lowerStarComparisonUpperStarBaseChange (cupIntersection i j) A
  let ei := asIso ((lowerStarComparisonUpperStarBaseChange i A).app (P.constantEtale Z))
  let ej := asIso ((lowerStarComparisonUpperStarBaseChange j A).app (P.constantEtale W))
  let eh := asIso ((lowerStarComparisonUpperStarBaseChange (cupIntersection i j) A).app
    (P.constantEtale (pullback i j)))
  let μ := (ei.inv ⊗ₘ ej.inv) ≫ Functor.LaxMonoidal.μ F Li Lj ≫
    F.map (Etale.closedConstantTensorMap P.Coefficient i j) ≫ eh.hom
  have he : IsIso (Etale.closedConstantTensorMap P.Coefficient i j) :=
    (Etale.closedConstantTensor P.Coefficient X i j i (𝟙 X)).2.2.2.2.2.2.2.2.2.1
  have hm : (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫ μ =
      cupCoefficientMultiplication P X ≫ cupCoefficientRestriction P (cupIntersection i j) := by
    rw [comparison_restriction, comparison_restriction, comparison_restriction]
    have heq : cupConstantIso P X = asIso (Functor.OplaxMonoidal.η F) :=
      Iso.ext (constant_iso_eta P X)
    rw [cupCoefficientMultiplication, heq]
    change _ = ((Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫
      (λ_ (𝟙_ _)).hom ≫ inv (Functor.OplaxMonoidal.η F)) ≫ _
    erw [comparison_multiplication F]
    -- Keep reassociation abstract instead of reducing concrete sheaf morphisms.
    conv_rhs => rw [Category.assoc]
    exact comparison_normalization F ei ej eh
      (Functor.LaxMonoidal.ε (Etale.lowerStar A i))
      (Functor.LaxMonoidal.ε (Etale.lowerStar A j))
      (Functor.LaxMonoidal.ε (Etale.lowerStar A (cupIntersection i j)))
      (Etale.closedConstantTensorMap P.Coefficient i j) (etale_normalization P i j)
  have hq : μ = cupCoefficientMap P i j :=
    (cupCoefficientMap_existsUnique P i j).unique hm
      (cupCoefficientMap_existsUnique P i j).exists.choose_spec
  rw [← hq]
  change IsIso (((ei.symm ⊗ᵢ ej.symm) ≪≫ Functor.Monoidal.μIso F Li Lj ≪≫
    F.mapIso (asIso (Etale.closedConstantTensorMap P.Coefficient i j)) ≪≫ eh).hom)
  infer_instance

end CoefficientComparison

/-- Flatness of each closed direct image of constants, without a geometric-stalk assumption.
Source: proposition-purity-vector-bundles, idempotent argument for flatness
(blueprint: proposition-purity-vector-bundles).
Proof: the coefficient ring is finite. The étale constant coefficient module is the tensor
unit, hence flat. The proved étale open-closed flatness theorem shows that its direct image
under the closed immersion is flat. Comparison inverse image preserves flatness, and its
base-change comparison with this closed direct image is an isomorphism because a closed
immersion is quasi-compact and quasi-separated. Transport flatness through that isomorphism.
This uses no conservativity assertion for geometric stalks of pro-étale sheaves. -/
theorem cupCoefficient_flat (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z)) := by
  set_option backward.isDefEq.respectTransparency true in
    have : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    have : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
    let A := ModuleCat.{u + 1} P.Coefficient
    have := isIso_lowerStarComparisonUpperStarBaseChange i A
    let e := asIso ((lowerStarComparisonUpperStarBaseChange i A).app (P.constantEtale Z))
    have hf : ObjectProperty.flat ((Etale.lowerStar A i).obj (P.constantEtale Z)) :=
      (openClosedFlatness_etale P.Coefficient i.openComplement.ι i
        i.range_eq_compl_range_openComplement_ι (P.constantEtale X)).2.2 _
          (ObjectProperty.prop_unit ObjectProperty.flat)
    exact ObjectProperty.prop_of_iso ObjectProperty.flat e
      (flat_comparisonUpperStar_obj hf)

/-- The canonical degree-zero comparison, constructed before specializing the category.
Source: proposition-purity-vector-bundles, the localization tensor comparison followed by the
ordinary single-complex comparison (blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupSingleTensorMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    (L M : C) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj (L ⊗ M) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app L)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M)).hom ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)).hom) ≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (L ⊗ M)).inv

/-- Apply a sheaf coefficient map after the canonical degree-zero tensor comparison.
The construction is made in a general category to keep the localization structure shared.
Source: proposition-purity-vector-bundles, theta induced by mu (blueprint:
proposition-purity-vector-bundles). -/
@[irreducible]
noncomputable def cupDerivedCoefficientMap {C : Type c} [Category.{v} C] [Abelian C]
    [hD : HasDerivedCategory.{w} C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (DerivedCategory C)] [(DerivedCategory.Q (C := C)).LaxMonoidal]
    {L M N : C} (μ : L ⊗ M ⟶ N) :
    (DerivedCategory.singleFunctor C 0).obj L ⊗
        (DerivedCategory.singleFunctor C 0).obj M ⟶
      (DerivedCategory.singleFunctor C 0).obj N :=
  cupSingleTensorMap L M ≫ (DerivedCategory.singleFunctor C 0).map μ

set_option backward.isDefEq.respectTransparency true in
private theorem cupSingleTensorMap_isIso {C : Type c} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C]
    [hB : BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (L M : C) (hL : ObjectProperty.flat L) :
    IsIso (cupSingleTensorMap L M) := by
  let K := (HomologicalComplex.single C (.up ℤ) 0).obj L
  let T := (HomologicalComplex.single C (.up ℤ) 0).obj M
  let H := HomotopyCategory.quotient C (.up ℤ)
  have hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (H.obj K) :=
    (HomotopyCategory.kFlat_quotient_obj_iff K).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have := DerivedCategory.isIso_μ_Qh_of_kFlat (H.obj K) (H.obj T) hK
  have : IsIso (Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T) := by
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K T) := by
    change IsIso (tensorHom _ _ ≫
      Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T ≫ _)
    infer_instance
  dsimp only [K, T] at this
  unfold cupSingleTensorMap
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single C (.up ℤ) 0).obj L)
      ((HomologicalComplex.single C (.up ℤ) 0).obj M)) := this
  have hmap : IsIso (DerivedCategory.Q.map
      ((((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)).hom)) :=
    inferInstance
  have ht : IsIso (tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app L)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)).hom := inferInstance
  have hi : IsIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app (L ⊗ M)).inv :=
    inferInstance
  exact IsIso.comp_isIso' ht (IsIso.comp_isIso' hμ (IsIso.comp_isIso' hmap hi))

private theorem cupDerivedCoefficientMap_isIso_of_flat {C : Type c} [Category.{v} C]
    [Abelian C] [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [hB : BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {L M N : C} (μ : L ⊗ M ⟶ N) [hμ : IsIso μ] (hL : ObjectProperty.flat L) :
    IsIso (cupDerivedCoefficientMap μ) := by
  have h := cupSingleTensorMap_isIso L M hL
  unfold cupDerivedCoefficientMap
  exact IsIso.comp_isIso' h (Functor.map_isIso _ μ)

private theorem cupDerivedPair_isIso {C : Type c} [Category.{v} C]
    [Abelian C] [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [hB : BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (p : Σ m : MonoidalCategory (DerivedCategory C),
      letI := m
      (DerivedCategory.Q (C := C)).LaxMonoidal)
    (e : p = ⟨inferInstance, inferInstance⟩)
    {L M N : C} (μ : L ⊗ M ⟶ N) [hμ : IsIso μ] (hL : ObjectProperty.flat L) :
    letI := p.1
    letI := p.2
    IsIso (cupDerivedCoefficientMap μ) := by
  subst p
  exact cupDerivedCoefficientMap_isIso_of_flat μ hL

/-- The derived coefficient comparison is invertible. Source: proposition-purity-vector-bundles,
K-flat tensor descent (blueprint: proposition-purity-vector-bundles).
Proof: cupCoefficient_flat makes each degree-zero supported coefficient K-flat: tensoring
an acyclic complex by an exact tensor functor preserves its kernels, images and cohomology.
Thus the localization tensor comparison in cupSingleTensorMap is invertible by
isIso_mu_Qh_of_kFlat and the quotient monoidal comparison. The single-complex comparison
is an isomorphism. Finally cupCoefficientMap_isIso inverts the remaining factor. -/
theorem cupDerivedCoefficientMap_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j)) := by
  exact cupDerivedPair_isIso
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))
    (hD := cupHasDerivedCategory P X)
    (hM := sheafMonoidalCategory (ModuleCat.{u + 1} P.Coefficient) X)
    (hB := sheafBraidedCategory (ModuleCat.{u + 1} P.Coefficient) X)
    (L := (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z))
    (M := (lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W))
    (N := (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
      (P.constant (pullback i j)))
    (hμ := cupCoefficientMap_isIso P i j)
    ⟨cupMonoidal P X, inferInstance⟩ rfl
    (cupCoefficientMap P i j) (cupCoefficient_flat P i)

/-- The right-shift-first comparison in a monoidal category with both tensor-shift
structures. On K-flat cochain representatives, its sign on P[a]^r tensor Q[b]^s is
(-1)^(b r). Source: proposition-purity-vector-bundles, the sign-normalized shift comparison
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupTensorShiftIso {C : Type c} [Category.{v} C]
    [hM : MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    (F G : C) (a b : ℤ) : F⟦a⟧ ⊗ G⟦b⟧ ≅ (F ⊗ G)⟦a + b⟧ :=
  (((curriedTensor C).obj (F⟦a⟧)).commShiftIso b).app G ≪≫
    (shiftFunctor C b).mapIso
      ((((curriedTensor C).flip.obj G).commShiftIso a).app F) ≪≫
    (shiftFunctorAdd C a b).symm.app _

/-- Supported groups for an arbitrary unbounded target, by the node's Hom convention.
For bounded-below targets supported_cohomology_hom identifies this with derived supported
sections. Source: proposition-purity-vector-bundles, unbounded output convention
(blueprint: proposition-purity-vector-bundles). -/
abbrev cupSupportedHom (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (K : CupDerivedCategory P X) (r : ℤ) :=
  (cupSingle P X).obj
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)) ⟶ K⟦r⟧

/-- Compose the inverse coefficient comparison, tensor of representatives, and the
right-shift-first comparison. Source: proposition-purity-vector-bundles, the displayed cup composite
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def cupComposite {C : Type c} [Category.{v} C]
    [hM : MonoidalCategory C] [HasShift C ℤ]
    [∀ K : C, ((curriedTensor C).obj K).CommShift ℤ]
    [∀ K : C, ((curriedTensor C).flip.obj K).CommShift ℤ]
    {L M N F G : C} (θ : L ⊗ M ⟶ N) (hθ : IsIso θ)
    (a b : ℤ) (α : L ⟶ F⟦a⟧) (β : M ⟶ G⟦b⟧) : N ⟶ (F ⊗ G)⟦a + b⟧ :=
  @inv _ _ _ _ θ hθ ≫ (α ⊗ₘ β) ≫ (cupTensorShiftIso F G a b).hom

/-- The supported cup product, on the supported-Hom representatives supplied by
supported_cohomology_hom. The inputs are bounded below, the integers a,b are arbitrary,
and the output uses the ambient unbounded derived category.
Source: blueprint main-20261015, proposition-purity-vector-bundles, displayed composite
(blueprint: proposition-purity-vector-bundles). -/
noncomputable def supportedCup (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} [X.Over (Spec (CommRingCat.of P.field.k))]
    (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (F G : CupPlus P X)
    (a b : ℤ) (α : cupSupportedHom P i F.obj a) (β : cupSupportedHom P j G.obj b) :
    cupSupportedHom P (cupIntersection i j)
      (cupTensorObject P X F.obj G.obj) (a + b) :=
  cupComposite (C := CupDerivedCategory P X) (hM := cupMonoidal P X)
    (L := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)))
    (M := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) j).obj (P.constant W)))
    (N := (cupSingle P X).obj
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
        (P.constant (pullback i j))))
    (F := F.obj) (G := G.obj)
    (cupDerivedCoefficientMap (hD := cupHasDerivedCategory P X)
      (hDM := cupMonoidal P X) (cupCoefficientMap P i j))
    (cupDerivedCoefficientMap_isIso P i j) a b α β

end AlgebraicGeometry.ProEtale
