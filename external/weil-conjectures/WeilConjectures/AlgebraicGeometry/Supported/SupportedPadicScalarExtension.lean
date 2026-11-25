/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import all WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import all WeilConjectures.CategoryTheory.FlatScalarUnit
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import all WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Unique
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import all WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.SixFunctors.Finite.Stalk
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Data.ZMod.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import all WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.SixFunctors.Finite.Exact
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExt

/-! # Scalar extension of the supported integral constant

Source: the source paragraph of step (3) of the diagonal tower construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] comparisonUpperStar diagonalScalarExtension

private def integralConstantForgetIso (X : Scheme.{u}) :
    Etale.supportedIntegralConstant X ≅
      (Etale.RawModuleScalarComparison.forget (ULift.{u + 1} ℤ) X).obj
        (Etale.ordinaryFiniteConstant (ULift.{u + 1} ℤ) X) := by
  let R := ULift.{u + 1} ℤ
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let P := (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R)
  let e := sheafifyComposeIso X.smallEtaleTopology U P
  exact { hom := ⟨e.hom⟩
          inv := ⟨e.inv⟩
          hom_inv_id := by ext : 1; exact e.hom_inv_id
          inv_hom_id := by ext : 1; exact e.inv_hom_id }

private theorem integralConstantForgetIso_hom (X : Scheme.{u}) :
    (integralConstantForgetIso X).hom =
      Etale.ordinaryFiniteIntegralGenerator (ULift.{u + 1} ℤ) X := by
  let R := ULift.{u + 1} ℤ
  let J := X.smallEtaleTopology
  let U := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let P := (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R)
  let t : IsTerminal (Scheme.Etale.mk (𝟙 X)) := Etale.terminalEtaleIsTerminal X
  apply ((constantSheafAdj J AddCommGrpCat.{u + 1} t).homEquiv _ _).injective
  unfold Etale.ordinaryFiniteIntegralGenerator
  erw [Equiv.apply_symm_apply]
  rw [constantSheafAdj_homEquiv_apply]
  have hfac := congr_app (sheafComposeIso_hom_fac J U P)
    (op (Scheme.Etale.mk (𝟙 X)))
  change (toSheafify J (P ⋙ U)).app _ ≫
      (sheafifyComposeIso J U P).hom.app _ = _
  calc
    (toSheafify J (P ⋙ U)).app _ ≫ (sheafifyComposeIso J U P).hom.app _ =
        (Functor.whiskerRight (toSheafify J P) U).app _ := hfac
    _ = _ := by ext x; rfl

private theorem etale_supported_integral_universal (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i]
    (H : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f :
        (Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
          (Etale.ordinaryFiniteConstant A X) ⟶ H ↦
      Etale.supportedIntegralGenerator A i ≫
        (Etale.RawModuleScalarComparison.forget A Z).map f) := by
  let R := ULift.{u + 1} ℤ
  let φ : R →+* A := (Int.castRingHom A).comp ULift.ringEquiv.toRingHom
  obtain ⟨η, _, hη, _⟩ := Etale.exists_supported_kummer_scalar_maps Z 0 A φ i
  let U := Etale.RawModuleScalarComparison.forget R Z
  let G := (Etale.lowerStar (ModuleCat.{u + 1} R) i).obj
    (Etale.ordinaryFiniteConstant R X)
  let Q := (Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
    (Etale.ordinaryFiniteConstant A X)
  let j := (Etale.lowerStar (ModuleCat.{u + 1} R) i).map η
  have hj := Etale.finite_ordinary_scalar_unit Z φ i
    (Etale.ordinaryFiniteConstant R X) (Etale.ordinaryFiniteConstant A X) η
    (Etale.constant_ordinary_scalar_unit X φ η hη) H
  change Function.Bijective (fun f : Q ⟶ H ↦
    j ≫ (Sheaf.restrictScalars Z.smallEtaleTopology φ).map f) at hj
  let a := (Etale.lowerStar AddCommGrpCat.{u + 1} i).mapIso
    (integralConstantForgetIso X)
  have ha : a.hom = Etale.supportedIntegralGenerator R i := by
    dsimp only [a, Functor.mapIso_hom, Etale.supportedIntegralGenerator]
    rw [integralConstantForgetIso_hom]
  have hgen : a.hom ≫ U.map j = Etale.supportedIntegralGenerator A i := by
    rw [ha]
    change (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
      (Etale.ordinaryFiniteIntegralGenerator R X) ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
          ((Etale.RawModuleScalarComparison.forget R X).map η) = _
    rw [← Functor.map_comp]
    erw [Etale.generator_scalar X φ η hη]
    rfl
  have hU : Function.Bijective (U.map (X := G)
      (Y := (Sheaf.restrictScalars Z.smallEtaleTopology φ).obj H)) :=
    ⟨U.map_injective, U.map_surjective⟩
  have hb := ((Iso.homCongr a.symm (Iso.refl _)).bijective.comp hU).comp hj
  have hstep (f : Q ⟶ H) :
      a.hom ≫ U.map (j ≫ (Sheaf.restrictScalars Z.smallEtaleTopology φ).map f) =
        Etale.supportedIntegralGenerator A i ≫
          (Etale.RawModuleScalarComparison.forget A Z).map f := by
    calc
      _ = a.hom ≫ (U.map j ≫ U.map
          ((Sheaf.restrictScalars Z.smallEtaleTopology φ).map f)) :=
        congrArg (fun k ↦ a.hom ≫ k) (U.map_comp _ _)
      _ = (a.hom ≫ U.map j) ≫ U.map
          ((Sheaf.restrictScalars Z.smallEtaleTopology φ).map f) :=
        (Category.assoc _ _ _).symm
      _ = Etale.supportedIntegralGenerator A i ≫ U.map
          ((Sheaf.restrictScalars Z.smallEtaleTopology φ).map f) :=
        congrArg (fun k ↦ k ≫ U.map
          ((Sheaf.restrictScalars Z.smallEtaleTopology φ).map f)) hgen
      _ = _ := rfl
  constructor
  · intro f g h
    apply hb.1
    change a.hom ≫ U.map (j ≫ (Sheaf.restrictScalars _ φ).map f) =
      a.hom ≫ U.map (j ≫ (Sheaf.restrictScalars _ φ).map g)
    exact (hstep f).trans (h.trans (hstep g).symm)
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    refine ⟨g, ?_⟩
    change a.hom ≫ U.map (j ≫ (Sheaf.restrictScalars _ φ).map g) = f at hg
    exact (hstep g).symm.trans hg

private theorem pro_supported_integral_universal (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i]
    (H : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f :
        (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A X) ⟶ H ↦
      cartierProIntegralGenerator A i ≫ (cartierForget A Z).map f) := by
  let Q := (Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
    (Etale.ordinaryFiniteConstant A X)
  let S := (Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
    (Etale.supportedIntegralConstant X)
  let am := comparisonAdjunction (ModuleCat.{u + 1} A) Z
  let aa := comparisonAdjunction AddCommGrpCat.{u + 1} Z
  let U := cartierForget A Z
  let V := Etale.RawModuleScalarComparison.forget A Z
  let s := cartierIntegralSourceIso i
  have : IsIso (geoCartierSourceComparison A i) := by
    have := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
    unfold geoCartierSourceComparison
    infer_instance
  let q := asIso (geoCartierSourceComparison A i)
  have hb := (Iso.homCongr q.symm (Iso.refl H)).bijective
  have hc := (am.homEquiv Q H).bijective.comp hb
  have hd := (etale_supported_integral_universal A i
    ((comparisonLowerStar (ModuleCat.{u + 1} A) Z).obj H)).comp hc
  have he := ((aa.homEquiv S (U.obj H)).symm.bijective).comp hd
  have hf := (Iso.homCongr s (Iso.refl (U.obj H))).bijective.comp he
  have hnatural (g : (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj Q ⟶ H) :
      (aa.homEquiv (V.obj Q) (U.obj H)).symm (V.map (am.homEquiv Q H g)) =
        cartierForgetComparison A Z Q ≫ U.map g := by
    rw [am.homEquiv_unit, V.map_comp]
    change (aa.homEquiv (V.obj Q) (U.obj H)).symm
      (V.map (am.unit.app Q) ≫
        (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map (U.map g)) = _
    exact aa.homEquiv_naturality_right_symm _ _
  convert! hf using 1
  funext f
  change cartierProIntegralGenerator A i ≫ U.map f =
    s.inv ≫ (aa.homEquiv S (U.obj H)).symm
      (Etale.supportedIntegralGenerator A i ≫ V.map
        (am.homEquiv Q H (q.hom ≫ f)))
  erw [aa.homEquiv_naturality_left_symm, hnatural]
  unfold cartierProIntegralGenerator
  simp only [Category.assoc, U.map_comp]
  rfl

/-- Scalar extension carries the supported integral constant to the supported
constant p-adic module, preserving the integral generator.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-system.proof.md, step (3), source
paragraph (blueprint: lem-sfb-supported-padic-scalar-extension).

Proof: Over the etale site the constant lifted integer module has the same
underlying abelian sheaf as the integral constant, and scalar forgetting from
lifted integers is fully faithful. The constant scalar unit from lifted integers
to the p-adic ring represents module maps out of the p-adic constant. The finite
ordinary scalar-unit theorem transports this Hom bijection through the closed
direct image. The etale/pro-etale comparison adjunctions and the supported-source
comparison isomorphisms give the same Hom bijection on the pro-etale site.
Naturality of both adjunctions identifies its unit with the specified supported
integral generator. This unit therefore has the same universal property as the
unit of diagonalScalarAdjunction. The unique comparison is an isomorphism and
preserves these units. No residue level or reduction presentation is involved;
on an empty scheme the Hom bijections are bijections of singleton sets. -/
theorem supported_padic_scalar_extension (ℓ : ℕ) [Fact ℓ.Prime]
    {X Z : Scheme.{u}} (i : X ⟶ Z) [IsClosedImmersion i] :
    ∃ e : (diagonalScalarExtension ℓ Z).obj
        ((lowerStar AddCommGrpCat.{u + 1} i).obj
          ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ])) i).obj
        (geoCartierConstant (ULift.{u + 1} ℤ_[ℓ]) X),
      HEq ((diagonalScalarAdjunction ℓ Z).unit.app _ ≫
        (diagonalForget ℓ Z).map e.hom)
        (cartierProIntegralGenerator (ULift.{u + 1} ℤ_[ℓ]) i) := by
  let A := ULift.{u + 1} ℤ_[ℓ]
  let S := (lowerStar AddCommGrpCat.{u + 1} i).obj
    ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
  let Q := (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A X)
  let adj := diagonalScalarAdjunction ℓ Z
  let e := (adj.homEquiv S Q).symm (cartierProIntegralGenerator A i)
  have he : adj.unit.app S ≫ (diagonalForget ℓ Z).map e =
      cartierProIntegralGenerator A i := (adj.homEquiv S Q).apply_symm_apply _
  have : IsIso e := by
    apply isIso_of_coyoneda_map_bijective
    intro H
    have hu := pro_supported_integral_universal A i H
    constructor
    · intro f g h
      apply hu.1
      change cartierProIntegralGenerator A i ≫ (diagonalForget ℓ Z).map f =
        cartierProIntegralGenerator A i ≫ (diagonalForget ℓ Z).map g
      have hf := congrArg (adj.homEquiv S H) h
      have hunit : adj.homEquiv S Q e = cartierProIntegralGenerator A i :=
        (adj.homEquiv S Q).apply_symm_apply _
      erw [adj.homEquiv_naturality_right, hunit,
        adj.homEquiv_naturality_right, hunit] at hf
      dsimp only [S] at hf
      exact hf
    · intro f
      obtain ⟨g, hg⟩ := hu.2 ((adj.homEquiv S H) f)
      refine ⟨g, (adj.homEquiv S H).injective ?_⟩
      change adj.unit.app S ≫ (diagonalForget ℓ Z).map (e ≫ g) = _
      rw [Functor.map_comp, ← Category.assoc, he]
      change cartierProIntegralGenerator A i ≫ (cartierForget A Z).map g = _
      exact hg
  exact ⟨asIso e, heq_of_eq he⟩

end AlgebraicGeometry.ProEtale
