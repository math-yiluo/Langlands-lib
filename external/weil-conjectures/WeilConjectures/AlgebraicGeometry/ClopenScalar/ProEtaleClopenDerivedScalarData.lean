/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenTotalTensorKFlatDetection
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm

/-! # Clopen derived scalar comparison and normalized compositor

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0D6D;
sites-modules.tex, Tag 05V4; the node's restriction/scalar square calculation.
(blueprint: def-pur-clopen-derived-scalar-comparison-data).

The helpers expose the recorded functors and package the normalized comparison laws.
The scalar-first sheaf tensor writes the paper's `p tensor s` as `s tensor p`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology

attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived

/-- The recorded module category; source: Stacks 03D7
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev Mods {Z : Scheme.{t}} (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}) :=
  SheafOfModules.SuccessiveDerivedQuotient.Modules.{t + 1, t, max u (t + 1)} R

/-- The inherited standard localization; source: Stacks 05RU
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
instance derived (Z : Scheme.{t}) :
    ∀ R : Sheaf (topology Z) CommRingCat.{max u (t + 1)},
      HasDerivedCategory.{max (u + 1) (t + 2)}
        (Mods.{t, u} R) :=
  fun R ↦ HasDerivedCategory.standard (Mods.{t, u} R)

/-- Families of presentations of the existing scalar extension, source: Stacks 06YY
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev Presentations (Z : Scheme.{t}) :=
  ∀ {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a

/-- The recorded restriction on the commutative coefficient sheaf; source: Stacks 04TR
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev rings {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  clopenTensorRings.{t, u} j

/-- The recorded restriction of module sheaves; source: Stacks 04TR
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev res {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    Mods.{t, u} R ⥤ Mods.{t, u} ((rings.{t, u} j).obj R) :=
  ClopenLocalization.restriction.{t, max u (t + 1), u, 0} j
    (derivedChangeRingIndependentCoefficients (topology X) R)

/-- Additivity of the recorded restriction. Source: Stacks 015F
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
instance resAdditive {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (res.{t, u} j R).Additive := clopenModuleRestriction_additive j _

/-- Exact restriction, using the existing localization interface. Source: Stacks 015F
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
instance resLimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteLimits (res.{t, u} j R) :=
  ClopenLocalization.restrictionLimits.{t, max u (t + 1), u, 0} j _

/-- Exact restriction, using the existing localization interface. Source: Stacks 015F
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
instance resColimits {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    PreservesFiniteColimits (res.{t, u} j R) :=
  ClopenLocalization.restrictionColimits.{t, max u (t + 1), u, 0} j _

/-- The recorded derived restriction; source: Stacks 05RU
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev resD {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    DerivedCategory (Mods.{t, u} R) ⥤ DerivedCategory (Mods.{t, u} ((rings.{t, u} j).obj R)) :=
  (res.{t, u} j R).mapDerivedCategory

/-- The canonical counit on cochain representatives, with the standard quotient comparisons.
Source: Stacks 06YY (blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def computation {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a)
    (P : CochainComplex (Mods.{t, u} R) ℤ) :
    p.derived.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) :=
  p.derived.map ((DerivedCategory.quotientCompQhIso (Mods.{t, u} R)).inv.app P) ≫
    p.counit.app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map ((p.ordinary.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso (Mods.{t, u} S)).hom.app
      ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P)

/-- Ordinary extension from the recorded presentation. Source: Stacks 06YY
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev ext {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a) : Mods.{t, u} R ⥤ Mods.{t, u} S :=
  p.ordinary

/-- Derived extension from the recorded universal pair. Source: Stacks 06YY
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
abbrev extD {Z : Scheme.{t}}
    {R S : Sheaf (topology Z) CommRingCat.{max u (t + 1)}} {a : R ⟶ S}
    (p : SheafOfModules.SuccessiveDerivedQuotient.Presentation.{t + 1, t,
      max u (t + 1), max (u + 1) (t + 2)} a) :
    DerivedCategory (Mods.{t, u} R) ⥤ DerivedCategory (Mods.{t, u} S) :=
  p.derived

attribute [local irreducible] computation
attribute [local irreducible] SheafOfModules.monoidalCategory HasDerivedCategory.standard

-- Bound elaboration while checking the representative normalization.
/-- Unit identifications normalized by multiplication on sections and by the canonical
K-flat computation counit. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
structure Units {Z : Scheme.{t}} (p : Presentations.{t, u} Z) where
  ordinary : ∀ R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}, (ext.{t, u} (Z := Z) (p (𝟙 R))) ≅
    𝟭 (Mods.{t, u} R)
  sections : ∀ (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    (M : Mods.{t, u} R) (U : Z.ProEtᵒᵖ) (x : M.val.obj U) (s : R.obj.obj U),
    ((ordinary R).hom.app M).val.app U (sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)}
      (C := Z.ProEt) (J := topology Z) (R := R) (S := R) (a := 𝟙 R) (p (𝟙 R)) M U s x) = s • x
  derived : ∀ R : Sheaf (topology Z) CommRingCat.{max u (t + 1)}, (extD.{t, u} (Z := Z) (p (𝟙 R))) ≅
    𝟭 (DerivedCategory (Mods.{t, u} R))
  representative : ∀ (R : Sheaf (topology Z) CommRingCat.{max u (t + 1)})
    (P : CochainComplex (Mods.{t, u} R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P →
    (∀ n : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology Z) (R := R) (P.X
      n)) →
    (derived R).hom.app (DerivedCategory.Q.obj P) =
      computation (Z := Z) (R := R) (S := R) (a := 𝟙 R) (p (𝟙 R)) P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (ordinary R) (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso (Mods.{t, u} R) (.up ℤ)).hom.app P)

-- Bound elaboration while checking the normalized comparison family.
/-- The scalar/restriction comparison and its full chain-level normalization. All morphisms
land in the component module category, so their linearity is part of their type.
Source: Stacks 06YY, 0D6D, 05V4
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
structure Comparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (p : Presentations.{t, u} X) (q : Presentations.{t, u} Y) where
  ordinary : ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    (ext.{t, u} (Z := X) (p a)) ⋙ res.{t, u} j S ≅ res.{t, u} j R ⋙ (ext.{t, u} (Z := Y) (q
      ((rings.{t, u} j).map a)))
  chain : ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    (ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ) ⋙
        (res.{t, u} j S).mapHomologicalComplex (.up ℤ) ≅
      (res.{t, u} j R).mapHomologicalComplex (.up ℤ) ⋙
        (ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map a))).mapHomologicalComplex (.up ℤ)
  derived : ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S),
    (extD.{t, u} (Z := X) (p a)) ⋙ resD.{t, u} j S ≅ resD.{t, u} j R ⋙ (extD.{t, u} (Z := Y) (q
      ((rings.{t, u} j).map a)))

/-- The sections law of the normalized scalar comparison. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def Comparison.sections {X Y : Scheme.{t}} {j : Y ⟶ X} [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (d : Comparison.{t, u} j @p @q) : Prop :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (M : Mods.{t, u} R) (U : Y.ProEtᵒᵖ)
    (s : ((rings.{t, u} j).obj S).obj.obj U) (x : ((res.{t, u} j R).obj M).val.obj U),
    ((d.ordinary a).hom.app M).val.app U (sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t +
      2)} (C := X.ProEt) (J := topology X) (R := R) (S := S) (a := a) (p a) M
      ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj U) s x) =
    sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := Y.ProEt) (J := topology Y) (R
      := (rings.{t, u} j).obj R) (S := (rings.{t, u} j).obj S) (a := (rings.{t, u} j).map a) (q
      ((rings.{t, u} j).map a)) ((res.{t, u} j R).obj M) U s x

/-- The degree law of the normalized scalar comparison. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def Comparison.degree {X Y : Scheme.{t}} {j : Y ⟶ X} [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (d : Comparison.{t, u} j @p @q) : Prop :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (P : CochainComplex (Mods.{t, u} R) ℤ) (n : ℤ),
    ((d.chain a).hom.app P).f n = (d.ordinary a).hom.app (P.X n)

/-- The representative law of the normalized scalar comparison. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def Comparison.representative {X Y : Scheme.{t}} {j : Y ⟶ X} [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (d : Comparison.{t, u} j @p @q) : Prop :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (P : CochainComplex (Mods.{t, u} R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P →
    (∀ n : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X) (R := R) (P.X
      n)) →
    (d.derived a).hom.app (DerivedCategory.Q.obj P) ≫
        (extD.{t, u} (Z := Y) (q ((rings.{t, u} j).map a))).map
          ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P) ≫
        computation (Z := Y) (R := (rings.{t, u} j).obj R)
          (S := (rings.{t, u} j).obj S) (a := (rings.{t, u} j).map a)
          (q ((rings.{t, u} j).map a))
          (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P) =
      (resD.{t, u} j S).map (computation (Z := X) (R := R) (S := S) (a := a) (p a) P) ≫
        (res.{t, u} j S).mapDerivedCategoryFactors.hom.app
          (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((d.chain a).hom.app P)

/-- The computed law of the normalized scalar comparison. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def Comparison.computed {X Y : Scheme.{t}} {j : Y ⟶ X} [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (_d : Comparison.{t, u} j @p @q) : Prop :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (P : CochainComplex (Mods.{t, u} R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P →
    (∀ n : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X) (R := R) (P.X
      n)) →
    IsIso (computation (Z := X) (R := R) (S := S) (a := a) (p a) P) ∧
      IsIso (computation (Z := Y) (R := (rings.{t, u} j).obj R)
          (S := (rings.{t, u} j).obj S) (a := (rings.{t, u} j).map a)
          (q ((rings.{t, u} j).map a))
        (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P))

/-- The unique law of the normalized scalar comparison. Source: Stacks 06YY, 0D6D
(blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
def Comparison.unique {X Y : Scheme.{t}} {j : Y ⟶ X} [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (d : Comparison.{t, u} j @p @q) : Prop :=
  ∀ {R S : Sheaf (topology X) CommRingCat.{max u (t + 1)}} (a : R ⟶ S)
    (e : (extD.{t, u} (Z := X) (p a)) ⋙ resD.{t, u} j S ⟶
      resD.{t, u} j R ⋙ (extD.{t, u} (Z := Y) (q ((rings.{t, u} j).map a)))),
    (∀ (P : CochainComplex (Mods.{t, u} R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, max u (t + 1)} (R := R) P →
      (∀ n : ℤ, IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)} (J := topology X) (R := R)
        (P.X n)) →
      e.app (DerivedCategory.Q.obj P) ≫
          (extD.{t, u} (Z := Y) (q ((rings.{t, u} j).map a))).map
            ((res.{t, u} j R).mapDerivedCategoryFactors.hom.app P) ≫
          computation (Z := Y) (R := (rings.{t, u} j).obj R)
          (S := (rings.{t, u} j).obj S) (a := (rings.{t, u} j).map a)
          (q ((rings.{t, u} j).map a))
            (((res.{t, u} j R).mapHomologicalComplex (.up ℤ)).obj P) =
        (resD.{t, u} j S).map (computation (Z := X) (R := R) (S := S) (a := a) (p a) P) ≫
          (res.{t, u} j S).mapDerivedCategoryFactors.hom.app
            (((ext.{t, u} (Z := X) (p a)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((d.chain a).hom.app P)) → e = (d.derived a).hom

-- Bound elaboration while checking the coherence diagrams.
/-- Coherence with the existing normalized scalar compositor and multiplication units.
Source: Stacks 0D6D (blueprint: def-pur-clopen-derived-scalar-comparison-data). -/
structure Coherence {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    {p : Presentations.{t, u} X} {q : Presentations.{t, u} Y}
    (n : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := X.ProEt) (J := topology
      X) (hD := derived.{t, u} X) @p)
    (m : Normalization.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := Y.ProEt) (J := topology
      Y) (hD := derived.{t, u} Y) @q) (U : Units.{t, u} (Z := X) @p) (V : Units.{t, u} (Z := Y) @q)
    (d : Comparison.{t, u} j @p @q) : Prop where
  composition : ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (K : DerivedCategory (Mods.{t, u} R)),
    (resD.{t, u} j T).map ((n.derived a b).hom.app K) ≫
        (d.derived (a ≫ b)).hom.app K =
      (d.derived b).hom.app ((extD.{t, u} (Z := X) (p a)).obj K) ≫
        (extD.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.derived a).hom.app K) ≫
        (m.derived ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app ((resD.{t, u} j R).obj
          K) ≫
        eqToHom (congrArg (fun f ↦ (extD.{t, u} (Z := Y) (q f)).obj ((resD.{t, u} j R).obj K))
          ((rings.{t, u} j).map_comp a b).symm)
  ordinary_composition : ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mods.{t, u} R),
    (res.{t, u} j T).map ((n.ordinary a b).hom.app M) ≫
        (d.ordinary (a ≫ b)).hom.app M =
      (d.ordinary b).hom.app ((ext.{t, u} (Z := X) (p a)).obj M) ≫
        (ext.{t, u} (Z := Y) (q ((rings.{t, u} j).map b))).map ((d.ordinary a).hom.app M) ≫
        (m.ordinary ((rings.{t, u} j).map a) ((rings.{t, u} j).map b)).hom.app ((res.{t, u} j R).obj
          M) ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_comp a b).symm)
  composite_sections : ∀ {R S T : Sheaf (topology X) CommRingCat.{max u (t + 1)}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Mods.{t, u} R) (W : Y.ProEtᵒᵖ)
    (x : ((res.{t, u} j R).obj M).val.obj W)
    (s : ((rings.{t, u} j).obj S).obj.obj W) (z : ((rings.{t, u} j).obj T).obj.obj W),
    (((res.{t, u} j T).map ((n.ordinary a b).hom.app M) ≫
        (d.ordinary (a ≫ b)).hom.app M).val.app W
      (sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := X.ProEt) (J := topology X)
        (R := S) (S := T) (a := b) (p b) ((ext.{t, u} (Z := X) (p a)).obj M)
        ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj W) z
        (sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := X.ProEt) (J := topology
          X) (R := R) (S := S) (a := a) (p a) M
          ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).op.obj W) s x))) =
      sectionTensor.{t + 1, t, max u (t + 1), max (u + 1) (t + 2)} (C := Y.ProEt) (J := topology Y)
        (R := (rings.{t, u} j).obj R) (S := (rings.{t, u} j).obj T) (a := (rings.{t, u} j).map (a ≫
        b)) (q ((rings.{t, u} j).map (a ≫ b))) ((res.{t, u} j R).obj M) W
        ((((rings.{t, u} j).map b).hom.app W).hom s * z) x
  identity : ∀ (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (K : DerivedCategory (Mods.{t, u} R)),
    (d.derived (𝟙 R)).hom.app K ≫
        eqToHom (congrArg (fun f ↦ (extD.{t, u} (Z := Y) (q f)).obj ((resD.{t, u} j R).obj K))
          ((rings.{t, u} j).map_id R)) ≫
        (V.derived ((rings.{t, u} j).obj R)).hom.app ((resD.{t, u} j R).obj K) =
      (resD.{t, u} j R).map ((U.derived R).hom.app K)
  ordinary_identity : ∀ (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) (M : Mods.{t, u} R),
    (d.ordinary (𝟙 R)).hom.app M ≫
        eqToHom (congrArg (fun f ↦ (ext.{t, u} (Z := Y) (q f)).obj ((res.{t, u} j R).obj M))
          ((rings.{t, u} j).map_id R)) ≫
        (V.ordinary ((rings.{t, u} j).obj R)).hom.app ((res.{t, u} j R).obj M) =
      (res.{t, u} j R).map ((U.ordinary R).hom.app M)

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
