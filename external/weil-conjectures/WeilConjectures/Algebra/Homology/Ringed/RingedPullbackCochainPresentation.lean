/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.Cochain.CochainUniversalCounitTransport
import WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement

/-! # A cochain presentation of independent-universe derived ringed pullback

This interface keeps the semilinear construction's instances private. In particular,
`import all` of an immediate consumer does not expose those implementation instances.
Source: Stacks Tag 06YY and the homotopy-to-cochain universal counit transport.
(blueprint: lem-pur-ringed-pullback-cochain-presentation)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe uC vC uD vD r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{r}} {S RI : Sheaf JD CommRingCat.{r}}

/-- The cochain counit for derived ringed pullback is universal and invertible on
flat-term K-flat representatives, with site and coefficient universes independent.

Source: Stacks Tag 06YY, via the independent-universe ringed derived pullback theorem,
and the universal cochain counit transport.
(blueprint: lem-pur-ringed-pullback-cochain-presentation)

Proof: apply the ringed derived pullback theorem to the specified algebraic inverse
image and scalar-extension presentation. Its universal homotopy counit is invertible
on the flat-term K-flat resolving class. Transport universality along the homotopy
quotient and its comparison with cochain localization. The componentwise transport
criterion preserves invertibility on precisely the same representatives. -/
theorem ringedPullbackCochainPresentation
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{r} ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    (hobj : ∀ M : SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
      (a : M ⟶ N), uStar.map a =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
          eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))] :
    ∃ (F : DerivedCategory (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
        DerivedCategory (SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S)))
      (ε : DerivedCategory.Q (C := SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⋙ F ⟶
        uStar.mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q (C := SheafOfModules.{r}
          ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj S))),
      F.IsRightKanExtension ε ∧
        ∀ P : CochainComplex (SheafOfModules.{r}
          ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ,
          P.IsKFlatIndependentCoefficients →
          (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
          IsIso (ε.app P) := by
  obtain ⟨F, ε, hF, _, _, hε, _⟩ :=
    ringedTopoiDerivedPullbackIndependent uInv uPush adj I c uStar hobj hmap
  let := hF
  let := Functor.IsLeftDerivedFunctor.isRightKanExtension F ε
    (HomotopyCategory.quasiIso
      (SheafOfModules.{r} ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ))
  obtain ⟨hkan, hiso⟩ := cochainUniversalCounitTransport uStar F ε
  refine ⟨F, derivedCochainCounit uStar F ε, hkan, ?_⟩
  intro P hp hf
  exact (hiso P).2 (hε P hp hf)

end SheafOfModules
