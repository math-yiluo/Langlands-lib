/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedImmersionComparisonNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedImmersionComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Open.OpenProjectionComparisonSquare
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The normalized immersion projection and site comparison

Source: Stacks Tags 0E8I, 0GL1, 09AF and 07A4; blueprint main-20261015,
finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-immersion-projection-site-comparison).

The closed arrow is the ordinary counit transpose. The open arrow is the inverse
unit transpose, with the signed symmetry putting the ambient factor first.
Exact termwise descent presents the closed comparison; its restriction to D+ is
identified with the specified derived counit mate by the normalization dependency.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u v₁ h₁ w₁

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

-- Prefer the direct monoidality proof over the indirect Grothendieck-abelian route.
attribute [local instance high] GrothendieckTopology.W.monoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.ImmersionProjectionComparison

namespace Etale

/-- The exact constant-coefficient inverse image.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
abbrev pull (A : Type (u + 1)) [CommRing A]
    {Y T : Scheme.{u}} (f : Y ⟶ T) :=
  (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- The canonical exact-pullback tensor comparison, transported from left derivation.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def tensorPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y T : Scheme.{u}} (f : Y ⟶ T)
    (D P : DerivedCategory (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))) :=
  (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    f).symm.app
      (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj D).obj P) ≪≫
    AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f D P ≪≫
    (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) Y).mapIso
      ((AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        f).app D)).app
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj P)) ≪≫
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((pull A f).obj D)).mapIso
        ((AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          f).app P)

/-- The exact closed direct image for the chosen factorization.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedPush (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory

/-- The ordinary restriction/direct-image adjunction localized termwise.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : pull A c ⊣ closedPush A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c)

/-- The exact functor Q = v_! c_*.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def extension (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :=
  closedPush A c v ⋙
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The closed projection arrow, defined by its specified ordinary counit transpose.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (S.smallEtaleTopology) (ModuleCat.{u + 1} A))) :=
  (closedAdjunction A c v).homEquiv _ _
    ((tensorPull A c D ((closedPush A c v).obj P)).hom ≫
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
        ((pull A c).obj D)).map ((closedAdjunction A c v).counit.app P))

/-- The signed symmetry of the native K-flat derived tensor.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def symmetry (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T ≅
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) T).flip :=
  letI := CategoryTheory.Sheaf.monoidalCategory
    (J := T.smallEtaleTopology) (A := ModuleCat.{u + 1} A)
  letI := CategoryTheory.Sheaf.braidedCategory
    (J := T.smallEtaleTopology) (A := ModuleCat.{u + 1} A)
  DerivedCategory.canonicalTensorSymmetry (Sheaf (T.smallEtaleTopology) (ModuleCat.{u + 1} A))

/-- The open projection isomorphism, inverse to the open-unit transpose.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def openProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} A))) :=
  ((symmetry A X).app D).app
      ((AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        v).mapDerivedCategory.obj P) ≪≫
    (((AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v).app P).app D).symm ≪≫
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.mapIso
      (((symmetry A V).app P).app
        ((AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj D) ≪≫
        ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V).mapIso
          ((AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v).app D)).app P)

/-- The canonical immersion projection: the open isomorphism followed by v_! of the closed map.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (S.smallEtaleTopology) (ModuleCat.{u + 1} A))) :=
  (openProjection A v D ((closedPush A c v).obj P)).hom ≫
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.map
      (closedProjection A c v ((pull A v).obj D) P)

end Etale

namespace ProEtale

/-- The exact constant-coefficient inverse image.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
abbrev pull (A : Type (u + 1)) [CommRing A]
    {Y T : Scheme.{u}} (f : Y ⟶ T) :=
  (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory

/-- The canonical exact-pullback tensor comparison, transported from left derivation.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def tensorPull (A : Type (u + 1)) [CommRing A] [Finite A]
    {Y T : Scheme.{u}} (f : Y ⟶ T)
    (D P : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    f).symm.app
      (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).obj D).obj P) ≪≫
    AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f D P ≪≫
    (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).mapIso
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        f).app D)).app
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj P))
          ≪≫
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((pull A f).obj D)).mapIso
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1}
          A) f).app P)

/-- The exact closed direct image for the chosen factorization.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedPush (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  (AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategory

/-- The ordinary restriction/direct-image adjunction localized termwise.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : pull A c ⊣ closedPush A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c)

/-- The exact functor Q = v_! c_*.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def extension (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :=
  closedPush A c v ⋙
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The closed projection arrow, defined by its specified ordinary counit transpose.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :=
  (closedAdjunction A c v).homEquiv _ _
    ((tensorPull A c D ((closedPush A c v).obj P)).hom ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).obj
        ((pull A c).obj D)).map ((closedAdjunction A c v).counit.app P))

/-- The signed symmetry of the native K-flat derived tensor.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def symmetry (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T ≅
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) T).flip :=
  letI := CategoryTheory.Sheaf.monoidalCategory
    (J := Scheme.ProEt.topology T) (A := ModuleCat.{u + 1} A)
  letI := CategoryTheory.Sheaf.braidedCategory
    (J := Scheme.ProEt.topology T) (A := ModuleCat.{u + 1} A)
  DerivedCategory.canonicalTensorSymmetry (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))

/-- The open projection isomorphism, inverse to the open-unit transpose.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def openProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :=
  ((symmetry A X).app D).app
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        v).mapDerivedCategory.obj P) ≪≫
    (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v).app P).app D).symm ≪≫
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.mapIso
      (((symmetry A V).app P).app
        ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj D) ≪≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).mapIso
          ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) v).app D)).app P)

/-- The canonical immersion projection: the open isomorphism followed by v_! of the closed map.
Source: Stacks Tags 0E8I, 0GL1 and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :=
  (openProjection A v D ((closedPush A c v).obj P)).hom ≫
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.map
      (closedProjection A c v ((pull A v).obj D) P)

end ProEtale

/-- Exact comparison pullback in the fixed constant-ring sheaf presentation.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
abbrev comparison (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory

/-- The canonical tensor comparison of exact site pullback.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def comparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (D P : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) D).app P

/-- The canonical comparison a_f, descended from the existing ordinary inverse-image square.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def pullComparison (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (f : S ⟶ X) :=
  Functor.mapDerivedCategorySquareIso
    (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) f).symm

/-- The composite a_s for s = c followed by v, in the factorized pullback presentation.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def immersionPullComparison (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X)
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (pullComparison A c).app ((Etale.pull A v).obj D) ≪≫
    (ProEtale.pull A c).mapIso ((pullComparison A v).app D)

/-- The closed counit-mate comparison, presented by exact termwise descent. On D+ this
is the specified fixedComparisonDirectImageMatePlus under the published normalization.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def closedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    Etale.closedPush A c v ⋙ comparison A V ≅
      comparison A S ⋙ ProEtale.closedPush A c v :=
  haveI : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  haveI : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  haveI := AlgebraicGeometry.ProEtale.derivedImmersionClosedEtale_exact A c
  haveI := AlgebraicGeometry.ProEtale.derivedImmersionClosedProEtale_exact A c
  letI := AlgebraicGeometry.ProEtale.isIso_lowerStarComparisonUpperStarBaseChange
    c (ModuleCat.{u + 1} A)
  Functor.mapDerivedCategorySquareIso
    (F₁ := AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c)
    (F₂ := AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) V)
    (G₁ := AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S)
    (G₂ := AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c)
    (asIso (AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange
      c (ModuleCat.{u + 1} A)))

/-- Delta is the canonical open comparison followed by v_! of the closed counit mate.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def extensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v).app
      ((Etale.closedPush A c v).obj P) ≪≫
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory.mapIso ((closedComparison A c v).app P)

/-- The degree-zero etale sheaf used in the comparison assertion.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
abbrev single (A : Type (u + 1)) [CommRing A] {S : Scheme.{u}}
    (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj P

/-- The stratum tensor s_e^*D tensor P, with the prescribed factorization.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
abbrev stratumTensor (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X)
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
    ((Etale.pull A c).obj ((Etale.pull A v).obj D))).obj (single A P)

/-- Invertibility and simultaneous naturality of the specified Etale projection arrow.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def etaleProjectionProperty (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : Prop :=
  (∀ (D : DerivedCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A)))
      (P : DerivedCategory (Sheaf (S.smallEtaleTopology) (ModuleCat.{u + 1} A))),
    IsIso (Etale.projection A c v D P)) ∧
  (∀ (D D' : DerivedCategory (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A)))
      (P P' : DerivedCategory (Sheaf (S.smallEtaleTopology) (ModuleCat.{u + 1} A)))
      (d : D ⟶ D') (p : P ⟶ P'),
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).map d).app
        ((Etale.extension A c v).obj P) ≫
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj D').map
        ((Etale.extension A c v).map p) ≫
      Etale.projection A c v D' P' =
    Etale.projection A c v D P ≫ (Etale.extension A c v).map
      (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).map
        ((Etale.pull A c).map ((Etale.pull A v).map d))).app P ≫
        ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((Etale.pull A c).obj ((Etale.pull A v).obj D'))).map p))

/-- Invertibility and simultaneous naturality of the specified ProEtale projection arrow.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def proetaleProjectionProperty (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : Prop :=
  (∀ (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (P : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))),
    IsIso (ProEtale.projection A c v D P)) ∧
  (∀ (D D' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (P P' : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
      (d : D ⟶ D') (p : P ⟶ P'),
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map d).app
        ((ProEtale.extension A c v).obj P) ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj D').map
        ((ProEtale.extension A c v).map p) ≫
      ProEtale.projection A c v D' P' =
    ProEtale.projection A c v D P ≫ (ProEtale.extension A c v).map
      (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
        ((ProEtale.pull A c).map ((ProEtale.pull A v).map d))).app P ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((ProEtale.pull A c).obj ((ProEtale.pull A v).obj D'))).map p))

/-- The target identification Q_p((a_s tensor 1) after t_S) in the displayed square.
Source: Stacks Tags 09AF, 099R and 07A4
(blueprint: lem-sf-immersion-projection-site-comparison). -/
def targetMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (ProEtale.extension A c v).map
    ((comparisonTensor A S ((Etale.pull A c).obj ((Etale.pull A v).obj D))
        (single A P)).hom ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
        (immersionPullComparison A c v D).hom).app ((comparison A S).obj (single A P)))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exactCounitIso
    {C D : Type v₁} [Category.{h₁} C] [Category.{h₁} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₁} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.counit] :
    IsIso (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit := by
  let ad := SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a
  let e : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso G F ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.counit) ≪≫
        Functor.mapDerivedCategoryIdIso D
  have hf := ad.fullyFaithfulROfCompIsoId e
  have := hf.full
  have := hf.faithful
  exact ad.counit_isIso_of_R_fully_faithful

private theorem supportedUnitIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms E] (F : C ⥤ D) (G : D ⥤ C) (R : C ⥤ E)
    (a : F ⊣ G) [IsIso a.counit]
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      IsIso (F.map f) → IsIso (R.map f) → IsIso f)
    (zero : ∀ P, IsZero (R.obj (G.obj P)))
    (X : C) (hX : IsZero (R.obj X)) : IsIso (a.unit.app X) := by
  apply detect
  · have : IsIso (F.map (a.unit.app X) ≫ a.counit.app (F.obj X)) := by
      rw [a.left_triangle_components X]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (a.counit.app _)
  · exact ⟨⟨0, hX.eq_of_src _ _, (zero _).eq_of_src _ _⟩⟩

private theorem projectionIso
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [IsIso a.counit]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td)
    (K : C) (P : D) [IsIso (a.unit.app ((tc.obj K).obj (G.obj P)))] :
    IsIso (a.homEquiv _ _
      (((e.app K).app (G.obj P)).hom ≫ (td.obj (F.obj K)).map (a.counit.app P))) := by
  rw [Adjunction.homEquiv_unit]
  infer_instance

private def tensorTransport
    {C D : Type*} [Category* C] [Category* D]
    (tC : C ⥤ C ⥤ C) (tD : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tC ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj tD) :
    (Functor.postcompose₂.obj F).obj tC ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj tD :=
  (Functor.postcompose₂.mapIso e.symm).app tC ≪≫ t ≪≫
    (((Functor.whiskeringLeft₂ D).mapIso e).app L).app tD ≪≫
    (((Functor.whiskeringLeft₂ D).obj F).mapIso e).app tD

private theorem tensorTransport_app
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) (K P : C) :
    (((tensorTransport tc td e t).app K).app P).hom =
      e.inv.app ((tc.obj K).obj P) ≫ ((t.app K).app P).hom ≫
        (td.map (e.hom.app K)).app (L.obj P) ≫ (td.obj (F.obj K)).map (e.hom.app P) := by
  rfl

private theorem tensorTransport_hom_app
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) (K P : C) :
    ((tensorTransport tc td e t).hom.app K).app P =
      e.inv.app ((tc.obj K).obj P) ≫ (t.hom.app K).app P ≫
        (td.map (e.hom.app K)).app (L.obj P) ≫ (td.obj (F.obj K)).map (e.hom.app P) := by
  rfl

private theorem tensorTransport_app_alt
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) (K P : C) :
    (((tensorTransport tc td e t).app K).app P).hom =
      e.inv.app ((tc.obj K).obj P) ≫ ((t.app K).app P).hom ≫
        (td.obj (L.obj K)).map (e.hom.app P) ≫ (td.map (e.hom.app K)).app (F.obj P) := by
  rw [tensorTransport_app]
  congr 2
  exact ((td.map (e.hom.app K)).naturality (e.hom.app P)).symm

private def tensorTransportSecond
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) :
    (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td :=
  (Functor.postcompose₂.mapIso e.symm).app tc ≪≫ t ≪≫
    (((Functor.whiskeringLeft₂ D).obj L).mapIso e).app td ≪≫
    (((Functor.whiskeringLeft₂ D).mapIso e).app F).app td

private theorem tensorTransportSecond_whisker
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) (K : C) :
    (tensorTransportSecond tc td e t).app K =
      Functor.isoWhiskerLeft (tc.obj K) e.symm ≪≫ t.app K ≪≫
        Functor.isoWhiskerRight e (td.obj (L.obj K)) ≪≫
        Functor.isoWhiskerLeft F (td.mapIso (e.app K)) := by
  rfl

private theorem tensorTransportSecond_eq
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) :
    tensorTransportSecond tc td e t = tensorTransport tc td e t := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply NatTrans.ext
  funext P
  change (((tensorTransportSecond tc td e t).app K).app P).hom =
    (((tensorTransport tc td e t).app K).app P).hom
  rw [tensorTransport_app_alt]
  rfl

private theorem tensorTransport_trans
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    {L F G : C ⥤ D} (e : L ≅ F) (f : F ≅ G)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td) :
    tensorTransport tc td f (tensorTransport tc td e t) =
      tensorTransport tc td (e ≪≫ f) t := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply NatTrans.ext
  funext P
  change f.inv.app ((tc.obj K).obj P) ≫
      (e.inv.app ((tc.obj K).obj P) ≫ ((t.app K).app P).hom ≫
        (td.map (e.hom.app K)).app (L.obj P) ≫ (td.obj (F.obj K)).map (e.hom.app P)) ≫
      (td.map (f.hom.app K)).app (F.obj P) ≫ (td.obj (G.obj K)).map (f.hom.app P) =
    (f.inv.app ((tc.obj K).obj P) ≫ e.inv.app ((tc.obj K).obj P)) ≫
      ((t.app K).app P).hom ≫
      (td.map (e.hom.app K ≫ f.hom.app K)).app (L.obj P) ≫
      (td.obj (G.obj K)).map (e.hom.app P ≫ f.hom.app P)
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [(td.map (f.hom.app K)).naturality_assoc]

private def compositeTensor
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E)
    (t : (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td)
    (s : (Functor.postcompose₂.obj G).obj td ≅
      (((Functor.whiskeringLeft₂ E).obj G).obj G).obj te) :
    (Functor.postcompose₂.obj (F ⋙ G)).obj tc ≅
      (((Functor.whiskeringLeft₂ E).obj (F ⋙ G)).obj (F ⋙ G)).obj te :=
  (Functor.postcompose₂.obj G).mapIso t ≪≫
    (((Functor.whiskeringLeft₂ E).obj F).obj F).mapIso s

private theorem compositeTensor_hom_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E)
    (t : (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td)
    (s : (Functor.postcompose₂.obj G).obj td ≅
      (((Functor.whiskeringLeft₂ E).obj G).obj G).obj te) (K P : C) :
    ((compositeTensor tc td te F G t s).hom.app K).app P =
      G.map ((t.hom.app K).app P) ≫ (s.hom.app (F.obj K)).app (F.obj P) := by
  rfl

private theorem tensorTransport_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E)
    {L F : C ⥤ D} {M G : D ⥤ E} (e : L ≅ F) (f : M ≅ G)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td)
    (s : (Functor.postcompose₂.obj M).obj td ≅
      (((Functor.whiskeringLeft₂ E).obj M).obj M).obj te) :
    compositeTensor tc td te F G (tensorTransport tc td e t) (tensorTransport td te f s) =
      tensorTransport tc te
        (Functor.isoWhiskerRight e M ≪≫ Functor.isoWhiskerLeft F f)
        (compositeTensor tc td te L M t s) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply NatTrans.ext
  funext P
  change G.map (e.inv.app ((tc.obj K).obj P) ≫ ((t.app K).app P).hom ≫
      (td.map (e.hom.app K)).app (L.obj P) ≫ (td.obj (F.obj K)).map (e.hom.app P)) ≫
      f.inv.app ((td.obj (F.obj K)).obj (F.obj P)) ≫
      ((s.app (F.obj K)).app (F.obj P)).hom ≫
      (te.map (f.hom.app (F.obj K))).app (M.obj (F.obj P)) ≫
      (te.obj (G.obj (F.obj K))).map (f.hom.app (F.obj P)) =
    (f.inv.app (F.obj ((tc.obj K).obj P)) ≫ M.map (e.inv.app ((tc.obj K).obj P))) ≫
      (M.map ((t.app K).app P).hom ≫ ((s.app (L.obj K)).app (L.obj P)).hom) ≫
      (te.map (M.map (e.hom.app K) ≫ f.hom.app (F.obj K))).app (M.obj (L.obj P)) ≫
      (te.obj (G.obj (F.obj K))).map (M.map (e.hom.app P) ≫ f.hom.app (F.obj P))
  rw [f.inv.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc, NatTrans.comp_app]
  have h₁ := (s.hom.app (F.obj K)).naturality (e.hom.app P)
  have h₂ := congr_app (s.hom.naturality (e.hom.app K)) (L.obj P)
  change M.map ((td.obj (F.obj K)).map (e.hom.app P)) ≫
      ((s.app (F.obj K)).app (F.obj P)).hom =
    ((s.app (F.obj K)).app (L.obj P)).hom ≫
      (te.obj (M.obj (F.obj K))).map (M.map (e.hom.app P)) at h₁
  change M.map ((td.map (e.hom.app K)).app (L.obj P)) ≫
      ((s.app (F.obj K)).app (L.obj P)).hom =
    ((s.app (L.obj K)).app (L.obj P)).hom ≫
      (te.map (M.map (e.hom.app K))).app (M.obj (L.obj P)) at h₂
  rw [reassoc_of% h₁, reassoc_of% h₂,
    (te.map (f.hom.app (F.obj K))).naturality_assoc]

private theorem tensorSquare_transport
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E) (tb : B ⥤ B ⥤ B)
    {L F : C ⥤ D} {M G : D ⥤ E} {N H : C ⥤ B} {O I : B ⥤ E}
    (e : L ≅ F) (f : M ≅ G) (g : N ≅ H) (k : O ≅ I)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td)
    (s : (Functor.postcompose₂.obj M).obj td ≅
      (((Functor.whiskeringLeft₂ E).obj M).obj M).obj te)
    (r : (Functor.postcompose₂.obj N).obj tc ≅
      (((Functor.whiskeringLeft₂ B).obj N).obj N).obj tb)
    (q : (Functor.postcompose₂.obj O).obj tb ≅
      (((Functor.whiskeringLeft₂ E).obj O).obj O).obj te)
    (a : N ⋙ O ≅ L ⋙ M)
    (h : compositeTensor tc td te L M t s =
      tensorTransport tc te a (compositeTensor tc tb te N O r q)) :
    compositeTensor tc td te F G (tensorTransport tc td e t) (tensorTransport td te f s) =
      tensorTransport tc te
        ((Functor.isoWhiskerRight g O ≪≫ Functor.isoWhiskerLeft H k).symm ≪≫ a ≪≫
          (Functor.isoWhiskerRight e M ≪≫ Functor.isoWhiskerLeft F f))
        (compositeTensor tc tb te H I (tensorTransport tc tb g r)
          (tensorTransport tb te k q)) := by
  rw [tensorTransport_comp, tensorTransport_comp, h, tensorTransport_trans,
    tensorTransport_trans]
  congr 1
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

private theorem tensorTransport_symmetry
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (bc : tc ≅ tc.flip) (bd : td ≅ td.flip)
    {L F : C ⥤ D} (e : L ≅ F)
    (t : (Functor.postcompose₂.obj L).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj L).obj L).obj td)
    (h : ∀ K P, L.map (((bc.app K).app P).hom) ≫ ((t.app P).app K).hom =
      ((t.app K).app P).hom ≫ ((bd.app (L.obj K)).app (L.obj P)).hom)
    (K P : C) :
    F.map (((bc.app K).app P).hom) ≫
        (((tensorTransport tc td e t).app P).app K).hom =
      (((tensorTransport tc td e t).app K).app P).hom ≫
        ((bd.app (F.obj K)).app (F.obj P)).hom := by
  rw [tensorTransport_app, tensorTransport_app]
  simp only [Category.assoc]
  have he := e.inv.naturality (((bc.app K).app P).hom)
  change F.map (((bc.app K).app P).hom) ≫ e.inv.app ((tc.obj P).obj K) =
    e.inv.app ((tc.obj K).obj P) ≫ L.map (((bc.app K).app P).hom) at he
  rw [reassoc_of% he]
  rw [reassoc_of% (h K P)]
  have hn := bd.hom.naturality (e.hom.app K)
  have hp := (bd.hom.app (F.obj K)).naturality (e.hom.app P)
  have hq := congr_app hn (L.obj P)
  change (td.map (e.hom.app K)).app (L.obj P) ≫
      ((bd.app (F.obj K)).app (L.obj P)).hom =
    ((bd.app (L.obj K)).app (L.obj P)).hom ≫
      (td.obj (L.obj P)).map (e.hom.app K) at hq
  change (td.obj (F.obj K)).map (e.hom.app P) ≫
      ((bd.app (F.obj K)).app (F.obj P)).hom =
    ((bd.app (F.obj K)).app (L.obj P)).hom ≫
      (td.map (e.hom.app P)).app (F.obj K) at hp
  have hr := (td.map (e.hom.app P)).naturality (e.hom.app K)
  rw [hp, reassoc_of% hq, hr]

attribute [local irreducible] tensorTransport tensorTransportSecond

section ExactTensor

variable {C D E B : Type*}
  [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution E]
  [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B] [BraidedCategory B]
  [Abelian.HasFunctorialFlatResolution B]
  (F₁ : C ⥤ D) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : D ⥤ E) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : C ⥤ B) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : B ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]

private def exactTensor :
    (Functor.postcompose₂.obj F₁.mapDerivedCategory).obj
        (MonoidalCategory.curriedTensor (DerivedCategory C)) ≅
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₁.mapDerivedCategory).obj (MonoidalCategory.curriedTensor (DerivedCategory D)) :=
  tensorTransport (MonoidalCategory.curriedTensor (DerivedCategory C))
    (MonoidalCategory.curriedTensor (DerivedCategory D))
    F₁.leftDerivedFunctorIsoMapDerivedCategory (asIso F₁.leftDerivedTensorComparison)

omit [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E]
  [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal] in
private theorem derivedSquare_normalization (a : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) :
    (Functor.isoWhiskerRight G₁.leftDerivedFunctorIsoMapDerivedCategory G₂.leftDerivedFunctor ≪≫
        Functor.isoWhiskerLeft G₁.mapDerivedCategory G₂.leftDerivedFunctorIsoMapDerivedCategory
      ).symm ≪≫ Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ a ≪≫
      (Functor.isoWhiskerRight F₁.leftDerivedFunctorIsoMapDerivedCategory F₂.leftDerivedFunctor ≪≫
        Functor.isoWhiskerLeft F₁.mapDerivedCategory F₂.leftDerivedFunctorIsoMapDerivedCategory) =
      Functor.mapDerivedCategorySquareIso a := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Functor.leftDerivedFunctorCompNatIso, Functor.leftDerivedFunctorCompIso,
    Functor.leftDerivedFunctorNatIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [G₂.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [F₂.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [G₂.mapDerivedCategory.map_id, F₂.leftDerivedFunctor.map_id,
    Category.id_comp, Category.id_comp, Iso.inv_hom_id_app]
  simpa only [Category.assoc, Functor.comp_obj] using Category.comp_id
    ((G₁.mapDerivedCategoryCompIso G₂).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso a).hom.app K ≫
        (F₁.mapDerivedCategoryCompIso F₂).inv.app K)

private theorem exactTensor_square (a : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    [NatTrans.IsMonoidal a.hom] :
    compositeTensor (MonoidalCategory.curriedTensor _) (MonoidalCategory.curriedTensor _)
      (MonoidalCategory.curriedTensor _) F₁.mapDerivedCategory F₂.mapDerivedCategory
      (exactTensor F₁) (exactTensor F₂) =
    tensorTransport (MonoidalCategory.curriedTensor _) (MonoidalCategory.curriedTensor _)
      (Functor.mapDerivedCategorySquareIso a)
      (compositeTensor (MonoidalCategory.curriedTensor _) (MonoidalCategory.curriedTensor _)
        (MonoidalCategory.curriedTensor _) G₁.mapDerivedCategory G₂.mapDerivedCategory
        (exactTensor G₁) (exactTensor G₂)) := by
  rw [← derivedSquare_normalization F₁ F₂ G₁ G₂ a]
  refine tensorSquare_transport (MonoidalCategory.curriedTensor _)
    (MonoidalCategory.curriedTensor _) (MonoidalCategory.curriedTensor _)
    (MonoidalCategory.curriedTensor _)
    F₁.leftDerivedFunctorIsoMapDerivedCategory F₂.leftDerivedFunctorIsoMapDerivedCategory
    G₁.leftDerivedFunctorIsoMapDerivedCategory G₂.leftDerivedFunctorIsoMapDerivedCategory
    (asIso F₁.leftDerivedTensorComparison) (asIso F₂.leftDerivedTensorComparison)
    (asIso G₁.leftDerivedTensorComparison) (asIso G₂.leftDerivedTensorComparison)
    (Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ a) ?_
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply NatTrans.ext
  funext M
  simp only [tensorTransport_hom_app]
  change F₂.leftDerivedFunctor.map ((F₁.leftDerivedTensorComparison.app K).app M) ≫
      (F₂.leftDerivedTensorComparison.app (F₁.leftDerivedFunctor.obj K)).app
        (F₁.leftDerivedFunctor.obj M) =
    (Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ a).inv.app
        (MonoidalCategory.tensorObj K M) ≫
      (G₂.leftDerivedFunctor.map ((G₁.leftDerivedTensorComparison.app K).app M) ≫
        (G₂.leftDerivedTensorComparison.app (G₁.leftDerivedFunctor.obj K)).app
          (G₁.leftDerivedFunctor.obj M)) ≫
      ((MonoidalCategory.curriedTensor (DerivedCategory E)).map
          ((Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ a).hom.app K)).app
            (G₂.leftDerivedFunctor.obj (G₁.leftDerivedFunctor.obj M)) ≫
      ((MonoidalCategory.curriedTensor (DerivedCategory E)).obj
        (F₂.leftDerivedFunctor.obj (F₁.leftDerivedFunctor.obj K))).map
          ((Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ a).hom.app M)
  have hh := Functor.map_leftDerivedTensorComparison_comp_eq_of_iso F₁ F₂ G₁ G₂ a K M
  rw [MonoidalCategory.tensorHom_def] at hh
  simpa only [Category.assoc, Functor.comp_obj,
      MonoidalCategory.curriedTensor_map_app,
      MonoidalCategory.curriedTensor_obj_map] using hh

private theorem exactTensor_compatible (a : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    [NatTrans.IsMonoidal a.hom] :
    Adjunction.ComparisonCompatible (Functor.mapDerivedCategorySquareIso a)
      (exactTensor F₁).hom (exactTensor G₂).hom
      (exactTensor F₂) (exactTensor G₁) := by
  intro K P
  have h := exactTensor_square F₁ F₂ G₁ G₂ a
  have hh := congr_app (congr_app (congrArg Iso.hom h) K) P
  simp only [tensorTransport_hom_app] at hh
  simpa only [compositeTensor_hom_app, Functor.comp_obj, Category.assoc] using hh

open MonoidalCategory in
private theorem exactTensor_braiding
    (hF : ∀ K P : C,
      F₁.map (@BraidedCategory.braiding C _ _ _ K P).hom ≫
          Functor.OplaxMonoidal.δ F₁ P K =
        Functor.OplaxMonoidal.δ F₁ K P ≫
          (@BraidedCategory.braiding D _ _ _ (F₁.obj K) (F₁.obj P)).hom)
    (K P : DerivedCategory C) :
    F₁.mapDerivedCategory.map
        (((DerivedCategory.canonicalTensorSymmetry C).app K).app P).hom ≫
        (((exactTensor F₁).app P).app K).hom =
      (((exactTensor F₁).app K).app P).hom ≫
        (((DerivedCategory.canonicalTensorSymmetry D).app
          (F₁.mapDerivedCategory.obj K)).app (F₁.mapDerivedCategory.obj P)).hom := by
  apply tensorTransport_symmetry
  intro M N
  let := DerivedCategory.braidedCategory' C
  let := DerivedCategory.braidedCategory' D
  have h := F₁.leftDerivedFunctor_map_braiding_hom_δ hF M N
  simp only [Functor.leftDerivedFunctorMonoidal_δ] at h
  exact h

end ExactTensor

private def etaleTensorPull
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : S ⟶ X) :
    (Functor.postcompose₂.obj (Etale.pull A f)).obj
        (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X) ≅
      (((Functor.whiskeringLeft₂ _).obj (Etale.pull A f)).obj (Etale.pull A f)).obj
        (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S) :=
  tensorTransport (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) f)
    (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) f)

private def proetaleTensorPull
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : S ⟶ X) :
    (Functor.postcompose₂.obj (ProEtale.pull A f)).obj
        (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) ≅
      (((Functor.whiskeringLeft₂ _).obj (ProEtale.pull A f)).obj (ProEtale.pull A f)).obj
        (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S) :=
  tensorTransport (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) f)
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) f)

private theorem etaleTensorPull_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : S ⟶ X)
    (D P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (((etaleTensorPull A f).app D).app P).hom = (Etale.tensorPull A f D P).hom := by
  unfold etaleTensorPull
  rw [tensorTransport_app]
  rfl

private theorem proetaleTensorPull_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : S ⟶ X)
    (D P : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (((proetaleTensorPull A f).app D).app P).hom = (ProEtale.tensorPull A f D P).hom := by
  unfold proetaleTensorPull
  rw [tensorTransport_app]
  rfl

private def comparisonTensorNat
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    (Functor.postcompose₂.obj (comparison A X)).obj
        (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X) ≅
      (((Functor.whiskeringLeft₂ _).obj (comparison A X)).obj (comparison A X)).obj
        (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) :=
  tensorTransportSecond
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory
    (asIso (AlgebraicGeometry.ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} A) X).leftDerivedTensorComparison)

private theorem comparisonTensorNat_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    comparisonTensorNat A X =
      exactTensor (AlgebraicGeometry.ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} A) X) := by
  apply tensorTransportSecond_eq

private theorem comparisonTensorNat_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (((comparisonTensorNat A X).app K).app P).hom = (comparisonTensor A X K P).hom := by
  unfold comparisonTensorNat
  rw [tensorTransportSecond_whisker]
  rfl

private theorem pullComparison_symm
    (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (f : S ⟶ X) :
    Functor.mapDerivedCategorySquareIso
      (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} A) f) = (pullComparison A f).symm := by
  apply Iso.ext
  simp only [pullComparison, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_symm
    (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) f).symm]
  rfl

private theorem etaleTensorPull_eq
  (A : Type (u + 1)) [CommRing A] [Finite A]
  {S X : Scheme.{u}} (f : S ⟶ X) : etaleTensorPull A f =
    exactTensor (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) f) := by
  unfold etaleTensorPull exactTensor
  congr 1
  apply Iso.ext
  exact (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso_hom
    (ModuleCat.{u + 1} A) f).trans
      (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
        (ModuleCat.{u + 1} A) f)

open AlgebraicGeometry.ProEtale in
private theorem proetaleTensorPull_eq
  (A : Type (u + 1)) [CommRing A] [Finite A]
  {S X : Scheme.{u}} (f : S ⟶ X) : proetaleTensorPull A f =
    exactTensor (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) f) := by
  unfold proetaleTensorPull exactTensor
  congr 1
  apply Iso.ext
  exact (AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso_hom
    (ModuleCat.{u + 1} A) f).trans
      (leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
        (ModuleCat.{u + 1} A) f)

attribute [local irreducible] exactTensor comparisonTensorNat

private theorem pullTensorCompatible
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : S ⟶ X) :
    Adjunction.ComparisonCompatible (pullComparison A f).symm
      (etaleTensorPull A f).hom (proetaleTensorPull A f).hom
      (comparisonTensorNat A S) (comparisonTensorNat A X) := by
  have h := exactTensor_compatible
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) f)
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S)
    (AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) f)
    (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) f)
  simpa only [← etaleTensorPull_eq, ← proetaleTensorPull_eq,
    ← comparisonTensorNat_eq, pullComparison_symm] using h

private theorem closedComparison_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    (mateEquiv (Etale.closedAdjunction A c v) (ProEtale.closedAdjunction A c v)
      (pullComparison A c).symm.hom) = (closedComparison A c v).hom := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  let e := AlgebraicGeometry.Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c
  let p := AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c
  let a := AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} A) c
  let d := AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange
    c (ModuleCat.{u + 1} A)
  have hd : (mateEquiv e p a.hom) = d := by
    apply NatTrans.ext
    funext P
    rw [AlgebraicGeometry.ProEtale.derivedImmersionClosed_sheaf_transpose A c P]
    simp [mateEquiv, Adjunction.homEquiv_unit, Functor.map_comp, e, p, a]
  have hb K := unit_mateEquiv e p a.hom K
  rw [show (mateEquiv e p a.hom) = TwoSquare.mk _ _ _ _ d from
    (by exact hd)] at hb
  have := AlgebraicGeometry.ProEtale.derivedImmersionClosedEtale_exact A c
  have := AlgebraicGeometry.ProEtale.derivedImmersionClosedProEtale_exact A c
  let := AlgebraicGeometry.ProEtale.isIso_lowerStarComparisonUpperStarBaseChange
    c (ModuleCat.{u + 1} A)
  have hm := CategoryTheory.exact_mate e p (asIso d) a (fun K ↦ (hb K).symm)
  have hs : (Functor.mapDerivedCategorySquareIso a).hom =
      (pullComparison A c).inv := congrArg Iso.hom (pullComparison_symm A c)
  rw [hs] at hm
  have he : (mateEquiv (Etale.closedAdjunction A c v) (ProEtale.closedAdjunction A c v)).symm
      (TwoSquare.mk _ _ _ _ (closedComparison A c v).hom) =
        TwoSquare.mk _ _ _ _ (pullComparison A c).inv := by exact hm
  exact ((Equiv.eq_symm_apply _).mp he.symm)

private theorem flipComparisonCompatible
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N : D ⥤ D'} {M : C ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M)
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (tc' : C' ⥤ C' ⥤ C') (td' : D' ⥤ D' ⥤ D')
    (e : (Functor.postcompose₂.obj F).obj td ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj tc)
    (e' : (Functor.postcompose₂.obj F').obj td' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj tc')
    (m : (Functor.postcompose₂.obj M).obj tc ≅
      (((Functor.whiskeringLeft₂ C').obj M).obj M).obj tc')
    (n : (Functor.postcompose₂.obj N).obj td ≅
      (((Functor.whiskeringLeft₂ D').obj N).obj N).obj td')
    (h : Adjunction.ComparisonCompatible a e e' m n) :
    Adjunction.ComparisonCompatible (T_C := tc.flip) (T_D := td.flip)
      (T_C' := tc'.flip) (T_D' := td'.flip) a
      ((flipFunctor _ _ _).map e) ((flipFunctor _ _ _).map e')
      ((flipFunctor _ _ _).mapIso m) ((flipFunctor _ _ _).mapIso n) := by
  intro K Q
  have hh := h Q K
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app] at hh ⊢
  rw [← (tc'.map (a.hom.app Q)).naturality] at hh
  exact hh

private theorem closedProjection_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A V).map (Etale.closedProjection A c v D P) ≫
        (closedComparison A c v).hom.app
          (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((Etale.pull A c).obj D)).obj P) ≫
        (ProEtale.closedPush A c v).map
          ((comparisonTensor A S ((Etale.pull A c).obj D) P).hom ≫
            ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
              ((pullComparison A c).hom.app D)).app ((comparison A S).obj P)) =
      (comparisonTensor A V D ((Etale.closedPush A c v).obj P)).hom ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj
          ((comparison A V).obj D)).map ((closedComparison A c v).hom.app P) ≫
        ProEtale.closedProjection A c v ((comparison A V).obj D) ((comparison A S).obj P) := by
  let tc := AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S
  let td := AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V
  let tp := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S
  let tq := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V
  have h := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
    (Etale.closedAdjunction A c v) (ProEtale.closedAdjunction A c v)
    (T_C := tc.flip) (T_D := td.flip) (T_C' := tp.flip) (T_D' := tq.flip)
    (φ := (flipFunctor _ _ _).map (etaleTensorPull A c).hom)
    (φ' := (flipFunctor _ _ _).map (proetaleTensorPull A c).hom)
    (m_C := (flipFunctor _ _ _).mapIso (comparisonTensorNat A S))
    (m_D := (flipFunctor _ _ _).mapIso (comparisonTensorNat A V))
    (α := (pullComparison A c).symm)
    (flipComparisonCompatible (pullComparison A c).symm tc td tp tq
      (etaleTensorPull A c).hom (proetaleTensorPull A c).hom
      (comparisonTensorNat A S) (comparisonTensorNat A V)
      (pullTensorCompatible A c)) P D
  have hm (K) := congr_app (closedComparison_mate A c v) K
  simp only [Iso.symm_hom] at hm
  simp only [Adjunction.rightAdjointProjectionMap_app_app,
    Functor.mapIso_hom, flipFunctor_map_app_app,
    Functor.flip_obj_map, Iso.symm_hom, Iso.symm_inv] at h
  simp only [hm] at h
  simp only [← Iso.app_hom, etaleTensorPull_app, proetaleTensorPull_app] at h
  change (comparison A V).map (Etale.closedProjection A c v D P) ≫
      (closedComparison A c v).hom.app _ ≫ (ProEtale.closedPush A c v).map
        ((((comparisonTensorNat A S).app ((Etale.pull A c).obj D)).app P).hom ≫
          (tp.map ((pullComparison A c).hom.app D)).app ((comparison A S).obj P)) =
    (((comparisonTensorNat A V).app D).app ((Etale.closedPush A c v).obj P)).hom ≫
      (tq.obj ((comparison A V).obj D)).map ((closedComparison A c v).hom.app P) ≫
      ProEtale.closedProjection A c v ((comparison A V).obj D) ((comparison A S).obj P) at h
  simpa only [comparisonTensorNat_app, tp, tq, Functor.id_obj] using h

private theorem adjoint_braiding
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [G.LaxBraided]
    (M N : C) :
    letI := a.leftAdjointOplaxMonoidal
    F.map (@BraidedCategory.braiding _ _ _ _ M N).hom ≫
        Functor.OplaxMonoidal.δ F N M =
      Functor.OplaxMonoidal.δ F M N ≫
        (@BraidedCategory.braiding _ _ _ _ (F.obj M) (F.obj N)).hom :=
  (a.leftAdjointOplaxMonoidal_δ_braiding M N).symm

-- Keep specialization of the two sheaf tensor structures explicit.
private theorem comparisonTensor_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map (((Etale.symmetry A X).app K).app P).hom ≫
        (comparisonTensor A X P K).hom =
      (comparisonTensor A X K P).hom ≫
        (((ProEtale.symmetry A X).app ((comparison A X).obj K)).app
          ((comparison A X).obj P)).hom := by
  let F := AlgebraicGeometry.ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  have hb (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      F.map (@BraidedCategory.braiding _ _ _ _ M N).hom ≫
          Functor.OplaxMonoidal.δ F N M =
        Functor.OplaxMonoidal.δ F M N ≫
          (@BraidedCategory.braiding _ _ _ _ (F.obj M) (F.obj N)).hom := by
    let G := AlgebraicGeometry.ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X
    let : G.LaxBraided := {
      toLaxMonoidal := ProEtale.laxMonoidal_comparisonLowerStar
        (ModuleCat.{u + 1} A) X
      braided := by
        intro M N
        exact Functor.LaxBraided.braided
          (F := (Scheme.toProEt X).sheafPushforwardContinuous
            (ModuleCat.{u + 1} A) X.smallEtaleTopology (Scheme.ProEt.topology X)) M N }
    have h := @adjoint_braiding
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      inferInstance inferInstance
      (Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf.monoidalCategory (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (Sheaf.braidedCategory X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf.braidedCategory (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      F G (AlgebraicGeometry.ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X)
      inferInstance M N
    simpa only [AlgebraicGeometry.ProEtale.oplaxMonoidal_comparisonUpperStar] using h
  have h := exactTensor_braiding F hb K P
  rw [← comparisonTensorNat_eq A X] at h
  change (comparison A X).map (((Etale.symmetry A X).app K).app P).hom ≫
      (((comparisonTensorNat A X).app P).app K).hom =
    (((comparisonTensorNat A X).app K).app P).hom ≫
      (((ProEtale.symmetry A X).app ((comparison A X).obj K)).app ((comparison A X).obj P)).hom at h
  simpa only [comparisonTensorNat_app] using h

private def leftDerivedPullComparison
    (A : Type (u + 1)) [CommRing A]
    {V X : Scheme.{u}} (v : V ⟶ X) :=
  Functor.isoWhiskerRight
      (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) v) (comparison A V) ≪≫
    pullComparison A v ≪≫
    Functor.isoWhiskerLeft (comparison A X)
      (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) v).symm

private theorem inverse_square
    {C : Type*} [Category* C] {X Y Z T : C}
    (e : X ≅ Y) (f : Z ≅ T) (a : X ⟶ Z) (b : Y ⟶ T)
    (h : e.hom ≫ b = a ≫ f.hom) : e.inv ≫ a = b ≫ f.inv := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ (e.inv ≫ a) = a := by rw [Iso.hom_inv_id_assoc]
    _ = (a ≫ f.hom) ≫ f.inv := by simp only [Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
    _ = (e.hom ≫ b) ≫ f.inv := by rw [h]
    _ = e.hom ≫ (b ≫ f.inv) := Category.assoc _ _ _

private def oppositeEtaleOpen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v
        ).mapDerivedCategory.obj P)).obj D ≅
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v
      ).mapDerivedCategory.obj
      (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V).obj P).obj
        ((Etale.pull A v).obj D)) :=
  (((AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} A) v).app P).app D).symm ≪≫
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.mapIso
      (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V).obj P).mapIso
        ((AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) v).app D))

private def oppositeProetaleOpen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)))
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v
        ).mapDerivedCategory.obj P)).obj D ≅
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v
      ).mapDerivedCategory.obj
      (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj P).obj
        ((ProEtale.pull A v).obj D)) :=
  (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} A) v).app P).app D).symm ≪≫
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory.mapIso
      (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj P).mapIso
        ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) v).app D))

private theorem oppositeOpen_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map (oppositeEtaleOpen A v P D).hom ≫
        (AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v).hom.app _ ≫
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
          ((comparisonTensor A V P ((Etale.pull A v).obj D)).hom ≫
            ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj
              ((comparison A V).obj P)).map ((pullComparison A v).hom.app D)) =
      (comparisonTensor A X
        ((AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
          v).mapDerivedCategory.obj P) D).hom ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
          ((AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v).hom.app P)).app
            ((comparison A X).obj D) ≫
        (oppositeProetaleOpen A v ((comparison A V).obj P) ((comparison A X).obj D)).hom := by
  let E := (AlgebraicGeometry.Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let F := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let o := AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v
  let te := AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V
  let tp := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V
  let L := (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor
  let Lp := (AlgebraicGeometry.ProEtale.upperStar
    (ModuleCat.{u + 1} A) v).leftDerivedFunctor
  let qe : E.obj ((te.obj P).obj (L.obj D)) ≅
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (E.obj P)).obj D :=
    ((AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v).app P).app D
  let qp : F.obj ((tp.obj ((comparison A V).obj P)).obj
      (Lp.obj ((comparison A X).obj D))) ≅
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        (F.obj ((comparison A V).obj P))).obj ((comparison A X).obj D) :=
    ((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v).app ((comparison A V).obj P)).app ((comparison A X).obj D)
  let ee := AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v
  let ep := AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v
  have h := AlgebraicGeometry.ProEtale.openProjectionTransport_projection_square A v P D
  have hp : (Functor.mapDerivedCategorySquareIso
      (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} A) v)).symm = pullComparison A v := by
    rw [pullComparison_symm, Iso.symm_symm_eq]
  change _ ≫ _ = _ ≫ _ at h
  change _ ≫ _ = (_ ≪≫ F.mapIso (_ ≪≫
    (tp.obj ((comparison A V).obj P)).mapIso
      ((Functor.isoWhiskerRight ee (comparison A V) ≪≫
        (Functor.mapDerivedCategorySquareIso
          (AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} A) v)).symm ≪≫
        Functor.isoWhiskerLeft (comparison A X) ep.symm).app D))).hom ≫ _ at h
  rw [hp] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at h
  change (comparison A X).map qe.hom ≫
      ((comparisonTensor A X (E.obj P) D).hom ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
          (o.hom.app P)).app ((comparison A X).obj D)) =
    o.hom.app ((te.obj P).obj (L.obj D)) ≫
      F.map ((comparisonTensor A V P (L.obj D)).hom) ≫
      F.map ((tp.obj ((comparison A V).obj P)).map
        ((leftDerivedPullComparison A v).hom.app D)) ≫ qp.hom at h
  rw [← F.map_comp_assoc] at h
  have hh := inverse_square ((comparison A X).mapIso qe) qp
    (o.hom.app ((te.obj P).obj (L.obj D)) ≫
      F.map ((comparisonTensor A V P (L.obj D)).hom ≫
        (tp.obj ((comparison A V).obj P)).map
          ((leftDerivedPullComparison A v).hom.app D)))
    ((comparisonTensor A X (E.obj P) D).hom ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
        (o.hom.app P)).app ((comparison A X).obj D))
    (by simpa only [Functor.mapIso_hom, Category.assoc] using h)
  dsimp only [oppositeEtaleOpen, oppositeProetaleOpen, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  have honat {K L} (f : K ⟶ L) :
      (comparison A X).map (E.map f) ≫ o.hom.app L =
        o.hom.app K ≫ F.map ((comparison A V).map f) := by
    exact o.hom.naturality f
  rw [reassoc_of% honat]
  change (comparison A X).map qe.inv ≫ o.hom.app _ ≫
      F.map ((comparison A V).map ((te.obj P).map (ee.hom.app D))) ≫ _ = _
  rw [← F.map_comp_assoc]
  have ht := (comparisonTensorNat A V).hom.app P |>.naturality (ee.hom.app D)
  change (comparison A V).map ((te.obj P).map (ee.hom.app D)) ≫
      (((comparisonTensorNat A V).app P).app ((Etale.pull A v).obj D)).hom =
    (((comparisonTensorNat A V).app P).app (L.obj D)).hom ≫
      (tp.obj ((comparison A V).obj P)).map ((comparison A V).map (ee.hom.app D)) at ht
  simp only [comparisonTensorNat_app] at ht
  rw [ht]
  rw [← F.map_comp]
  simp only [Category.assoc]
  have ha : (comparison A V).map (ee.hom.app D) ≫ (pullComparison A v).hom.app D =
      (leftDerivedPullComparison A v).hom.app D ≫ ep.hom.app ((comparison A X).obj D) := by
    change _ = ((comparison A V).map (ee.hom.app D) ≫
      (pullComparison A v).hom.app D ≫ ep.inv.app ((comparison A X).obj D)) ≫
        ep.hom.app ((comparison A X).obj D)
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (fun k ↦ (comparison A V).map (ee.hom.app D) ≫ k)
      (Category.comp_id ((pullComparison A v).hom.app D)).symm
  rw [← (tp.obj ((comparison A V).obj P)).map_comp, ha,
    (tp.obj ((comparison A V).obj P)).map_comp]
  simp only [F.map_comp]
  rw [← F.map_comp_assoc]
  simp only [Functor.mapIso_inv, Category.assoc] at hh
  rw [reassoc_of% hh]
  rfl

private theorem symmetry_naturality
    {C : Type*} [Category* C] (t : C ⥤ C ⥤ C) (b : t ≅ t.flip)
    (P : C) {K L : C} (e : K ⟶ L) :
    (((b.app P).app K).hom ≫ (t.map e).app P) =
      (t.obj P).map e ≫ ((b.app P).app L).hom := by
  exact ((b.hom.app P).naturality e).symm

private theorem etaleOpenProjection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Etale.openProjection A v D P).hom =
      (((Etale.symmetry A X).app D).app
          ((AlgebraicGeometry.Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj P)).hom ≫
        (oppositeEtaleOpen A v P D).hom ≫
        (AlgebraicGeometry.Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
            (((Etale.symmetry A V).app P).app ((Etale.pull A v).obj D)).hom := by
  simp only [Etale.openProjection, oppositeEtaleOpen, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  exact congrArg
    (fun k ↦ (((Etale.symmetry A X).app D).app
      ((AlgebraicGeometry.Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj P)).hom ≫
      (((AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) v).app P).app D).inv ≫
      (AlgebraicGeometry.Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.map k)
    (symmetry_naturality
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V)
      (Etale.symmetry A V) P
      ((AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) v).hom.app D))

private theorem proetaleOpenProjection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :
    (ProEtale.openProjection A v D P).hom =
      (((ProEtale.symmetry A X).app D).app
          ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
            (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj P)).hom ≫
        (oppositeProetaleOpen A v P D).hom ≫
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
            (((ProEtale.symmetry A V).app P).app ((ProEtale.pull A v).obj D)).hom := by
  simp only [ProEtale.openProjection, oppositeProetaleOpen, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp]
  exact congrArg
    (fun k ↦ (((ProEtale.symmetry A X).app D).app
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj P)).hom ≫
      (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
        (ModuleCat.{u + 1} A) v).app P).app D).inv ≫
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.map k)
    (symmetry_naturality
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V)
      (ProEtale.symmetry A V) P
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) v).hom.app D))

private theorem openProjection_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map (Etale.openProjection A v D P).hom ≫
        (AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v).hom.app _ ≫
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
          ((comparisonTensor A V ((Etale.pull A v).obj D) P).hom ≫
            ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).map
              ((pullComparison A v).hom.app D)).app ((comparison A V).obj P)) =
      (comparisonTensor A X D
        ((AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
          v).mapDerivedCategory.obj P)).hom ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((comparison A X).obj D)).map
          ((AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v).hom.app P) ≫
        (ProEtale.openProjection A v ((comparison A X).obj D) ((comparison A V).obj P)).hom := by
  let E := (AlgebraicGeometry.Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let F := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let o := AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v
  let tp := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V
  let tx := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X
  let CP := (comparison A V).obj P
  let CD := (comparison A X).obj D
  let LD := (Etale.pull A v).obj D
  let LDp := (ProEtale.pull A v).obj CD
  have hi := comparisonTensor_symmetry A V P LD
  have hop := oppositeOpen_square A v P D
  simp only [Functor.map_comp] at hop
  have hβ := ((ProEtale.symmetry A V).hom.app CP).naturality
    ((pullComparison A v).hom.app D)
  change (tp.obj CP).map ((pullComparison A v).hom.app D) ≫
      (((ProEtale.symmetry A V).app CP).app LDp).hom =
    (((ProEtale.symmetry A V).app CP).app ((comparison A V).obj LD)).hom ≫
      (tp.map ((pullComparison A v).hom.app D)).app CP at hβ
  rw [etaleOpenProjection_eq, proetaleOpenProjection_eq]
  simp only [Functor.map_comp, Category.assoc]
  have honat {K L} (f : K ⟶ L) :
      (comparison A X).map (E.map f) ≫ o.hom.app L =
        o.hom.app K ≫ F.map ((comparison A V).map f) := by
    exact o.hom.naturality f
  erw [reassoc_of% (honat
    ((((Etale.symmetry A V).app P).app LD).hom)),
    ← F.map_comp_assoc, ← F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hi, ← hβ]
  simp only [Functor.map_comp]
  rw [reassoc_of% hop,
    reassoc_of% (comparisonTensor_symmetry A X D (E.obj P))]
  have ho := ((ProEtale.symmetry A X).hom.app CD).naturality (o.hom.app P)
  change (tx.obj CD).map (o.hom.app P) ≫
      (((ProEtale.symmetry A X).app CD).app (F.obj CP)).hom =
    (((ProEtale.symmetry A X).app CD).app ((comparison A X).obj (E.obj P))).hom ≫
      (tx.map (o.hom.app P)).app CD at ho
  rw [← reassoc_of% ho]

private theorem etaleClosedIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso (Etale.closedProjection A c v D P) := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  let U : V.Opens :=
    ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let r := AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) U.ι
  let f := AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) c
  let g := AlgebraicGeometry.Etale.lowerStar (ModuleCat.{u + 1} A) c
  have : IsIso (Etale.closedAdjunction A c v).counit :=
    exactCounitIso (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) c)
  have hd : JointlyReflectIsomorphisms (pairFunctor f r) := by
    apply jointlyReflectIsomorphisms_pairFunctor
    intro M N k hf hr
    exact AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map
      (ModuleCat.{u + 1} A) U.ι c (by simp [U]) k hr hf
  have hdet := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory f r hd
  have hz (N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
      IsZero (r.mapDerivedCategory.obj (g.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    have h0 := AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range
      (ModuleCat.{u + 1} A) U.ι c (by
        rw [Scheme.Opens.range_ι]
        exact Set.disjoint_left.mpr (fun _ hx hy ↦ hx hy))
      ((DerivedCategory.homologyFunctor _ n).obj N)
    exact h0.of_iso
      (r.mapIso ((g.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  have hu : IsIso ((Etale.closedAdjunction A c v).unit.app
      (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V).obj D).obj
        ((Etale.closedPush A c v).obj P))) := by
    apply supportedUnitIso (Etale.pull A c) (Etale.closedPush A c v)
      r.mapDerivedCategory (Etale.closedAdjunction A c v)
      (fun k hf hr ↦ hdet.isIso_of_pairFunctor k hf hr) hz
    exact (AlgebraicGeometry.Etale.isZero_derivedTensor_obj_obj_of_isZero_right
      (A := ModuleCat.{u + 1} A) _ (hz P)).of_iso
        (Etale.tensorPull A U.ι D ((Etale.closedPush A c v).obj P))
  have h := projectionIso (Etale.closedAdjunction A c v)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
    (etaleTensorPull A c) D P
  simpa only [etaleTensorPull_app, Etale.closedProjection, Functor.id_obj] using h

private theorem proetaleClosedIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
    IsIso (ProEtale.closedProjection A c v D P) := by
  have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
  have : CompactSpace V :=
    ⟨v.isOpenEmbedding.isInducing.isCompact_iff.2
      (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  let U : V.Opens :=
    ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let r := AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) U.ι
  let f := AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} A) c
  let g := AlgebraicGeometry.ProEtale.lowerStar (ModuleCat.{u + 1} A) c
  have hcompl : IsCompl (Set.range c.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have : IsIso (ProEtale.closedAdjunction A c v).counit :=
    exactCounitIso (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) c)
  have hd : JointlyReflectIsomorphisms (pairFunctor f r) := by
    apply jointlyReflectIsomorphisms_pairFunctor
    intro M N k hf hr
    exact AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_of_isCompl c U.ι hcompl k
  have hdet := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory f r hd
  have hz (N : DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :
      IsZero (r.mapDerivedCategory.obj (g.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    have h0 := AlgebraicGeometry.ProEtale.isZero_upperStar_lowerStar_of_disjoint
      (ModuleCat.{u + 1} A) c U.ι hcompl.disjoint
      ((DerivedCategory.homologyFunctor _ n).obj N)
    exact h0.of_iso
      (r.mapIso ((g.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  have hu : IsIso ((ProEtale.closedAdjunction A c v).unit.app
      (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V).obj D).obj
        ((ProEtale.closedPush A c v).obj P))) := by
    apply supportedUnitIso (ProEtale.pull A c) (ProEtale.closedPush A c v)
      r.mapDerivedCategory (ProEtale.closedAdjunction A c v)
      (fun k hf hr ↦ hdet.isIso_of_pairFunctor k hf hr) hz
    have h0 : IsZero
        (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) U.toScheme).obj
          (r.mapDerivedCategory.obj D)).obj
            (r.mapDerivedCategory.obj ((ProEtale.closedPush A c v).obj P))) := by
      simpa only [AlgebraicGeometry.ProEtale.derivedTensor,
        MonoidalCategory.curriedTensor_obj_obj, ProEtale.closedPush, g] using
        MonoidalCategory.isZero_tensorObj_of_isZero_right (r.mapDerivedCategory.obj D) (hz P)
    exact h0.of_iso (ProEtale.tensorPull A U.ι D ((ProEtale.closedPush A c v).obj P))
  have h := projectionIso (ProEtale.closedAdjunction A c v)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
    (proetaleTensorPull A c) D P
  simpa only [proetaleTensorPull_app, ProEtale.closedProjection, Functor.id_obj] using h

private def closedProjectionNat
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td) :=
  (flipFunctor _ _ _).map
    (a.rightAdjointProjectionMap (T_C := td.flip) (T_D := tc.flip)
      ((flipFunctor _ _ _).map e.hom))

private theorem closedProjectionNat_app
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (e : (Functor.postcompose₂.obj F).obj tc ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj td) (K : C) (P : D) :
    ((closedProjectionNat a tc td e).app K).app P =
      a.homEquiv _ _
        ((((e.app K).app (G.obj P)).hom) ≫
          (td.obj (F.obj K)).map (a.counit.app P)) := by
  rfl

private def openProjectionNat
    {C D : Type*} [Category* C] [Category* D]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D)
    (bC : tc ≅ tc.flip) (bD : td ≅ td.flip)
    (E : D ⥤ C) {L F : C ⥤ D} (e : L ≅ F)
    (o : (Functor.postcompose₂.obj E).obj
        ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj L).obj td) ≅
      E ⋙ tc) :=
  ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj E).mapIso bC) ≪≫
    (flipFunctor _ _ _).mapIso o.symm ≪≫
    (Functor.postcompose₂.obj E).mapIso
      ((flipFunctor _ _ _).mapIso
          ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj L).mapIso bD) ≪≫
        (((Functor.whiskeringLeft₂ D).mapIso e).app (𝟭 D)).app td)

private def etaleOpenProjectionNat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v] :
    (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
      (AlgebraicGeometry.Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory).obj
          (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X) ≅
    (Functor.postcompose₂.obj (AlgebraicGeometry.Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory).obj
      ((((Functor.whiskeringLeft₂ _).obj (Etale.pull A v)).obj (𝟭 _)).obj
        (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V)) :=
  openProjectionNat
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V)
    (Etale.symmetry A X) (Etale.symmetry A V)
    (AlgebraicGeometry.Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory
    (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) v)
    (AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v)

private def proetaleOpenProjectionNat
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v] :
    (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory).obj
          (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X) ≅
    (Functor.postcompose₂.obj (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v).mapDerivedCategory).obj
      ((((Functor.whiskeringLeft₂ _).obj (ProEtale.pull A v)).obj (𝟭 _)).obj
        (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V)) :=
  openProjectionNat
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
    (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V)
    (ProEtale.symmetry A X) (ProEtale.symmetry A V)
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
      v).mapDerivedCategory
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) v)
    (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) v)

private theorem etaleOpenProjectionNat_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (((etaleOpenProjectionNat A v).app D).app P).hom =
      (Etale.openProjection A v D P).hom := by
  rfl

private theorem proetaleOpenProjectionNat_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (v : V ⟶ X) [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :
    (((proetaleOpenProjectionNat A v).app D).app P).hom =
      (ProEtale.openProjection A v D P).hom := by
  rfl

private def composedProjectionNat
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E)
    (p : C ⥤ D) (r : D ⥤ E) (q : E ⥤ D) (f : D ⥤ C)
    (o : (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj f).obj tc ⟶
      (Functor.postcompose₂.obj f).obj
        ((((Functor.whiskeringLeft₂ D).obj p).obj (𝟭 D)).obj td))
    (k : (((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj q).obj td ⟶
      (Functor.postcompose₂.obj q).obj
        ((((Functor.whiskeringLeft₂ E).obj r).obj (𝟭 E)).obj te)) :=
  ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj q).map o) ≫
    (Functor.postcompose₂.obj f).map
      ((((Functor.whiskeringLeft₂ D).obj p).obj (𝟭 E)).map k)

private theorem composedProjectionNat_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (tc : C ⥤ C ⥤ C) (td : D ⥤ D ⥤ D) (te : E ⥤ E ⥤ E)
    (p : C ⥤ D) (r : D ⥤ E) (q : E ⥤ D) (f : D ⥤ C)
    (o : (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj f).obj tc ⟶
      (Functor.postcompose₂.obj f).obj
        ((((Functor.whiskeringLeft₂ D).obj p).obj (𝟭 D)).obj td))
    (k : (((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj q).obj td ⟶
      (Functor.postcompose₂.obj q).obj
        ((((Functor.whiskeringLeft₂ E).obj r).obj (𝟭 E)).obj te)) (K : C) (P : E) :
    ((composedProjectionNat tc td te p r q f o k).app K).app P =
      (o.app K).app (q.obj P) ≫ f.map ((k.app (p.obj K)).app P) := by
  rfl

private theorem bifunctorNaturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C ⥤ D ⥤ E} (a : F ⟶ G)
    {K K' : C} {P P' : D} (d : K ⟶ K') (p : P ⟶ P') :
    (F.map d).app P ≫ (F.obj K').map p ≫ (a.app K').app P' =
      (a.app K).app P ≫ (G.map d).app P ≫ (G.obj K').map p := by
  rw [(a.app K').naturality p, ← Category.assoc, a.naturality_app, Category.assoc]

attribute [local irreducible] Etale.projection ProEtale.projection

private theorem etaleProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : etaleProjectionProperty A c v := by
  constructor
  · intro D P
    have := etaleClosedIso A c v ((Etale.pull A v).obj D) P
    unfold Etale.projection
    change IsIso ((Etale.openProjection A v D ((Etale.closedPush A c v).obj P)).hom ≫
      (AlgebraicGeometry.Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
          (Etale.closedProjection A c v ((Etale.pull A v).obj D) P))
    infer_instance
  · intro D D' P P' d p
    let n := composedProjectionNat
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X)
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) V)
      (AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S)
      (Etale.pull A v) (Etale.pull A c) (Etale.closedPush A c v)
      (AlgebraicGeometry.Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory
      (etaleOpenProjectionNat A v).hom
      (closedProjectionNat (Etale.closedAdjunction A c v) _ _ (etaleTensorPull A c))
    have hn (K Q) : (n.app K).app Q = Etale.projection A c v K Q := by
      rw [composedProjectionNat_app]
      simp only [← Iso.app_hom, etaleOpenProjectionNat_app,
        closedProjectionNat_app, etaleTensorPull_app]
      unfold Etale.projection
      rfl
    have h := bifunctorNaturality n d p
    simp only [hn] at h
    change ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).map d).app
        ((Etale.extension A c v).obj P) ≫
      ((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj D').map
        ((Etale.extension A c v).map p) ≫ Etale.projection A c v D' P' =
      Etale.projection A c v D P ≫ (Etale.extension A c v).map
        (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((Etale.pull A c).map ((Etale.pull A v).map d))).app P) ≫
        (Etale.extension A c v).map
          (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((Etale.pull A c).obj ((Etale.pull A v).obj D'))).map p) at h
    simpa only [Functor.map_comp, Category.assoc] using h

private theorem proetaleProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] : proetaleProjectionProperty A c v := by
  constructor
  · intro D P
    have := proetaleClosedIso A c v ((ProEtale.pull A v).obj D) P
    unfold ProEtale.projection
    change IsIso ((ProEtale.openProjection A v D ((ProEtale.closedPush A c v).obj P)).hom ≫
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
          (ProEtale.closedProjection A c v ((ProEtale.pull A v).obj D) P))
    infer_instance
  · intro D D' P P' d p
    let n := composedProjectionNat
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X)
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V)
      (AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S)
      (ProEtale.pull A v) (ProEtale.pull A c) (ProEtale.closedPush A c v)
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} A) v).mapDerivedCategory
      (proetaleOpenProjectionNat A v).hom
      (closedProjectionNat (ProEtale.closedAdjunction A c v) _ _ (proetaleTensorPull A c))
    have hn (K Q) : (n.app K).app Q = ProEtale.projection A c v K Q := by
      rw [composedProjectionNat_app]
      simp only [← Iso.app_hom, proetaleOpenProjectionNat_app,
        closedProjectionNat_app, proetaleTensorPull_app]
      unfold ProEtale.projection
      rfl
    have h := bifunctorNaturality n d p
    simp only [hn] at h
    change ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map d).app
        ((ProEtale.extension A c v).obj P) ≫
      ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj D').map
        ((ProEtale.extension A c v).map p) ≫ ProEtale.projection A c v D' P' =
      ProEtale.projection A c v D P ≫ (ProEtale.extension A c v).map
        (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
          ((ProEtale.pull A c).map ((ProEtale.pull A v).map d))).app P) ≫
        (ProEtale.extension A c v).map
          (((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((ProEtale.pull A c).obj ((ProEtale.pull A v).obj D'))).map p) at h
    simpa only [Functor.map_comp, Category.assoc] using h

private theorem projection_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map (Etale.projection A c v D P) ≫
        (extensionComparison A c v
          (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
            ((Etale.pull A c).obj ((Etale.pull A v).obj D))).obj P)).hom ≫
        (ProEtale.extension A c v).map
          ((comparisonTensor A S ((Etale.pull A c).obj ((Etale.pull A v).obj D)) P).hom ≫
            ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S).map
              (immersionPullComparison A c v D).hom).app ((comparison A S).obj P)) =
      (comparisonTensor A X D ((Etale.extension A c v).obj P)).hom ≫
        ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((comparison A X).obj D)).map (extensionComparison A c v P).hom ≫
        ProEtale.projection A c v ((comparison A X).obj D) ((comparison A S).obj P) := by
  let E := (AlgebraicGeometry.Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let F := (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) v).mapDerivedCategory
  let G := ProEtale.closedPush A c v
  let o := AlgebraicGeometry.ProEtale.derivedImmersionOpenExtensionComparison A v
  let δ := closedComparison A c v
  let tv := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) V
  let ts := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) S
  let tx := AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X
  let LD := (Etale.pull A v).obj D
  let CD := (comparison A X).obj D
  let CP := (comparison A S).obj P
  let Q := (Etale.closedPush A c v).obj P
  let a := (pullComparison A v).hom.app D
  let b := (comparisonTensor A S ((Etale.pull A c).obj LD) P).hom ≫
    (ts.map ((pullComparison A c).hom.app LD)).app CP
  let H := (((AlgebraicGeometry.Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj
    ((Etale.pull A c).obj LD)).obj P)
  let bt := (comparisonTensor A S ((Etale.pull A c).obj LD) P).hom ≫
    (ts.map (immersionPullComparison A c v D).hom).app CP
  let n := (ts.map ((ProEtale.pull A c).map a)).app CP
  have ht : bt = b ≫ n := by
    simp only [bt, b, n, immersionPullComparison, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rfl
  have hc := closedProjection_square A c v LD P
  change (comparison A V).map (Etale.closedProjection A c v LD P) ≫
      δ.hom.app H ≫ G.map b =
    (comparisonTensor A V LD Q).hom ≫
      (tv.obj ((comparison A V).obj LD)).map (δ.hom.app P) ≫
      ProEtale.closedProjection A c v ((comparison A V).obj LD) CP at hc
  have ho := openProjection_square A v D Q
  simp only [Functor.map_comp] at ho
  let k := closedProjectionNat (ProEtale.closedAdjunction A c v)
    tv ts (proetaleTensorPull A c)
  have hk := congr_app (k.naturality a) CP
  simp only [NatTrans.comp_app] at hk
  change (tv.map a).app (G.obj CP) ≫ (k.app _).app CP =
    (k.app _).app CP ≫ G.map n at hk
  dsimp only [k] at hk
  simp only [closedProjectionNat_app, proetaleTensorPull_app] at hk
  change (tv.map a).app (G.obj CP) ≫
      ProEtale.closedProjection A c v ((ProEtale.pull A v).obj CD) CP =
    ProEtale.closedProjection A c v ((comparison A V).obj LD) CP ≫
      G.map n at hk
  have hm : (comparison A V).map (Etale.closedProjection A c v LD P) ≫
      δ.hom.app H ≫ G.map bt =
    (comparisonTensor A V LD Q).hom ≫ (tv.map a).app ((comparison A V).obj Q) ≫
      (tv.obj ((ProEtale.pull A v).obj CD)).map (δ.hom.app P) ≫
      ProEtale.closedProjection A c v ((ProEtale.pull A v).obj CD) CP := by
    rw [ht, G.map_comp]
    rw [reassoc_of% hc, ← hk]
    have hn : (tv.obj ((comparison A V).obj LD)).map (δ.hom.app P) ≫
        (tv.map a).app (G.obj CP) =
      (tv.map a).app ((comparison A V).obj Q) ≫
        (tv.obj ((ProEtale.pull A v).obj CD)).map (δ.hom.app P) :=
      (tv.map a).naturality (δ.hom.app P)
    rw [reassoc_of% hn]
  have hn := ((proetaleOpenProjectionNat A v).hom.app CD).naturality (δ.hom.app P)
  change (tx.obj CD).map (F.map (δ.hom.app P)) ≫
      (ProEtale.openProjection A v CD (G.obj CP)).hom =
    (ProEtale.openProjection A v CD ((comparison A V).obj Q)).hom ≫
      F.map ((tv.obj ((ProEtale.pull A v).obj CD)).map (δ.hom.app P)) at hn
  unfold Etale.projection ProEtale.projection
  change (comparison A X).map
      ((Etale.openProjection A v D Q).hom ≫ E.map (Etale.closedProjection A c v LD P)) ≫
        (o.hom.app ((Etale.closedPush A c v).obj H) ≫ F.map (δ.hom.app H)) ≫
        F.map (G.map bt) =
    (comparisonTensor A X D (E.obj Q)).hom ≫
      (tx.obj CD).map (o.hom.app Q ≫ F.map (δ.hom.app P)) ≫
      (ProEtale.openProjection A v CD (G.obj CP)).hom ≫
        F.map (ProEtale.closedProjection A c v ((ProEtale.pull A v).obj CD) CP)
  rw [(comparison A X).map_comp]
  simp only [Category.assoc]
  have honat {K L} (f : K ⟶ L) :
      (comparison A X).map (E.map f) ≫ o.hom.app L =
        o.hom.app K ≫ F.map ((comparison A V).map f) := by
    exact o.hom.naturality f
  rw [reassoc_of% (honat (Etale.closedProjection A c v LD P))]
  rw [← F.map_comp_assoc, ← F.map_comp]
  simp only [Category.assoc]
  rw [hm]
  rw [F.map_comp, F.map_comp]
  rw [reassoc_of% ho]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]

private theorem flatTensorLowerBound
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P : C) (hP : ObjectProperty.flat P) (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    ((MonoidalCategory.curriedTensor (DerivedCategory C)).obj K).obj
      ((DerivedCategory.singleFunctor C 0).obj P) |>.IsGE n := by
  have hh : (((MonoidalCategory.curriedTensor (DerivedCategory C)).obj
      ((DerivedCategory.singleFunctor C 0).obj P)).obj K).IsGE (0 + n) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeIn
      (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hP) K n
  have h := DerivedCategory.TStructure.t.isGE_of_iso
    (((DerivedCategory.canonicalTensorSymmetry C).app
      ((DerivedCategory.singleFunctor C 0).obj P)).app K) (0 + n)
  simpa only [zero_add, Functor.flip_obj_obj] using h

private theorem stratumTensor_bounded
    (A : Type (u + 1)) [CommRing A]
    {S V X : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ X)
    (D : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hP : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Module.Flat A (((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} A)).obj P)) :
    ∃ n : ℤ, (stratumTensor A c v D.obj P).IsGE n := by
  have hp : ObjectProperty.flat P := by
    apply GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj
      (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale S (ModuleCat.{u + 1} A))
    rintro ⟨-, ⟨x⟩⟩
    exact (ModuleCat.flat_iff_flat _).2 (hP _ (S.algClosurePoint x))
  obtain ⟨n, hn⟩ := D.property
  have : D.obj.IsGE n := hn
  have := (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) v
    ).isGE_mapDerivedCategory_obj D.obj n
  have := (AlgebraicGeometry.Etale.upperStar (ModuleCat.{u + 1} A) c
    ).isGE_mapDerivedCategory_obj ((Etale.pull A v).obj D.obj) n
  refine ⟨n, ?_⟩
  exact flatTensorLowerBound P hp
    ((Etale.pull A c).obj ((Etale.pull A v).obj D.obj)) n

/-- The normalized immersion projection is natural and invertible on both unbounded
categories and respects site comparison in the stated bounded-below flat-sheaf case.
Source: Stacks Tags 0E8I, 0GL1, 09AF and 07A4; blueprint main-20261015,
finite-duality site-comparison proof, second paragraph
(blueprint: lem-sf-immersion-projection-site-comparison).

Proof:
1. Exact termwise descent preserves the closed adjunction and its invertible counit.
Noetherianity supplies the required exactness on the intermediate open subscheme.
2. Closed restriction and restriction to the complementary open jointly detect
isomorphisms. The tensor of an ambient complex with a closed direct image vanishes
on that open. The closed restriction of its adjunction unit is invertible by the
triangle identity; its open restriction is a map between zero objects. Hence the
unit is invertible, and so is the specified closed projection transpose.
3. Compose the published unbounded open projection with the open direct image of
this closed projection. Package the maps as bifunctor transformations to prove
simultaneous naturality in both inputs.
4. Flat geometric stalks imply a flat sheaf. Its degree-zero single complex has
Tor amplitude [0,0]. Exact pullback preserves a lower bound for D; the native
Tor-amplitude tensor bound and signed symmetry preserve it for the stratum tensor.
5. Transport the native left-derived tensor comparisons through the exact-functor
normalizations. Naturality makes this transport compatible with composition and
symmetry. The ordinary monoidal pullback square therefore yields compatibility
of the exact tensor maps with the specified pullComparison.
6. The ordinary closed base-change map is the mate of the pullback square.
Exact mate normalization and the categorical projection-mate identity give the
closed projection square for the precise closedComparison in the statement.
7. Invert the published open projection comparison square, move restriction
normalizations by naturality, and conjugate by the signed tensor symmetries.
8. Expand projection and extensionComparison into their open and closed factors.
Naturality moves the closed projection through the open comparison. Insert the
closed square, move the pullback comparison through the closed projection, and
insert the open square. Naturality in its stratum input moves the closed comparison
through the open projection. Tensor functoriality identifies the resulting target
with targetMap. Combine this equality with steps 3 and 4.
-/
theorem immersion_projection_site_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V X : Scheme.{u}} [IsNoetherian X] (c : S ⟶ V) (v : V ⟶ X)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    etaleProjectionProperty A c v ∧ proetaleProjectionProperty A c v ∧
    (∀ (D : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Module.Flat A (((Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} A)).obj P)) →
      (∃ n : ℤ, (stratumTensor A c v D.obj P).IsGE n) ∧
      (comparison A X).map (Etale.projection A c v D.obj (single A P)) ≫
          (extensionComparison A c v (stratumTensor A c v D.obj P)).hom ≫
          targetMap A c v D.obj P =
        (comparisonTensor A X D.obj ((Etale.extension A c v).obj (single A P))).hom ≫
          ((AlgebraicGeometry.ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((comparison A X).obj D.obj)).map
              (extensionComparison A c v (single A P)).hom ≫
          ProEtale.projection A c v ((comparison A X).obj D.obj)
            ((comparison A S).obj (single A P))) := by
  refine ⟨etaleProjection A c v, proetaleProjection A c v, ?_⟩
  intro D P hP
  exact ⟨stratumTensor_bounded A c v D P hP,
    projection_comparison A c v D.obj (single A P)⟩

end AlgebraicGeometry.ImmersionProjectionComparison
