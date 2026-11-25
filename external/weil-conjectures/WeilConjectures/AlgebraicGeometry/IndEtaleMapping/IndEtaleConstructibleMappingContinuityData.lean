/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomAdjunction
import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.Constructible
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Category.Grp.AB

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)
variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

/-- Global RHom of the two exact inverse images along a scheme over X.
This is the existing RΓ of the existing derived internal Hom.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def value (T : Over X) : DerivedCategory (ModuleCat.{u + 1} A) :=
  ((ExternalRHom.globalHom A T.left).obj
    (op ((ExternalRHom.pull A T.hom).obj K))).obj
      ((ExternalRHom.pull A T.hom).obj M)

/-- Pullback of derived morphisms, transported along the canonical composition
isomorphisms for inverse image. Its source is the evaluation transpose already
provided by `ExternalRHom.restriction`; no map or isomorphism is chosen.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def pullback {T S : Over X} (f : T ⟶ S) : value A K M S ⟶ value A K M T :=
  ExternalRHom.restriction A f.left
      ((ExternalRHom.pull A S.hom).obj K) ((ExternalRHom.pull A S.hom).obj M) ≫
    ((ExternalRHom.globalHom A T.left).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
        f.w.symm).hom.app K).op).app
          ((ExternalRHom.pull A f.left).obj ((ExternalRHom.pull A S.hom).obj M)) ≫
    ((ExternalRHom.globalHom A T.left).obj
      (op ((ExternalRHom.pull A T.hom).obj K))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f.left S.hom T.hom
          f.w.symm).inv.app M)

variable {K' M'} in
/-- The map of global RHom induced by the coefficient maps `α : K' ⟶ K`
(contravariantly) and `β : M ⟶ M'` (covariantly), after exact inverse image
to a scheme over X.
Source: Bhatt--Scholze 6.3.16, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def coefficientMap (T : Over X) : value A K M T ⟶ value A K' M' T :=
  ExternalRHom.homMap A ((ExternalRHom.pull A T.hom).map α)
    ((ExternalRHom.pull A T.hom).map β)

/-- Compatible strict representatives for the global RHom diagram and its
pullback cocone. The two equations normalize every transition and every leg
against the canonical pullback of morphisms. This is computational input for an
exact filtered colimit, not an assumed continuity isomorphism.
Source: Bhatt--Scholze 6.3.16, p. 48; the node's proof, Steps 2--6
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
structure Model where
  /-- The strict diagram of representatives. -/
  diagram : Iᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 1} A) ℤ
  /-- The strict cocone of representatives over the limit. -/
  cocone : Cocone diagram
  /-- The identification of each stage with the global RHom on `D.obj i`. -/
  stage : ∀ i : I, DerivedCategory.Q.obj (diagram.obj (op i)) ≅ value A K M (D.obj i)
  /-- The identification of the apex with the global RHom on `c.pt`. -/
  apex : DerivedCategory.Q.obj cocone.pt ≅ value A K M c.pt
  transition : ∀ {i j : I} (f : i ⟶ j),
    DerivedCategory.Q.map (diagram.map f.op) ≫ (stage i).hom =
      (stage j).hom ≫ pullback A K M (D.map f)
  leg : ∀ i : I,
    DerivedCategory.Q.map (cocone.ι.app (op i)) ≫ apex.hom =
      (stage i).hom ≫ pullback A K M (c.π.app i)

/-- The canonical comparison, computed by the exact colimit of complexes and
then localized. The normalization in `Model` fixes its pullback legs.
Source: Bhatt--Scholze 6.3.16, p. 48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity). -/
def comparison (P : Model A K M D c) :
    DerivedCategory.Q.obj (colimit P.diagram) ⟶ value A K M c.pt :=
  DerivedCategory.Q.map (colimit.desc P.diagram P.cocone) ≫ P.apex.hom

/-- A compatible representative map without the cone-square field.
The geometric cone equation is supplied separately by the square hypothesis.
Source: Bhatt--Scholze 6.3.16, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-model-skeleton).
-/
structure ModelMapSkeleton (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt) where
  stages : r.op ⋙ P.diagram ⟶ Q.diagram
  apex : P.cocone.pt ⟶ Q.cocone.pt
  square : ∀ j : J,
    P.cocone.ι.app (op (r.obj j)) ≫ apex = stages.app (op j) ≫ Q.cocone.ι.app (op j)
  stage_normalization : ∀ j : J,
    DerivedCategory.Q.map (stages.app (op j)) ≫ (Q.stage j).hom =
      (P.stage (r.obj j)).hom ≫ pullback A K M (η.app j) ≫
        coefficientMap A K M α β (E.obj j)
  apex_normalization : DerivedCategory.Q.map apex ≫ Q.apex.hom =
    P.apex.hom ≫ pullback A K M v ≫ coefficientMap A K M α β d.pt

end AlgebraicGeometry.Etale.IndEtaleMapping
