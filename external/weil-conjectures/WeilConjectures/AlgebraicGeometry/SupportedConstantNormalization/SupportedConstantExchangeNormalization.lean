/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
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
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.Support.SupportQuotientPairPullback
import all WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedConstantPresentation
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedSectionsHom
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-!
# Canonically normalized closed constant exchange

Source: Stacks Project, Tags 03S6 and 095L; Milne, Lectures on Etale Cohomology,
Section 9, Theorem 9.4 (blueprint: lem-pur-supported-constant-exchange-normalization).
The Boolean parameter only selects the etale (`false`) or pro-etale (`true`) site.
All sheaves are ordinary fixed-scalar modules over the given constant ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SupportedConstantNormalization

/-- The existing small site, selected without changing either universe.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev Site (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- The category structure of the selected existing site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
@[reducible] instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

/-- The selected existing topology.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X

/-- Ordinary module sheaves on the selected site, with the usual larger coefficients.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev Modules (A : Type (u + 1)) [CommRing A] (pro : Bool) (X : Scheme.{u}) :=
  Sheaf (topology pro X) (ModuleCat.{u + 1} A)

namespace ConstantProof
section
universe v₁ v₂ u₁ u₂ w

variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {D : Type w} [Category D]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  [HasWeakSheafify J₁ D] [HasWeakSheafify J₂ D]

section Monoidal
open MonoidalCategory
variable [MonoidalCategory D] [BraidedCategory D]
  [(J₁.W (A := D)).IsMonoidal] [(J₂.W (A := D)).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory

private lemma constantDirect_unit_monoidal (F : C₁ ⥤ C₂) [F.IsContinuous J₁ J₂] :
    Functor.LaxMonoidal.ε (F.sheafPushforwardContinuous D J₁ J₂) =
      Scheme.constantDirect J₁ J₂ F (𝟙_ D) := by
  apply ((sheafificationAdjunction J₁ D).homEquiv _ _).injective
  unfold Scheme.constantDirect
  conv_rhs => erw [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  have he1 : Functor.LaxMonoidal.ε (sheafToPresheaf J₁ D) =
      toSheafify J₁ ((Functor.const C₁ᵒᵖ).obj (𝟙_ D)) := by
    change (sheafificationAdjunction J₁ D).homEquiv _ _ (𝟙 _) = _
    rw [Adjunction.homEquiv_unit, (sheafToPresheaf J₁ D).map_id]
    exact Category.comp_id _
  have he2 : Functor.LaxMonoidal.ε (sheafToPresheaf J₂ D) =
      toSheafify J₂ ((Functor.const C₂ᵒᵖ).obj (𝟙_ D)) := by
    change (sheafificationAdjunction J₂ D).homEquiv _ _ (𝟙 _) = _
    rw [Adjunction.homEquiv_unit, (sheafToPresheaf J₂ D).map_id]
    exact Category.comp_id _
  apply NatTrans.ext
  funext W
  have he := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app F D J₁ J₂ W
  rw [he1, he2] at he
  exact he
end Monoidal

end
end ConstantProof

variable (A : Type (u + 1)) [CommRing A]

/-- Sheafification on either existing small site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
instance sheafify (pro : Bool) (X : Scheme.{u}) :
    HasSheafify (topology pro X) (ModuleCat.{u + 1} A) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

/-- The already defined constant sheaf of the coefficient module.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev constant (pro : Bool) (X : Scheme.{u}) : Modules A pro X :=
  (constantSheaf (topology pro X) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- Inverse image along an arbitrary scheme morphism.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev pull (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules A pro Y ⥤ Modules A pro X :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} A) f
  | true => ProEtale.upperStar (ModuleCat.{u + 1} A) f

/-- Direct image along an arbitrary scheme morphism.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev push (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules A pro X ⥤ Modules A pro Y :=
  match pro with
  | false => Etale.lowerStar (ModuleCat.{u + 1} A) f
  | true => ProEtale.lowerStar (ModuleCat.{u + 1} A) f

/-- The actual inverse-image adjunction, on either site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def adj (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull A pro f ⊣ push A pro f :=
  match pro with
  | false => Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  | true => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f

/-- The existing scalar-preserving constant identification on either site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def unitIso (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull A pro f).obj (constant A pro Y) ≅ constant A pro X :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
      (ModuleCat.of A A)
  | true => (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).app
      (ModuleCat.of A A)

/-- The supported constant is the recorded closed direct image.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev supported (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (push A pro i).obj (constant A pro Z)

/-- Reuse constant restriction; the pro-etale arrow is the sheafified scalar map.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def restriction (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X) :
    constant A pro X ⟶ supported A pro i :=
  match pro with
  | false => (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
        (ModuleCat.of A A)).hom
  | true => Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)

/-- The existing extension by zero along an open immersion.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev shriek (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Modules A pro U ⥤ Modules A pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j

/-- The open adjunction with inverse image, in its recorded normalization.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def openAdj (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    shriek A pro j ⊣ pull A pro j :=
  match pro with
  | false => Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  | true => ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j

/-- The actual open counit, with the canonical constant coefficient identification.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def epsilon (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (shriek A pro j).obj (constant A pro U) ⟶ constant A pro X :=
  ((openAdj A pro j).homEquiv _ _).symm (unitIso A pro j).inv

/-- The specified pullback comparison; pro-etale uses its recorded coherent square.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def square (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    pull A pro h ⋙ pull A pro i' ≅ pull A pro i ⋙ pull A pro g :=
  match pro with
  | false => Etale.squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq
  | true => ProEtale.supportSiteProEtaleComparisonSquare (ModuleCat.{u + 1} A) sq

/-- The closed adjunction transpose, with the coefficient object kept as a parameter.
Source: adjunction mate formula; Stacks 03S6
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def closedTranspose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (d : D) {d' : D'} (q : Q.obj d ⟶ d') :
    L.obj (s.obj d) ⟶ s'.obj d' :=
  a'.homEquiv _ _ (t.hom.app (s.obj d) ≫ Q.map (a.counit.app d) ≫ q)

/-- The canonical closed exchange, defined by its actual adjunction mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (constant A false Z) ≫ (Etale.lowerStar (ModuleCat.{u + 1} A) i').map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
          (ModuleCat.of A A)).hom
  | true => closedTranspose (adj A true i) (adj A true i')
      (pull A true h) (pull A true g) (square A true sq)
      (constant A true Z) (unitIso A true g).hom

/-- The inverse open comparison, formed by transposing a normalized open unit.
This is the displayed composite in the definition of `openBackward`.
Source: Stacks 03S6 (blueprint: lem-pur-supported-constant-exchange-normalization). -/
def openTranspose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) {d : D} {d' : D'} (q : Q.obj d ≅ d') :
    s'.obj d' ⟶ L.obj (s.obj d) :=
  (a'.homEquiv _ _).symm
    (q.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d))

/-- The inverse of the open comparison, as the transpose of the localized unit.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def openBackward (pro : Bool) {U' U X' X : Scheme.{u}}
    {g : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) :
    (shriek A pro j').obj (constant A pro U') ⟶
      (pull A pro h).obj ((shriek A pro j).obj (constant A pro U)) :=
  openTranspose (openAdj A pro j) (openAdj A pro j')
    (pull A pro h) (pull A pro g) (square A pro sq) (unitIso A pro g)

/-- The actual terminal object of the selected site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def terminal (pro : Bool) (X : Scheme.{u}) : Site pro X :=
  match pro with
  | false => Scheme.Etale.mk (𝟙 X)
  | true => Scheme.ProEt.mk (𝟙 X)

/-- Restriction to the complementary open, using the published support arrow.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def supportArrow (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Site pro X :=
  match pro with
  | false => Scheme.Etale.mk i.openComplement.ι
  | true => Scheme.ProEt.mk i.openComplement.ι

/-- The restriction arrow selecting the published support kernel.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def supportRestriction (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : supportArrow pro i ⟶ terminal pro X :=
  match pro with
  | false => Etale.supportRestrictionArrow i
  | true => ProEtale.supportRestrictionArrow i

/-- The existing kernel of restriction, for all ordinary module sheaves.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev sections (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (topology pro X) (ModuleCat.{u + 1} A)
    (supportRestriction pro i)

/-- The inverse-image unit on global sections, with the actual terminal base change.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def sigma (pro : Bool) {X' X : Scheme.{u}} (h : X' ⟶ X) (M : Modules A pro X) :
    M.obj.obj (op (terminal pro X)) ⟶
      ((pull A pro h).obj M).obj.obj (op (terminal pro X')) :=
  match pro with
  | false => ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map
        (MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
          (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)).inv.op
  | true => ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
      (op (Scheme.ProEt.mk (𝟙 X))) ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map
        (ProEtale.overPullbackObjMkIdIso h).inv.op

/-- The etale-to-pro-etale inverse image, with the recorded adjunction.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev compare (X : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X

/-- The scalar-preserving constant-unit identification for site comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev compareUnit (X : Scheme.{u}) := ProEtale.comparisonUpperStarUnitIso A X

/-- The recorded coherent comparison, with exactly the orientation in the node.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def comparePullback {X' X : Scheme.{u}} (h : X' ⟶ X) :
    pull A false h ⋙ compare A X' ≅ compare A X ⋙ pull A true h :=
  ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h

/-- The closed site exchange is the adjunction mate of that coherent comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def gamma {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (compare A X).obj (supported A false i) ⟶ supported A true i :=
  (adj A true i).homEquiv _ _
    ((comparePullback A i).inv.app (supported A false i) ≫
      (compare A Z).map ((adj A false i).counit.app (constant A false Z)) ≫
      (compareUnit A Z).hom)

/-- The canonical comparison on the open constants, with inverse orientation.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareOpenBackward {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (shriek A true j).obj (constant A true U) ⟶
      (compare A X).obj ((shriek A false j).obj (constant A false U)) :=
  ((openAdj A true j).homEquiv _ _).symm
    ((compareUnit A U).inv ≫
      (compare A U).map ((openAdj A false j).unit.app (constant A false U)) ≫
      (comparePullback A j).hom.app ((shriek A false j).obj (constant A false U)))

/-- The site-comparison unit on global sections, before taking its support kernel.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareSigma (X : Scheme.{u}) (M : Modules A false X) :
    M.obj.obj (op (terminal false X)) ⟶
      ((compare A X).obj M).obj.obj (op (terminal true X)) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M).hom.app
    (op (Scheme.Etale.mk (𝟙 X)))

-- The closed mate preserves the specified restriction once the constant units commute.
private lemma generic_functor_square_named {C D : Type*} [Category C] [Category D]
    {I : Type*} (F : I → C ⥤ D) (X : C) {Y : D}
    (q : ∀ i, (F i).obj X ⟶ Y) {i j : I} (h : i = j)
    {L R : C ⥤ D} (e : F i ≅ L) (d : F j ≅ R)
    (c : L ≅ R) (hc : c = e.symm ≪≫ eqToIso (congrArg F h) ≪≫ d)
    (a : L.obj X ⟶ Y) (b : R.obj X ⟶ Y)
    (ha : e.hom.app X ≫ a = q i) (hb : d.hom.app X ≫ b = q j) :
    c.hom.app X ≫ b = a := by
  subst c
  cases h
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso_refl, Iso.refl_hom,
    NatTrans.comp_app, Category.id_comp, Category.assoc, hb]
  rw [← ha, Iso.inv_hom_id_app_assoc]

private lemma normalized_closed_exchange
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (B : s ⋙ L ⟶ Q ⋙ s') (d : D) {d' : D'}
    (q : Q.obj d ⟶ d')
    (hb : r'.map (B.app d) ≫ a'.counit.app (Q.obj d) =
      t.hom.app (s.obj d) ≫ Q.map (a.counit.app d)) :
    B.app d ≫ s'.map q = closedTranspose a a' L Q t d q := by
  unfold closedTranspose
  apply (a'.homEquiv _ _).symm.injective
  change (a'.homEquiv (L.obj (s.obj d)) d').symm _ =
    (a'.homEquiv (L.obj (s.obj d)) d').symm ((a'.homEquiv _ _) _)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_right_symm]
  change (r'.map (B.app d) ≫ a'.counit.app (Q.obj d)) ≫ q = _
  rw [hb, Category.assoc]

private lemma normalized_closed_mate
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) {c : C} {d : D} {c' : C'} {d' : D'}
    (q : r.obj c ⟶ d) (q' : r'.obj c' ⟶ d')
    (qL : L.obj c ⟶ c') (qQ : Q.obj d ⟶ d')
    (h : t.hom.app c ≫ Q.map q ≫ qQ = r'.map qL ≫ q') :
    L.map (a.homEquiv _ _ q) ≫
        a'.homEquiv _ _ (t.hom.app (s.obj d) ≫ Q.map (a.counit.app d) ≫ qQ) =
      qL ≫ a'.homEquiv _ _ q' := by
  apply (a'.homEquiv _ _).symm.injective
  rw [← Adjunction.homEquiv_naturality_left,
    Equiv.symm_apply_apply, ← Adjunction.homEquiv_naturality_left,
    Equiv.symm_apply_apply]
  have hn := t.hom.naturality (a.homEquiv _ _ q)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← Q.map_comp_assoc]
  have hq : r.map (a.homEquiv _ _ q) ≫ a.counit.app d = q :=
    (a.homEquiv _ _).symm_apply_apply q
  rw [hq]
  exact h

private lemma normalized_closed_transpose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) {c : C} {d : D} {c' : C'} {d' : D'}
    (q : r.obj c ⟶ d) (q' : r'.obj c' ⟶ d')
    (qL : L.obj c ⟶ c') (qQ : Q.obj d ⟶ d')
    (h : t.hom.app c ≫ Q.map q ≫ qQ = r'.map qL ≫ q') :
    L.map (a.homEquiv _ _ q) ≫ closedTranspose a a' L Q t d qQ =
      qL ≫ a'.homEquiv _ _ q' := by
  exact normalized_closed_mate a a' L Q t q q' qL qQ h

-- Transposing the open comparison reduces counit compatibility to the constant square.
private lemma normalized_open_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) {c : C} {d : D} {c' : C'} {d' : D'}
    (q : r.obj c ≅ d) (q' : r'.obj c' ≅ d')
    (qL : L.obj c ≅ c') (qQ : Q.obj d ≅ d')
    (h : t.hom.app c ≫ Q.map q.hom ≫ qQ.hom = r'.map qL.hom ≫ q'.hom) :
    (a'.homEquiv _ _).symm
        (qQ.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d)) ≫
        L.map ((a.homEquiv _ _).symm q.inv) ≫ qL.hom =
      (a'.homEquiv _ _).symm q'.inv := by
  apply (a'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := t.inv.naturality ((a.homEquiv _ _).symm q.inv)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← Q.map_comp_assoc]
  rw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
  have hi : t.app c ≪≫ Q.mapIso q ≪≫ qQ = r'.mapIso qL ≪≫ q' := Iso.ext h
  have hinv : qQ.inv ≫ Q.map q.inv ≫ t.inv.app c =
      q'.inv ≫ r'.map qL.inv := by
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
      congrArg Iso.inv hi
  calc
    _ = (qQ.inv ≫ Q.map q.inv ≫ t.inv.app c) ≫ r'.map qL.hom := by
      simp only [Category.assoc]
    _ = (q'.inv ≫ r'.map qL.inv) ≫ r'.map qL.hom := by rw [hinv]
    _ = q'.inv := by
      simp only [Category.assoc, ← r'.map_comp, Iso.inv_hom_id]
      rw [r'.map_id, Category.comp_id]

-- Uniqueness and invertibility of a normalized map between two cokernel presentations.
private lemma normalized_cokernel_iso
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (L : C ⥤ D) [L.PreservesZeroMorphisms] [PreservesFiniteColimits L]
    {x y z : C} {x' y' z' : D}
    (f : x ⟶ y) (p : y ⟶ z) (w : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p w))
    (f' : x' ⟶ y') (p' : y' ⟶ z') (w' : f' ≫ p' = 0)
    (hc' : IsColimit (CokernelCofork.ofπ p' w'))
    (b : x' ≅ L.obj x) (q : L.obj y ≅ y') (d : L.obj z ⟶ z')
    (hb : b.hom ≫ L.map f ≫ q.hom = f')
    (hd : L.map p ≫ d = q.hom ≫ p') :
    IsIso d ∧ ∀ e : L.obj z ⟶ z',
      L.map p ≫ e = q.hom ≫ p' → e = d := by
  let c := CokernelCofork.mapIsColimit (CokernelCofork.ofπ p w) hc L
  have : Epi (L.map p) := Cofork.IsColimit.epi c
  let e := CokernelCofork.mapIsoOfIsColimit c hc'
    (Arrow.isoMk b.symm q (by
      apply (cancel_epi b.hom).mp
      change b.hom ≫ b.inv ≫ f' = b.hom ≫ L.map f ≫ q.hom
      simpa only [Iso.hom_inv_id_assoc] using hb.symm))
  have he : e.hom = d := by
    apply (cancel_epi (L.map p)).mp
    exact (CokernelCofork.π_mapOfIsColimit c _ _).trans hd.symm
  refine ⟨?_, ?_⟩
  · rw [← he]
    infer_instance
  · intro e he
    exact (cancel_epi (L.map p)).mp (he.trans hd.symm)

-- A normalized transpose is invertible when the corresponding open mate is.
private lemma open_transpose_isIso
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (b : Q ⋙ s' ≅ s ⋙ L)
    (hb : ∀ d : D, a'.unit.app (Q.obj d) ≫ r'.map (b.hom.app d) =
      Q.map (a.unit.app d) ≫ t.inv.app (s.obj d))
    {d : D} {d' : D'} (q : Q.obj d ≅ d') :
    IsIso ((a'.homEquiv _ _).symm
      (q.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d))) := by
  have he : (a'.homEquiv _ _).symm
      (q.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d)) =
        s'.map q.inv ≫ b.hom.app d := by
    apply (a'.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
    change _ = q.inv ≫ (a'.unit.app _ ≫ r'.map (b.hom.app d))
    rw [hb]
  rw [he]
  infer_instance

private lemma open_transpose_named
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (b : Q ⋙ s' ≅ s ⋙ L)
    (hb : ∀ d : D, a'.unit.app (Q.obj d) ≫ r'.map (b.hom.app d) =
      Q.map (a.unit.app d) ≫ t.inv.app (s.obj d))
    {d : D} {d' : D'} (q : Q.obj d ≅ d')
    : IsIso (openTranspose a a' L Q t q) := by
  unfold openTranspose
  have he : (a'.homEquiv _ _).symm
      (q.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d)) =
        s'.map q.inv ≫ b.hom.app d := by
    apply (a'.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_left]
    change _ = q.inv ≫ (a'.unit.app _ ≫ r'.map (b.hom.app d))
    rw [hb]
  rw [he]
  infer_instance

-- Use the already verified constant-section descriptions of the canonical units.
set_option backward.isDefEq.respectTransparency false in
private lemma pro_unit_adjunct {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (adj A true i).homEquiv _ _ (unitIso A true i).hom = restriction A true i := by
  simp only [unitIso, Iso.app_hom, ProEtale.CachedConstantCoherence.proConstant_eq_inverse]
  change (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _).symm
      (restriction A true i)) = restriction A true i
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private lemma et_constant_square {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (square A false sq).hom.app (constant A false X) ≫
        (pull A false g).map (unitIso A false i).hom ≫ (unitIso A false g).hom =
      (pull A false i').map (unitIso A false h).hom ≫ (unitIso A false i').hom := by
  dsimp only [square, Etale.squareUpperStarIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, unitIso, Iso.app_hom, pull, constant]
  simp only [Category.assoc]
  rw [Scheme.upperStarConstantSheafIso_comp]
  apply (cancel_epi ((Etale.upperStarComp (ModuleCat.{u + 1} A) i' h (g ≫ i)
    sq.w).hom.app (constant A false X))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  have hc (k : Z' ⟶ X) (hk : k = i' ≫ h) :
      (Etale.upperStarComp (ModuleCat.{u + 1} A) i' h k hk).hom.app
          (constant A false X) ≫
        (pull A false i').map (unitIso A false h).hom ≫ (unitIso A false i').hom =
      (unitIso A false k).hom := by
    subst k
    exact Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} A)
      i' h (ModuleCat.of A A)
  exact (hc (g ≫ i) sq.w).symm

set_option backward.isDefEq.respectTransparency false in
private lemma pro_constant_comp {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    (ProEtale.supportSiteProEtaleComparisonComp (ModuleCat.{u + 1} A) f g).hom.app
        (constant A true X) ≫ (pull A true f).map (unitIso A true g).hom ≫
          (unitIso A true f).hom = (unitIso A true (f ≫ g)).hom := by
  simp only [unitIso, Iso.app_hom, ProEtale.CachedConstantCoherence.proConstant_eq_inverse]
  exact (Scheme.constantInverse_comp (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology Z) (Scheme.proEtaleBaseChange g) (Scheme.proEtaleBaseChange f)
    (Scheme.proEtaleBaseChange (f ≫ g))
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (f ≫ g))
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    (ModuleCat.of A A)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pro_constant_square {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (square A true sq).hom.app (constant A true X) ≫
        (pull A true g).map (unitIso A true i).hom ≫ (unitIso A true g).hom =
      (pull A true i').map (unitIso A true h).hom ≫ (unitIso A true i').hom := by
  exact generic_functor_square_named
    (ProEtale.supportSiteProEtaleComparisonPullback (ModuleCat.{u + 1} A))
    (constant A true X) (fun f ↦ (unitIso A true f).hom) sq.w.symm
    (ProEtale.supportSiteProEtaleComparisonComp (ModuleCat.{u + 1} A) i' h)
    (ProEtale.supportSiteProEtaleComparisonComp (ModuleCat.{u + 1} A) g i)
    (square A true sq) rfl
    ((pull A true i').map (unitIso A true h).hom ≫ (unitIso A true i').hom)
    ((pull A true g).map (unitIso A true i).hom ≫ (unitIso A true g).hom)
    (pro_constant_comp A i' h) (pro_constant_comp A g i)

set_option backward.isDefEq.respectTransparency false in
private lemma restriction_adjunct (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X) :
    restriction A pro i = (adj A pro i).homEquiv _ _ (unitIso A pro i).hom := by
  cases pro
  · rfl
  · exact (pro_unit_adjunct A i).symm

set_option backward.isDefEq.respectTransparency false in
private lemma exchange_mate (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    exchange A pro sq = closedTranspose (adj A pro i) (adj A pro i')
      (pull A pro h) (pull A pro g) (square A pro sq)
      (constant A pro Z) (unitIso A pro g).hom := by
  cases pro
  · exact normalized_closed_exchange
      (adj A false i) (adj A false i') (pull A false h) (pull A false g)
      (square A false sq) (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
      (constant A false Z) (unitIso A false g).hom
      (Etale.upperStar_map_baseChangeMap_app_counit (ModuleCat.{u + 1} A)
        sq.toCommSq (constant A false Z))
  · rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exchange_normalized (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).map (restriction A pro i) ≫ exchange A pro sq =
      (unitIso A pro h).hom ≫ restriction A pro i' := by
  rw [restriction_adjunct, restriction_adjunct, exchange_mate]
  apply normalized_closed_transpose (adj A pro i) (adj A pro i')
    (pull A pro h) (pull A pro g) (square A pro sq)
  cases pro
  · exact et_constant_square A sq
  · exact pro_constant_square A sq

set_option backward.isDefEq.respectTransparency false in
private lemma compare_unit_terminal (X : Scheme.{u}) :
    (compareUnit A X).hom =
      (ProEtale.CachedConstantCoherence.constantComparisonTerminal
        (ModuleCat.{u + 1} A) X).hom.app (ModuleCat.of A A) := by
  rw [ProEtale.CachedConstantCoherence.constantComparisonTerminal_eq_inverse]
  change ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _).symm
    (Functor.LaxMonoidal.ε (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X)) = _
  unfold Scheme.constantInverse
  erw [ConstantProof.constantDirect_unit_monoidal]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma compare_constant_square {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (comparePullback A i).inv.app (constant A false X) ≫
        (compare A Z).map (unitIso A false i).hom ≫ (compareUnit A Z).hom =
      (pull A true i).map (compareUnit A X).hom ≫ (unitIso A true i).hom := by
  simp only [compare_unit_terminal]
  exact (ProEtale.CachedConstantCoherence.constantComparisonTerminal_square
    (ModuleCat.{u + 1} A) i (ModuleCat.of A A)).symm

set_option backward.isDefEq.respectTransparency false in
private lemma gamma_normalized {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (compare A X).map (restriction A false i) ≫ gamma A i =
      (compareUnit A X).hom ≫ restriction A true i := by
  rw [restriction_adjunct, restriction_adjunct]
  exact normalized_closed_mate (adj A false i) (adj A true i)
    (compare A X) (compare A Z) (comparePullback A i).symm
    (unitIso A false i).hom (unitIso A true i).hom
    (compareUnit A X).hom (compareUnit A Z).hom (compare_constant_square A i)

private lemma generic_inverse_square {C D : Type*} [Category C] [Category D]
    {I : Type*} (F : I → C ⥤ D) {i j : I} (h : i = j)
    {L R : C ⥤ D} (e : F i ≅ L) (d : F j ≅ R) :
    e.symm ≪≫ eqToIso (congrArg F h) ≪≫ d =
      (d.symm ≪≫ eqToIso (congrArg F h.symm) ≪≫ e).symm := by
  cases h
  simp only [congrArg, eqToIso_refl, Iso.refl_trans,
    Iso.trans_symm, Iso.symm_symm_eq]

private lemma generic_unit_mate_named
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (b : Q ⋙ s' ⟶ s ⋙ L) (t : r ⋙ Q ⟶ L ⋙ r')
    (ht : (mateEquiv a a' b) = t) (d : D) :
    a'.unit.app (Q.obj d) ≫ r'.map (b.app d) =
      Q.map (a.unit.app d) ≫ t.app (s.obj d) := by
  rw [← ht]
  exact (unit_mateEquiv a a' b d).symm

private lemma pro_open_unit (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {U' U X' X : Scheme.{u}} {g : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) (M : Sheaf (Scheme.ProEt.topology U) D) :
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j').unit.app
        ((ProEtale.upperStar D g).obj M) ≫
      (ProEtale.upperStar D j').map
        ((ProEtale.openImmersionLowerShriekBaseChangeMap D sq.toCommSq).app M) =
    (ProEtale.upperStar D g).map
        ((ProEtale.openImmersionLowerShriekUpperStarAdjunction D j).unit.app M) ≫
      (ProEtale.supportSiteProEtaleComparisonSquare D sq).inv.app
        ((ProEtale.openImmersionLowerShriek D j).obj M) := by
  apply generic_unit_mate_named
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j')
    (ProEtale.upperStar D h) (ProEtale.upperStar D g)
    (ProEtale.openImmersionLowerShriekBaseChangeMap D sq.toCommSq)
    (ProEtale.supportSiteProEtaleComparisonSquare D sq).inv
    (d := M)
  rw [ProEtale.mateEquiv_openImmersionLowerShriekBaseChangeMap]
  have ht : ProEtale.upperStarCompIso D sq.w =
      (ProEtale.supportSiteProEtaleComparisonSquare D sq).symm := by
    exact generic_inverse_square
      (ProEtale.supportSiteProEtaleComparisonPullback D) sq.w
      (ProEtale.supportSiteProEtaleComparisonComp D g j)
      (ProEtale.supportSiteProEtaleComparisonComp D j' h)
  exact congrArg Iso.hom ht

private lemma pro_open_transpose_named (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {U' U X' X : Scheme.{u}} {g : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h)
    (N : Sheaf (Scheme.ProEt.topology U) D) (N' : Sheaf (Scheme.ProEt.topology U') D)
    (q : (ProEtale.upperStar D g).obj N ≅ N') :
    IsIso (openTranspose
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j)
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j')
      (ProEtale.upperStar D h) (ProEtale.upperStar D g)
      (ProEtale.supportSiteProEtaleComparisonSquare D sq) q) := by
  have hs := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have := ProEtale.isIso_openImmersionLowerShriekBaseChangeMap D hs
  exact open_transpose_named
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction D j')
    (ProEtale.upperStar D h) (ProEtale.upperStar D g)
    (ProEtale.supportSiteProEtaleComparisonSquare D sq)
    (asIso (ProEtale.openImmersionLowerShriekBaseChangeMap D sq.toCommSq))
    (fun d ↦ pro_open_unit D sq d) q

private lemma et_open_transpose_named (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {U' U X' X : Scheme.{u}} {g : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h)
    (N : Sheaf U.smallEtaleTopology D) (N' : Sheaf U'.smallEtaleTopology D)
    (q : (Etale.upperStar D g).obj N ≅ N') :
    IsIso (openTranspose
      (Etale.openImmersionLowerShriekUpperStarAdjunction D j)
      (Etale.openImmersionLowerShriekUpperStarAdjunction D j')
      (Etale.upperStar D h) (Etale.upperStar D g)
      (Etale.squareUpperStarIso D sq.toCommSq) q) := by
  have hs := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap D hs
  apply open_transpose_named
    (Etale.openImmersionLowerShriekUpperStarAdjunction D j)
    (Etale.openImmersionLowerShriekUpperStarAdjunction D j')
    (Etale.upperStar D h) (Etale.upperStar D g)
    (Etale.squareUpperStarIso D sq.toCommSq)
    (asIso (Etale.openImmersionLowerShriekBaseChangeMap D sq.toCommSq)) (q := q)
  intro d
  have hu := Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app D sq.toCommSq d
  rw [Etale.squareUpperStarIso_flip D sq.toCommSq] at hu
  exact hu

set_option backward.isDefEq.respectTransparency false in
private lemma open_backward_isIso (pro : Bool) {U' U X' X : Scheme.{u}}
    {g : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) : IsIso (openBackward A pro sq) := by
  cases pro
  · exact et_open_transpose_named (ModuleCat.{u + 1} A) sq _ _ (unitIso A false g)
  · exact pro_open_transpose_named (ModuleCat.{u + 1} A) sq _ _ (unitIso A true g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma compare_open_isIso [Finite A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : IsIso (compareOpenBackward A j) := by
  let c : shriek A false j ⋙ compare A X ≅ compare A U ⋙ shriek A true j :=
    ProEtale.openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j
  apply open_transpose_isIso (openAdj A false j) (openAdj A true j)
    (compare A X) (compare A U) (comparePullback A j).symm c.symm
    (q := compareUnit A U)
  intro d
  have hn := (ProEtale.openComparison_unit_normalization A j).2 d
  have hr : (compare A U).map
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app d) ≫
        (ProEtale.openComparisonRestrictionIso A j).hom.app
          ((shriek A false j).obj d) =
      (ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((compare A U).obj d) ≫
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j).map (c.inv.app d) := by
    apply (Iso.cancel_iso_hom_right _ _
      ((ProEtale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapIso (c.app d))).mp
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [Category.assoc]
    change _ = _ at hn
    erw [hn]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply (Iso.cancel_iso_hom_right _ _
    ((ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app
      ((compare A X).obj ((shriek A false j).obj d)))).mp
  have hp := (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.naturality
    (c.inv.app d)
  change _ = _ at hp
  erw [Category.assoc, hp]
  change ((ProEtale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app _ ≫
      (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv.app _) ≫
      (ProEtale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app _ ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hr]
  dsimp only [ProEtale.openComparisonRestrictionIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom]
  change _ = (compare A U).map
      ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app d ≫
        (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv.app _) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction is the cokernel of the open constant counit in both topologies.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem presentation (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ w : epsilon P.Coefficient pro i.openComplement.ι ≫
        restriction P.Coefficient pro i = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (restriction P.Coefficient pro i) w)) := by
  let A := ULift.{u + 1, u} P.Ring
  cases pro
  · let S := Etale.openClosedShortComplex (ModuleCat.{u + 1} A) i.openComplement.ι i
      (disjoint_range_of_range_eq_compl i.openComplement.ι i
        i.range_eq_compl_range_openComplement_ι) (constant A false X)
    have hs : S.ShortExact := Etale.shortExact_openClosedShortComplex
      (ModuleCat.{u + 1} A) i.openComplement.ι i (constant A false X)
      i.range_eq_compl_range_openComplement_ι
    let ex := (shriek A false i.openComplement.ι).mapIso
      (unitIso A false i.openComplement.ι)
    let ez := (push A false i).mapIso (unitIso A false i)
    have he : epsilon A false i.openComplement.ι = ex.inv ≫ S.f := by
      rw [epsilon, Adjunction.homEquiv_symm_apply]
      rfl
    have hr : restriction A false i = S.g ≫ ez.hom := by
      rw [restriction, Adjunction.homEquiv_apply]
      rfl
    have hz : epsilon A false i.openComplement.ι ≫ restriction A false i = 0 := by
      rw [he, hr]
      simp only [Category.assoc, S.zero_assoc, comp_zero, zero_comp]
    have := hs.epi_g
    refine ⟨hz, ⟨?_⟩⟩
    exact IsCokernel.ofIso S.f hs.exact.gIsCokernel (CokernelCofork.ofπ _ hz)
      ex (Iso.refl _) ez (by simp [he]) (by simpa using hr)
  · have : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    let C := ModuleCat.{u + 1} (ULift.{u + 1, u} P.Ring)
    let j := i.openComplement.ι
    let a := ProEtale.openImmersionLowerShriekAdjunction C j
    let b : (shriek A true j).obj (constant A true i.openComplement.toScheme) ⟶
        constant A true X := ProEtale.openConstantArrow j P.Ring
    let r := restriction A true i
    let t := a.homEquiv _ _ (epsilon A true j)
    have ht : IsIso t := by
      change IsIso (a.homEquiv _ _
        (((a.ofNatIsoRight (ProEtale.upperStarIsoOpenImmersionRestriction C j).symm
          ).homEquiv _ _).symm (unitIso A true j).inv))
      rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Equiv.apply_symm_apply]
      infer_instance
    have hb : IsIso (a.homEquiv _ _ b) := by
      dsimp only [a, b, ProEtale.openConstantArrow, ProEtale.openConstantMap]
      erw [Equiv.apply_symm_apply]
      exact Scheme.fixedOpenConstantMap_isIso j P.Ring
    let tb := a.homEquiv _ _ b
    have : IsIso tb := hb
    let e := (shriek A true j).mapIso (asIso t ≪≫ (asIso tb).symm)
    have he : epsilon A true j = e.hom ≫ b := by
      apply (a.homEquiv _ _).injective
      dsimp only [e, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
        asIso_hom, asIso_inv]
      rw [Adjunction.homEquiv_naturality_left]
      change t = (t ≫ inv (a.homEquiv _ _ b)) ≫ a.homEquiv _ _ b
      simp
    obtain ⟨w, ⟨hc⟩⟩ := ProEtale.fixedConstantPresentation P.Ring i
    have hz : epsilon A true j ≫ r = 0 := by
      rw [he, Category.assoc]
      exact (congrArg (fun f ↦ e.hom ≫ f) w).trans (comp_zero)
    refine ⟨hz, ⟨?_⟩⟩
    exact IsCokernel.ofIso b hc (CokernelCofork.ofπ r hz)
      e.symm (Iso.refl _) (Iso.refl _) (by simp [he]) (by rfl)

/-- Exact pullback, the actual open counit comparison, and the canonical closed mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem scheme_normalization (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    PreservesFiniteLimits (pull P.Coefficient pro h) ∧
    PreservesFiniteColimits (pull P.Coefficient pro h) ∧
    (∀ (gU : i'.openComplement.toScheme ⟶ i.openComplement.toScheme)
      (sqU : ChosenCartesianSquare gU i'.openComplement.ι i.openComplement.ι h),
      IsIso (openBackward P.Coefficient pro sqU) ∧
      openBackward P.Coefficient pro sqU ≫
          (pull P.Coefficient pro h).map (epsilon P.Coefficient pro i.openComplement.ι) ≫
            (unitIso P.Coefficient pro h).hom =
        epsilon P.Coefficient pro i'.openComplement.ι) ∧
    IsIso (exchange P.Coefficient pro sq) ∧
    (pull P.Coefficient pro h).map (restriction P.Coefficient pro i) ≫
        exchange P.Coefficient pro sq =
      (unitIso P.Coefficient pro h).hom ≫ restriction P.Coefficient pro i' ∧
    (∀ d : (pull P.Coefficient pro h).obj (supported P.Coefficient pro i) ⟶
        supported P.Coefficient pro i',
      (pull P.Coefficient pro h).map (restriction P.Coefficient pro i) ≫ d =
        (unitIso P.Coefficient pro h).hom ≫ restriction P.Coefficient pro i' →
      d = exchange P.Coefficient pro sq) := by
  let A := P.Coefficient
  have hl : PreservesFiniteLimits (pull A pro h) := by cases pro <;> infer_instance
  have hc : PreservesFiniteColimits (pull A pro h) := by cases pro <;> infer_instance
  let := hl
  let := hc
  have : (pull A pro h).PreservesZeroMorphisms := by cases pro <;> infer_instance
  have ho (gU : i'.openComplement.toScheme ⟶ i.openComplement.toScheme)
      (sqU : ChosenCartesianSquare gU i'.openComplement.ι i.openComplement.ι h) :
      IsIso (openBackward A pro sqU) ∧
      openBackward A pro sqU ≫ (pull A pro h).map
          (epsilon A pro i.openComplement.ι) ≫ (unitIso A pro h).hom =
        epsilon A pro i'.openComplement.ι := by
    refine ⟨open_backward_isIso A pro sqU, ?_⟩
    apply normalized_open_counit (openAdj A pro i.openComplement.ι)
      (openAdj A pro i'.openComplement.ι) (pull A pro h) (pull A pro gU)
      (square A pro sqU) (unitIso A pro i.openComplement.ι)
      (unitIso A pro i'.openComplement.ι) (unitIso A pro h) (unitIso A pro gU)
    cases pro
    · exact et_constant_square A sqU
    · exact pro_constant_square A sqU
  have hn := exchange_normalized A pro sq
  have hs : IsPullback g i' i h := IsPullback.of_iso_pullback
    sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have he : h ⁻¹ᵁ i.openComplement = i'.openComplement := by
    ext x
    change h.base x ∉ Set.range i.base ↔ x ∉ Set.range i'.base
    rw [Scheme.range_snd_of_isPullback hs]
    rfl
  let gU := h.resLE i.openComplement i'.openComplement he.symm.le
  have hf : gU ≫ i.openComplement.ι = i'.openComplement.ι ≫ h :=
    Scheme.Hom.resLE_comp_ι h he.symm.le
  have hu : IsPullback gU i'.openComplement.ι i.openComplement.ι h :=
    IsOpenImmersion.isPullback _ _ _ _ hf.symm (by simpa using he)
  let sqU : ChosenCartesianSquare gU i'.openComplement.ι i.openComplement.ι h :=
    { w := hf
      isoPullback := hu.isoPullback
      hom_fst := hu.isoPullback_hom_fst
      hom_snd := hu.isoPullback_hom_snd }
  obtain ⟨w, ⟨hp⟩⟩ := presentation P pro i
  obtain ⟨w', ⟨hp'⟩⟩ := presentation P pro i'
  have := (ho gU sqU).1
  obtain ⟨hi, unique⟩ := normalized_cokernel_iso (pull A pro h)
    (epsilon A pro i.openComplement.ι) (restriction A pro i) w hp
    (epsilon A pro i'.openComplement.ι) (restriction A pro i') w' hp'
    (asIso (openBackward A pro sqU)) (unitIso A pro h) (exchange A pro sq)
    (ho gU sqU).2 hn
  exact ⟨hl, hc, ho, hi, hn, unique⟩

/-- The same normalization for the prescribed site-comparison mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem site_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (compare P.Coefficient X) ∧
    PreservesFiniteColimits (compare P.Coefficient X) ∧
    IsIso (compareOpenBackward P.Coefficient i.openComplement.ι) ∧
    compareOpenBackward P.Coefficient i.openComplement.ι ≫
        (compare P.Coefficient X).map (epsilon P.Coefficient false i.openComplement.ι) ≫
          (compareUnit P.Coefficient X).hom = epsilon P.Coefficient true i.openComplement.ι ∧
    IsIso (gamma P.Coefficient i) ∧
    (compare P.Coefficient X).map (restriction P.Coefficient false i) ≫
        gamma P.Coefficient i =
      (compareUnit P.Coefficient X).hom ≫ restriction P.Coefficient true i ∧
    (∀ d : (compare P.Coefficient X).obj (supported P.Coefficient false i) ⟶
        supported P.Coefficient true i,
      (compare P.Coefficient X).map (restriction P.Coefficient false i) ≫ d =
        (compareUnit P.Coefficient X).hom ≫ restriction P.Coefficient true i →
      d = gamma P.Coefficient i) := by
  let A := P.Coefficient
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : Finite A := (Equiv.ulift : A ≃ P.Ring).finite_iff.mpr inferInstance
  have hl : PreservesFiniteLimits (compare A X) := inferInstance
  have hc : PreservesFiniteColimits (compare A X) := inferInstance
  have hb := compare_open_isIso A i.openComplement.ι
  let := hb
  have he : compareOpenBackward A i.openComplement.ι ≫
      (compare A X).map (epsilon A false i.openComplement.ι) ≫
        (compareUnit A X).hom = epsilon A true i.openComplement.ι := by
    apply normalized_open_counit (openAdj A false i.openComplement.ι)
      (openAdj A true i.openComplement.ι) (compare A X)
      (compare A i.openComplement.toScheme) (comparePullback A i.openComplement.ι).symm
      (unitIso A false i.openComplement.ι) (unitIso A true i.openComplement.ι)
      (compareUnit A X) (compareUnit A i.openComplement.toScheme)
    exact compare_constant_square A i.openComplement.ι
  have hn := gamma_normalized A i
  obtain ⟨w, ⟨hp⟩⟩ := presentation P false i
  obtain ⟨w', ⟨hp'⟩⟩ := presentation P true i
  obtain ⟨hi, unique⟩ := normalized_cokernel_iso (compare A X)
    (epsilon A false i.openComplement.ι) (restriction A false i) w hp
    (epsilon A true i.openComplement.ι) (restriction A true i) w' hp'
    (asIso (compareOpenBackward A i.openComplement.ι)) (compareUnit A X)
    (gamma A i) he hn
  exact ⟨hl, hc, hb, he, hi, hn, unique⟩

/-- Normalization of the supported-section transformation by its kernel inclusion.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def SectionCondition (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsClosedImmersion i] [IsClosedImmersion i']
    (h : X' ⟶ X)
    (l : sections A pro i ⟶ pull A pro h ⋙ sections A pro i') : Prop :=
  ∀ M : Modules A pro X,
    l.app M ≫ kernel.ι (((pull A pro h).obj M).obj.map (supportRestriction pro i').op) =
      kernel.ι (M.obj.map (supportRestriction pro i).op) ≫ sigma A pro h M

/-- The supported inverse-image section transformation exists and is uniquely normalized.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Evaluate the inverse-image unit at the terminal object. The localized direct-image
identity of Stacks 04J0 makes its restrictions on X and U commute (node step 7).
Consequently it sends the kernel of restriction into the target kernel. Apply the kernel
universal property on each module sheaf. Naturality follows from naturality of the unit;
uniqueness follows from the monic kernel inclusion. This works for every module sheaf,
without a compactness or finiteness assumption. -/
theorem sectionMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (_sq : ChosenCartesianSquare g i' i h) :
    ∃! l : sections P.Coefficient pro i ⟶
        pull P.Coefficient pro h ⋙ sections P.Coefficient pro i',
      SectionCondition P.Coefficient pro h l := by
  let A := P.Coefficient
  have hs : IsPullback g i' i h :=
    IsPullback.of_iso_pullback _sq.toCommSq _sq.isoPullback _sq.hom_fst _sq.hom_snd
  have hu : Set.range (i'.openComplement.ι ≫ h).base ⊆
      Set.range i.openComplement.ι.base := by
    rw [← compl_compl (Set.range i.openComplement.ι.base),
      ← i.range_eq_compl_range_openComplement_ι, Set.subset_compl_iff_disjoint_left,
      Set.disjoint_left]
    rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
    apply x.2
    rw [Scheme.range_snd_of_isPullback hs]
    exact ⟨z, hx.symm⟩
  let gU := IsOpenImmersion.lift i.openComplement.ι (i'.openComplement.ι ≫ h) hu
  have hgU : gU ≫ i.openComplement.ι = i'.openComplement.ι ≫ h :=
    IsOpenImmersion.lift_fac _ _ _
  cases pro
  · let F := MorphismProperty.Over.pullback @Etale ⊤ h
    let t : F.obj (terminal false X) ≅ terminal false X' :=
      MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
        (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)
    let r : supportArrow false i' ⟶ F.obj (supportArrow false i) :=
      MorphismProperty.Over.homMk (pullback.lift gU i'.openComplement.ι hgU)
        (by change pullback.lift _ _ _ ≫ pullback.snd _ _ = i'.openComplement.ι; simp) (by trivial)
    have hr : r ≫ F.map (supportRestriction false i) =
        supportRestriction false i' ≫ t.inv := by
      apply (cancel_mono t.hom).1
      exact (Scheme.Etale.isTerminalMkId X').hom_ext _ _
    let eta := (adj A false h).unit
    have w (M : Modules A false X) :
        M.obj.map (supportRestriction false i).op ≫
            (eta.app M).hom.app (op (supportArrow false i)) ≫
              ((pull A false h).obj M).obj.map r.op =
          sigma A false h M ≫
            ((pull A false h).obj M).obj.map (supportRestriction false i').op := by
      have en := (eta.app M).hom.naturality (supportRestriction false i).op
      change M.obj.map _ ≫ (eta.app M).hom.app _ =
        (eta.app M).hom.app _ ≫ ((pull A false h).obj M).obj.map
          (F.map (supportRestriction false i)).op at en
      change M.obj.map _ ≫ (eta.app M).hom.app _ ≫ _ =
        (eta.app M).hom.app _ ≫ ((pull A false h).obj M).obj.map t.inv.op ≫ _
      calc
        _ = ((eta.app M).hom.app (op (terminal false X)) ≫
            ((pull A false h).obj M).obj.map (F.map (supportRestriction false i)).op) ≫
              ((pull A false h).obj M).obj.map r.op :=
          congrArg (fun z ↦ z ≫ ((pull A false h).obj M).obj.map r.op) en
        _ = _ := by
          simp only [Category.assoc, ← Functor.map_comp]
          exact congrArg (fun z ↦ (eta.app M).hom.app (op (terminal false X)) ≫
            ((pull A false h).obj M).obj.map z) (congrArg Quiver.Hom.op hr)
    let l : sections A false i ⟶ pull A false h ⋙ sections A false i' :=
      { app := fun M ↦ kernel.map _ _ (sigma A false h M)
          ((eta.app M).hom.app (op (supportArrow false i)) ≫
            ((pull A false h).obj M).obj.map r.op) (w M)
        naturality := by
          intro M N f
          apply (cancel_mono (kernel.ι
            (((pull A false h).obj N).obj.map (supportRestriction false i').op))).1
          dsimp [sections, Sheaf.supportedSectionsFunctor]
          simp only [kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
          have e := congrArg (fun q ↦ q.hom.app (op (terminal false X)))
            (eta.naturality f)
          change f.hom.app _ ≫ (eta.app N).hom.app _ =
            (eta.app M).hom.app _ ≫
              ((pull A false h).map f).hom.app (op (F.obj (terminal false X))) at e
          change kernel.ι _ ≫ f.hom.app _ ≫
              ((eta.app N).hom.app _ ≫ ((pull A false h).obj N).obj.map t.inv.op) =
            kernel.ι _ ≫ ((eta.app M).hom.app _ ≫
              ((pull A false h).obj M).obj.map t.inv.op) ≫ ((pull A false h).map f).hom.app _
          simp only [Category.assoc]
          rw [← Category.assoc (f.hom.app _), e, Category.assoc]
          rw [← (((pull A false h).map f).hom.naturality t.inv.op)] }
    refine ⟨l, ?_, ?_⟩
    · intro M
      exact kernel.lift_ι _ _ _
    · intro l' hl'
      apply NatTrans.ext
      funext M
      apply (cancel_mono (kernel.ι
        (((pull A false h).obj M).obj.map (supportRestriction false i').op))).1
      exact (hl' M).trans (kernel.lift_ι _ _ _).symm
  · let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ h
    let t : F.obj (terminal true X) ≅ terminal true X' :=
      MorphismProperty.Over.isoMk (P := @WeaklyEtale) (Q := ⊤)
        (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)
    let r : supportArrow true i' ⟶ F.obj (supportArrow true i) :=
      MorphismProperty.Over.homMk (pullback.lift gU i'.openComplement.ι hgU)
        (by change pullback.lift _ _ _ ≫ pullback.snd _ _ = i'.openComplement.ι; simp) (by trivial)
    have hr : r ≫ F.map (supportRestriction true i) =
        supportRestriction true i' ≫ t.inv := by
      apply (cancel_mono t.hom).1
      exact (Scheme.ProEt.isTerminalMkId X').hom_ext _ _
    let eta := (adj A true h).unit
    have w (M : Modules A true X) :
        M.obj.map (supportRestriction true i).op ≫
            (eta.app M).hom.app (op (supportArrow true i)) ≫
              ((pull A true h).obj M).obj.map r.op =
          sigma A true h M ≫
            ((pull A true h).obj M).obj.map (supportRestriction true i').op := by
      have en := (eta.app M).hom.naturality (supportRestriction true i).op
      change M.obj.map _ ≫ (eta.app M).hom.app _ =
        (eta.app M).hom.app _ ≫ ((pull A true h).obj M).obj.map
          (F.map (supportRestriction true i)).op at en
      change M.obj.map _ ≫ (eta.app M).hom.app _ ≫ _ =
        (eta.app M).hom.app _ ≫ ((pull A true h).obj M).obj.map t.inv.op ≫ _
      calc
        _ = ((eta.app M).hom.app (op (terminal true X)) ≫
            ((pull A true h).obj M).obj.map (F.map (supportRestriction true i)).op) ≫
              ((pull A true h).obj M).obj.map r.op :=
          congrArg (fun z ↦ z ≫ ((pull A true h).obj M).obj.map r.op) en
        _ = _ := by
          simp only [Category.assoc, ← Functor.map_comp]
          exact congrArg (fun z ↦ (eta.app M).hom.app (op (terminal true X)) ≫
            ((pull A true h).obj M).obj.map z) (congrArg Quiver.Hom.op hr)
    let l : sections A true i ⟶ pull A true h ⋙ sections A true i' :=
      { app := fun M ↦ kernel.map _ _ (sigma A true h M)
          ((eta.app M).hom.app (op (supportArrow true i)) ≫
            ((pull A true h).obj M).obj.map r.op) (w M)
        naturality := by
          intro M N f
          apply (cancel_mono (kernel.ι
            (((pull A true h).obj N).obj.map (supportRestriction true i').op))).1
          dsimp [sections, Sheaf.supportedSectionsFunctor]
          simp only [kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
          have e := congrArg (fun q ↦ q.hom.app (op (terminal true X)))
            (eta.naturality f)
          change f.hom.app _ ≫ (eta.app N).hom.app _ =
            (eta.app M).hom.app _ ≫
              ((pull A true h).map f).hom.app (op (F.obj (terminal true X))) at e
          change kernel.ι _ ≫ f.hom.app _ ≫
              ((eta.app N).hom.app _ ≫ ((pull A true h).obj N).obj.map t.inv.op) =
            kernel.ι _ ≫ ((eta.app M).hom.app _ ≫
              ((pull A true h).obj M).obj.map t.inv.op) ≫ ((pull A true h).map f).hom.app _
          simp only [Category.assoc]
          rw [← Category.assoc (f.hom.app _), e, Category.assoc]
          rw [← (((pull A true h).map f).hom.naturality t.inv.op)] }
    refine ⟨l, ?_, ?_⟩
    · intro M
      exact kernel.lift_ι _ _ _
    · intro l' hl'
      apply NatTrans.ext
      funext M
      apply (cancel_mono (kernel.ι
        (((pull A true h).obj M).obj.map (supportRestriction true i').op))).1
      exact (hl' M).trans (kernel.lift_ι _ _ _).symm

/-- The canonical kernel restriction of the inverse-image unit, determined uniquely.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def sectionMap (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    sections P.Coefficient pro i ⟶
      pull P.Coefficient pro h ⋙ sections P.Coefficient pro i' :=
  (sectionMap_existsUnique P pro sq).choose

/-- Normalization of the site-comparison section transformation.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def CompareSectionCondition {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : sections A false i ⟶ compare A X ⋙ sections A true i) : Prop :=
  ∀ M : Modules A false X,
    l.app M ≫ kernel.ι (((compare A X).obj M).obj.map (supportRestriction true i).op) =
      kernel.ι (M.obj.map (supportRestriction false i).op) ≫ compareSigma A X M

/-- The uniquely normalized supported-section map for the site comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Evaluate the inverse-image unit at the terminal object. The localized direct-image
identity of Stacks 04J0 makes its restrictions on X and U commute (node step 7).
Consequently it sends the kernel of restriction into the target kernel. Apply the kernel
universal property on each module sheaf. Naturality follows from naturality of the unit;
uniqueness follows from the monic kernel inclusion. This works for every module sheaf,
without a compactness or finiteness assumption. -/
theorem compareSectionMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! l : sections P.Coefficient false i ⟶
        compare P.Coefficient X ⋙ sections P.Coefficient true i,
      CompareSectionCondition P.Coefficient i l := by
  let A := P.Coefficient
  let eta := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit
  let l : sections A false i ⟶ compare A X ⋙ sections A true i :=
    { app := fun M ↦ (sections A false i).map (eta.app M)
      naturality := by
        intro M N f
        change (sections A false i).map f ≫ (sections A false i).map (eta.app N) =
          (sections A false i).map (eta.app M) ≫
            (sections A false i).map
              ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X).map
                ((compare A X).map f))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (sections A false i).map (eta.naturality f) }
  refine ⟨l, ?_, ?_⟩
  · intro M
    exact kernel.lift_ι _ _ _
  · intro l' hl'
    apply NatTrans.ext
    funext M
    apply (cancel_mono (kernel.ι
      (((compare A X).obj M).obj.map (supportRestriction true i).op))).1
    exact (hl' M).trans (kernel.lift_ι _ _ _).symm

/-- The canonical site-comparison map on kernels of restriction, for every module.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareSectionMap (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    sections P.Coefficient false i ⟶
      compare P.Coefficient X ⋙ sections P.Coefficient true i :=
  (compareSectionMap_existsUnique P i).choose

set_option backward.isDefEq.respectTransparency false in
private lemma sigma_comparison_square {X' X : Scheme.{u}} (h : X' ⟶ X)
    (M : Modules A false X) :
    sigma A false h M ≫ compareSigma A X' ((pull A false h).obj M) ≫
        ((comparePullback A h).hom.app M).hom.app (op (terminal true X')) =
      compareSigma A X M ≫ sigma A true h ((compare A X).obj M) := by
  let ae := (adj A false h).comp (ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} A) X')
  let ap := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp (adj A true h)
  let d := ProEtale.supportSiteComparisonCoefficientDirectImageIso
    (ModuleCat.{u + 1} A) h
  have hu := unit_conjugateEquiv_symm ap ae d.hom M
  have hk : ((conjugateEquiv ap ae).symm d.hom) = (comparePullback A h).hom := by
    rfl
  rw [hk] at hu
  dsimp only [ae, ap] at hu
  have e := congrArg (fun t ↦ t.hom.app (op (Scheme.Etale.mk (𝟙 X)))) hu
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at e
  have hd : (d.hom.app ((pull A true h).obj ((compare A X).obj M))).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) = 𝟙 _ := by
    dsimp only [d, ProEtale.supportSiteComparisonCoefficientDirectImageIso]
    change ((𝟙 _ ≫ _ ≫ 𝟙 _)) = 𝟙 _
    simp only [ProEtale.supportSiteComparisonSiteBaseChangeIso, Category.id_comp,
      Category.comp_id]
    exact CategoryTheory.Functor.map_id _ _
  erw [hd, Category.comp_id] at e
  let t : (MorphismProperty.Over.pullback @Etale ⊤ h).obj (terminal false X) ≅
      terminal false X' := MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
    (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)
  have en := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X').unit.app
    ((pull A false h).obj M)).hom.naturality t.inv.op
  have kn := ((comparePullback A h).hom.app M).hom.naturality
    (ProEtale.overPullbackObjMkIdIso h).inv.op
  dsimp only [sigma, compareSigma]
  simp only [Category.assoc]
  erw [reassoc_of% en]
  have ht : ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) X').obj
      ((compare A X').obj ((pull A false h).obj M))).obj.map t.inv.op =
      ((compare A X').obj ((pull A false h).obj M)).obj.map
        (ProEtale.overPullbackObjMkIdIso h).inv.op := by rfl
  erw [ht]
  erw [kn]
  erw [← reassoc_of% e]
  rfl

/-- Both canonical underived comparison squares commute, with the prescribed k.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Precompose the two closed-exchange composites with the twice-pulled-back
constant restriction (node step 6). The closed normalization identifies them with the
two scalar-preserving constant units. Coherence of the recorded comparison makes those
equal. Exactness preserves the cokernel, hence its epimorphism can be cancelled.
For sections, use the composite adjunctions (step 8). Their right adjoints identify
sectionwise on each etale object with evaluation on its base change. The recorded
comparison is their conjugate, so the conjugate-isomorphism unit equation makes the
two composite section maps agree after applying k. Step 7 restricts this equality to
support kernels, and their monic inclusions give the displayed equation for all M.
This argument uses neither quasi-compactness of the open complement nor finiteness
of h or X'. -/
theorem comparison_square (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    ((compare P.Coefficient X').map (exchange P.Coefficient false sq) ≫
        gamma P.Coefficient i' =
      (comparePullback P.Coefficient h).hom.app (supported P.Coefficient false i) ≫
        (pull P.Coefficient true h).map (gamma P.Coefficient i) ≫
          exchange P.Coefficient true sq) ∧
    (∀ M : Modules P.Coefficient false X,
      (sectionMap P false sq).app M ≫
          (compareSectionMap P i').app ((pull P.Coefficient false h).obj M) ≫
            (sections P.Coefficient true i').map
              ((comparePullback P.Coefficient h).hom.app M) =
        (compareSectionMap P i).app M ≫
          (sectionMap P true sq).app ((compare P.Coefficient X).obj M)) := by
  let A := P.Coefficient
  constructor
  · obtain ⟨w, ⟨hp⟩⟩ := presentation P false i
    have : Epi (restriction A false i) := Cofork.IsColimit.epi hp
    have hn : (compare A X').map ((pull A false h).map (restriction A false i)) ≫
        (comparePullback A h).hom.app (supported A false i) =
      (comparePullback A h).hom.app (constant A false X) ≫
        (pull A true h).map ((compare A X).map (restriction A false i)) :=
      (comparePullback A h).hom.naturality (restriction A false i)
    have hk : (compare A X').map (unitIso A false h).hom ≫ (compareUnit A X').hom =
        (comparePullback A h).hom.app (constant A false X) ≫
          (pull A true h).map (compareUnit A X).hom ≫ (unitIso A true h).hom := by
      apply (cancel_epi ((comparePullback A h).inv.app (constant A false X))).mp
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
        compare_constant_square A h
    apply (cancel_epi ((compare A X').map
      ((pull A false h).map (restriction A false i)))).mp
    rw [← Functor.map_comp_assoc, exchange_normalized, Functor.map_comp,
      Category.assoc, gamma_normalized]
    change _ = (compare A X').map ((pull A false h).map (restriction A false i)) ≫
      (comparePullback A h).hom.app (supported A false i) ≫
      (pull A true h).map (gamma A i) ≫ exchange A true sq
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc, gamma_normalized,
      Functor.map_comp, Category.assoc, exchange_normalized]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ restriction A true i') hk
  · intro M
    have he := (sectionMap_existsUnique P false sq).choose_spec.1
    have hp := (sectionMap_existsUnique P true sq).choose_spec.1
    have hc := (compareSectionMap_existsUnique P i).choose_spec.1
    have hc' := (compareSectionMap_existsUnique P i').choose_spec.1
    change SectionCondition A false h (sectionMap P false sq) at he
    change SectionCondition A true h (sectionMap P true sq) at hp
    change CompareSectionCondition A i (compareSectionMap P i) at hc
    change CompareSectionCondition A i' (compareSectionMap P i') at hc'
    apply (cancel_mono (kernel.ι
      (((pull A true h).obj ((compare A X).obj M)).obj.map
        (supportRestriction true i').op))).mp
    simp only [Category.assoc]
    have hn : (sections A true i').map ((comparePullback A h).hom.app M) ≫
        kernel.ι (((pull A true h).obj ((compare A X).obj M)).obj.map
          (supportRestriction true i').op) =
      kernel.ι (((compare A X').obj ((pull A false h).obj M)).obj.map
        (supportRestriction true i').op) ≫
        ((comparePullback A h).hom.app M).hom.app (op (terminal true X')) := by
      exact kernel.lift_ι _ _ _
    rw [hn]
    erw [reassoc_of% hc' ((pull A false h).obj M),
      reassoc_of% he M, hp ((compare A X).obj M)]
    rw [← Category.assoc _ (kernel.ι _), hc M]
    simp only [Category.assoc]
    rw [sigma_comparison_square]

end AlgebraicGeometry.SupportedConstantNormalization
