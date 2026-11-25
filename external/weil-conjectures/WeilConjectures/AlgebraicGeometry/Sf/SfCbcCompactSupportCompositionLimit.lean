/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import WeilConjectures.CategoryTheory.AdicSites.SmallSiteReducedCompletionUnit
import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

/-! # Normalized reconstruction of composable completed operations

All categories are the equivalent small models of the small pro-etale sites.
The model enlarges only Hom universes. Letters carry scheme maps, and both functors
are computed from those maps. Words are indexed composable chains.

## References

* Stacks Project, Tags 00VC, 00YV, 03D2, 0941, 099M, 099N, 09A5 and 0B56

## Implementation details

`SfCbcReducedUnitsInvertible` is a conclusion of the reconstruction theorem, never an
assumption of it.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- The small model, retaining every pro-etale object. -/
def sfCbcSite (T : Scheme.{t}) : AdicSites.Site.{t + 1} where
  objects := proEtaleSiteModel T
  topology := proEtaleModelTopology T

attribute [instance 2000] proEtaleModelBaseChange_isContinuous

/-- Geometric inverse image on the equivalent small models, by sheafified Kan extension. -/
abbrev sfCbcModelInverse {U V : Scheme.{t}} (u : U ⟶ V) :=
  (proEtaleModelBaseChange u).sheafPullback (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- Geometric direct image is precomposition with the transported base-change functor. -/
abbrev sfCbcModelDirect {U V : Scheme.{t}} (u : U ⟶ V) :=
  (proEtaleModelBaseChange u).sheafPushforwardContinuous (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The canonical geometric adjunction on the small models. -/
def sfCbcModelAdjunction {U V : Scheme.{t}} (u : U ⟶ V) :
    sfCbcModelInverse u ⊣ sfCbcModelDirect u :=
  Functor.sheafAdjunctionContinuous (proEtaleModelBaseChange u) (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The downward site equivalence preserves finite limits. -/
instance sfCbcModelDownLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) :=
  inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv.{t, t + 1, t + 1}
    (C := T.ProEt)).inverse)

/-- The upward site equivalence preserves finite limits. -/
instance sfCbcModelUpLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (AsSmall.up : T.ProEt ⥤ proEtaleSiteModel T) :=
  inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv.{t, t + 1, t + 1}
    (C := T.ProEt)).functor)

/-- Transported base change preserves finite limits through the two site equivalences. -/
instance sfCbcModelBaseChangeFiniteLimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (proEtaleModelBaseChange u) :=
  inferInstanceAs (PreservesFiniteLimits
    ((AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt) ⋙ proEtaleBaseChange u ⋙ AsSmall.up))

/-- Finite limits on the site model are transported from the original site. -/
instance sfCbcModelHasFiniteLimits (T : Scheme.{t}) :
    HasFiniteLimits (proEtaleSiteModel T) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
    (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse

/-- Geometric inverse image is left exact on the small models. -/
instance sfCbcModelInverseFiniteLimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (sfCbcModelInverse u) :=
  letI := flat_of_preservesFiniteLimits (proEtaleModelBaseChange u)
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (proEtaleModelBaseChange u) (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The actual geometric morphism, with the existing algebraic lift of inverse image.
Its module functors are the constant-ring inverse image and its representing right adjoint. -/
def sfCbcMorphism {U V : Scheme.{t}} (u : U ⟶ V) :
    AdicSites.Morphism (sfCbcSite V) (sfCbcSite U) :=
  letI := sfCbcModelInverseFiniteLimits u
  { inverse := sfCbcModelInverse u
    direct := sfCbcModelDirect u
    adjunction := sfCbcModelAdjunction u
    finiteLimits := sfCbcModelInverseFiniteLimits u
    algebra := Classical.choice (ConstantCompletion.inverseImageData_exists
      (sfCbcModelInverse u) (sfCbcModelDirect u) (sfCbcModelAdjunction u)) }

/-- A letter contains exactly its geometric map, with open immersions certified. -/
inductive SfCbcLetter : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | pullback {U V : Scheme.{t}} (u : U ⟶ V) : SfCbcLetter V U
  | directImage {U V : Scheme.{t}} (u : U ⟶ V) : SfCbcLetter U V
  | openExtension {U V : Scheme.{t}} (j : U ⟶ V) (hj : IsOpenImmersion j) :
      SfCbcLetter U V

/-- A finite composable chain; the indices enforce source/target matching. -/
inductive SfCbcWord : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | nil (T : Scheme.{t}) : SfCbcWord T T
  | snoc {S U V : Scheme.{t}} (W : SfCbcWord S U) (F : SfCbcLetter U V) : SfCbcWord S V

variable {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)

/-- The completed functor of a letter is computed from its map. -/
def SfCbcLetter.complete {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match F with
  | .pullback u => (sfCbcMorphism u).pull _ ⋙ (sfCbcSite T).completion _ (sfCbcModelIdeal d)
  | .directImage u => (sfCbcMorphism u).push _
  | .openExtension j hj =>
    letI := hj
    sfCbcModelDerivedExtension j A ⋙ (sfCbcSite T).completion _ (sfCbcModelIdeal d)

/-- The strict functor is termwise inverse image, derived termwise direct image,
or the exact termwise extension, according to the letter. -/
def SfCbcLetter.strict {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match F with
  | .pullback u => (sfCbcMorphism u).towerPull _
  | .directImage u => (sfCbcMorphism u).towerPush _
  | .openExtension j hj =>
    letI := hj
    sfCbcDerivedTowerExtension j A

/-- Completed word functors are recursive composites, with identity at length zero. -/
def SfCbcWord.complete {S T : Scheme.{t}} (W : SfCbcWord S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match W with
  | .nil _ => 𝟭 _
  | .snoc W F => complete W ⋙ F.complete d

/-- Strict word functors are recursive composites of the actual strict letters. -/
def SfCbcWord.strict {S T : Scheme.{t}} (W : SfCbcWord S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match W with
  | .nil _ => 𝟭 _
  | .snoc W F => strict W ⋙ F.strict (A := A)

/-- The specified reduced completion unit, before any tower evaluation. -/
def sfCbcModelReducedUnit (T : Scheme.{t}) :
    (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite T).completion _ (sfCbcModelIdeal d) ⋙
        (sfCbcSite T).reduction _ (sfCbcModelIdeal d) :=
  whiskerRight ((sfCbcSite T).unit _ (sfCbcModelIdeal d))
    ((sfCbcSite T).reduction _ (sfCbcModelIdeal d))

/-- The specified reduced unit `sfCbcModelReducedUnit d T` is an isomorphism for every
scheme `T`. -/
def SfCbcReducedUnitsInvertible : Prop := ∀ T : Scheme.{t}, IsIso (sfCbcModelReducedUnit d T)

/-- The counit-tensor projection map as one natural transformation of strict towers.
Its component is exactly AdicSites.Morphism.towerProjection. -/
def sfCbcDirectQ {U V : Scheme.{t}} (u : U ⟶ V) :
    (sfCbcMorphism u).push (ULift.{t + 1, t} A) ⋙
        (sfCbcSite V).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite U).reduction _ (sfCbcModelIdeal d) ⋙ (sfCbcMorphism u).towerPush _ :=
  whiskerLeft ((sfCbcMorphism u).push _ ⋙
      (sfCbcSite V).reduction _ (sfCbcModelIdeal d))
    ((sfCbcMorphism u).towerAdjunction _).unit ≫
  whiskerRight (whiskerLeft ((sfCbcMorphism u).push _)
    ((sfCbcMorphism u).reductionPullIso _ (sfCbcModelIdeal d)).hom)
      ((sfCbcMorphism u).towerPush _) ≫
  whiskerRight (whiskerRight ((sfCbcMorphism u).adj _).counit
    ((sfCbcSite U).reduction _ (sfCbcModelIdeal d))) ((sfCbcMorphism u).towerPush _)

/-- The three specified one-letter maps. Pullback is inverse reduced unit followed by
strict pullback/tensor comparison. Direct image is the diagram counit-tensor mate.
Open extension uses exactly the normalized tensor comparison of the extension
lemma, preceded by inverse reduced unit, hence is its q_j in the small model. -/
def SfCbcLetter.q (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    F.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ F.strict (A := A) :=
  match F with
  | .pullback u =>
    whiskerLeft ((sfCbcMorphism u).pull _)
      (@asIso _ _ _ _ (sfCbcModelReducedUnit d T) (hunit T)).inv ≫
        ((sfCbcMorphism u).reductionPullIso _ (sfCbcModelIdeal d)).inv
  | .directImage u => sfCbcDirectQ d u
  | .openExtension j hj =>
    letI := hj
    whiskerLeft (sfCbcModelDerivedExtension j A)
      (@asIso _ _ _ _ (sfCbcModelReducedUnit d T) (hunit T)).inv ≫
        (sfCbcTensorComparison_existsUnique j d).exists.choose.hom

/-- The strict comparison is recursively defined by the concatenation formula.
For the empty word it is the identity, expressed by the canonical functor unitors. -/
def SfCbcWord.q (hunit : SfCbcReducedUnitsInvertible d) :
    {S T : Scheme.{t}} → (W : SfCbcWord S T) →
    W.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ W.strict (A := A)
  | _, _, .nil _ => (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv
  | _, _, .snoc W F => whiskerLeft (W.complete d) (F.q d hunit) ≫
      whiskerRight (SfCbcWord.q hunit W) (F.strict (A := A))

/-- Reconstruction is eta followed by derived strict inverse limit of q, by definition. -/
def SfCbcWord.a (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (W : SfCbcWord S T) :
    W.complete d ⟶ (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙
      W.strict (A := A) ⋙ (sfCbcSite T).rlim (ULift.{t + 1, t} A) :=
  whiskerLeft (W.complete d) ((sfCbcSite T).unit _ (sfCbcModelIdeal d)) ≫
    whiskerRight (W.q d hunit) ((sfCbcSite T).rlim _)

/-- Concatenation appends the letters of V after those of W, with matching middle scheme. -/
def SfCbcWord.append {S U T : Scheme.{t}} (W : SfCbcWord S U)
    (V : SfCbcWord U T) : SfCbcWord S T :=
  match V with
  | .nil _ => W
  | .snoc V F => (append W V).snoc F

/-- The same canonical reassociation for the actual strict tower functors. -/
def SfCbcWord.appendStrictIso {S U T : Scheme.{t}} (W : SfCbcWord S U)
    (V : SfCbcWord U T) :
    (W.append V).strict (A := A) ≅ W.strict (A := A) ⋙ V.strict (A := A) :=
  match (generalizing := true) V with
  | .nil _ => (Functor.rightUnitor _).symm
  | .snoc V F => isoWhiskerRight (appendStrictIso W V) (F.strict (A := A)) ≪≫
      Functor.associator _ _ _

/-- A parenthesized expression in composable subwords. Every finite bracketing is included. -/
inductive SfCbcExpression : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | word {S T : Scheme.{t}} (W : SfCbcWord S T) : SfCbcExpression S T
  | comp {S U T : Scheme.{t}} (E : SfCbcExpression S U) (F : SfCbcExpression U T) :
      SfCbcExpression S T

/-- Forget the parentheses, retaining the complete composable chain. -/
def SfCbcExpression.flatten {S T : Scheme.{t}} (E : SfCbcExpression S T) : SfCbcWord S T :=
  match E with
  | .word W => W
  | .comp E F => (flatten E).append (flatten F)

/-- The completed functor with precisely the parentheses of the expression. -/
def SfCbcExpression.complete {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match E with
  | .word W => W.complete d
  | .comp E F => complete E ⋙ complete F

/-- The strict functor with the same parentheses. -/
def SfCbcExpression.strict {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match E with
  | .word W => W.strict (A := A)
  | .comp E F => strict E ⋙ strict F

/-- Reassociation from the flattened strict chain to the chosen parentheses. -/
def SfCbcExpression.strictIso {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.flatten.strict (A := A) ≅ E.strict (A := A) :=
  match (generalizing := true) E with
  | .word _ => Iso.refl _
  | .comp E F => SfCbcWord.appendStrictIso E.flatten F.flatten ≪≫
      isoWhiskerRight (strictIso E) (F.flatten.strict (A := A)) ≪≫
      isoWhiskerLeft (E.strict (A := A)) (strictIso F)

/-- The comparison obtained by composing with the chosen parentheses. -/
def SfCbcExpression.q (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ E.strict (A := A) :=
  match (generalizing := true) E with
  | .word W => W.q d hunit
  | .comp E F => whiskerLeft (E.complete d) (SfCbcExpression.q hunit F) ≫
      whiskerRight (SfCbcExpression.q hunit E) (F.strict (A := A))

/-- Reconstruction with the chosen parentheses uses the same eta then L(q) rule. -/
def SfCbcExpression.a (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.complete d ⟶ (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙
      E.strict (A := A) ⋙ (sfCbcSite T).rlim (ULift.{t + 1, t} A) :=
  whiskerLeft (E.complete d) ((sfCbcSite T).unit _ (sfCbcModelIdeal d)) ≫
    whiskerRight (E.q d hunit) ((sfCbcSite T).rlim _)

end AlgebraicGeometry.Scheme
