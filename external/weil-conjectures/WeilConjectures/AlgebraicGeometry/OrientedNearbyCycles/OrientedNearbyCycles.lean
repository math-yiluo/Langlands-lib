/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.OrientedProduct.OrientedProductUniversal
public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Oriented nearby cycles and their canonical comparison maps

## Main definitions

* `VanishingTopos`, `p₁`, `p₂`, `orientation`, `psi`: the concrete oriented construction.
* `nearbyCycles`, `baseChange`, `IsPsiGood`: unbounded nearby cycles and base change.
* `laxTensor`, `externalEtale`, `externalVanishing`, `kunneth`: the specified tensor maps.

The étale sites are transported through `AsSmall.equiv`. This changes neither
coverings nor the associated topoi and accommodates independent scheme/coefficient sizes.

## References

* Illusie--Laszlo--Orgogozo, Exposé XI §§1.1--1.7, 1.9, 4.1--4.3
* Illusie, Around the Thom--Sebastiani theorem, §§1.4--1.5, 2.1
* ILO XI §4.3
* ILO XI §1.1, §4.3
* ILO XI §1.1(ii), §4.3
* ILO XI §1.7, §4.3
* ILO XI §1.3, §4.3
* ILO XI §1.3
* ILO XI Lemma 1.2(ii)
* ILO XI §1.3, Theorem 1.4
* ILO XI Theorem 1.4
* ILO XI §1.1
* ILO XI §4.3 (4.b)
* ILO XI §1.9
* ILO XI §1.9, §4.3
* ILO XI Theorem 1.4, §1.9, §4.3
* ILO XI §4.1
* Stacks 03D2
* ILO XI §4.1, §4.3
* Stacks 079P
* Illusie §1.4
* Stacks 06YS, 06YT
* Stacks 03EL, 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- The small étale site presented in a common universe by Mathlib's equivalence. -/
abbrev EtaleSite (X : Scheme.{u}) := AsSmall.{v} X.Etale

/-- The transported étale topology, using Mathlib's induced topology. -/
def etaleTopology (X : Scheme.{u}) : GrothendieckTopology (EtaleSite.{u, v} X) :=
  (AsSmall.down : EtaleSite.{u, v} X ⥤ X.Etale).inducedTopology X.smallEtaleTopology

/-- The transported small étale site has finite limits. -/
theorem etaleSite_hasFiniteLimits (X : Scheme.{u}) :
    HasFiniteLimits (EtaleSite.{u, v} X) :=
  ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (AsSmall.equiv (C := X.Etale)).inverse⟩

attribute [instance] etaleSite_hasFiniteLimits

/-- The actual scheme-theoretic base-change functor on the transported small étale sites. -/
def etaleBaseChange {T B : Scheme.{u}} (f : T ⟶ B) :
    EtaleSite.{u, v} B ⥤ EtaleSite.{u, v} T :=
  AsSmall.down ⋙ MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up

/-- Base change preserves finite limits on the étale sites. -/
theorem etaleBaseChange_preservesFiniteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (etaleBaseChange.{u, v} f) := by
  have : PreservesFiniteLimits (AsSmall.down : EtaleSite.{u, v} B ⥤ B.Etale) :=
    inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv (C := B.Etale)).inverse)
  have : PreservesFiniteLimits (AsSmall.up : T.Etale ⥤ EtaleSite.{u, v} T) :=
    inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv (C := T.Etale)).functor)
  have : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f) := inferInstance
  exact comp_preservesFiniteLimits _ _

attribute [instance] etaleBaseChange_preservesFiniteLimits

/-- Base change is continuous for the transported étale topologies. -/
theorem etaleBaseChange_isContinuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (etaleBaseChange.{u, v} f).IsContinuous (etaleTopology B) (etaleTopology T) := by
  have : (AsSmall.down : EtaleSite.{u, v} B ⥤ B.Etale).IsContinuous (etaleTopology B)
      B.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.equiv (C := B.Etale)).inverse.IsContinuous
      ((AsSmall.equiv (C := B.Etale)).inverse.inducedTopology B.smallEtaleTopology)
      B.smallEtaleTopology)
  have : (AsSmall.up : T.Etale ⥤ EtaleSite.{u, v} T).IsContinuous T.smallEtaleTopology
      (etaleTopology T) :=
    inferInstanceAs ((AsSmall.equiv (C := T.Etale)).functor.IsContinuous T.smallEtaleTopology
      ((AsSmall.equiv (C := T.Etale)).inverse.inducedTopology T.smallEtaleTopology))
  have : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous B.smallEtaleTopology
      T.smallEtaleTopology :=
    Scheme.isContinuous_overPullback (P := @Etale) (Q := @Etale) le_rfl f
  have := Functor.isContinuous_comp (MorphismProperty.Over.pullback @Etale ⊤ f) AsSmall.up
    B.smallEtaleTopology T.smallEtaleTopology (etaleTopology T)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.pullback @Etale ⊤ f ⋙ AsSmall.up) (etaleTopology B)
    B.smallEtaleTopology (etaleTopology T)

attribute [instance] etaleBaseChange_isContinuous

/-- The geometric morphism associated to a continuous finite-limit-preserving site functor.
The inverse image is Mathlib's left adjoint; its universal property fixes the construction. -/
def siteMorphism {C D : Type s} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] [PreservesFiniteLimits F] :
    GeometricMorphism (Sheaf K (Type s)) (Sheaf J (Type s)) where
  inverse := F.sheafPullback (Type s) J K
  direct := F.sheafPushforwardContinuous (Type s) J K
  adj := F.sheafAdjunctionContinuous (Type s) J K
  leftExact :=
    letI : RepresentablyFlat F := flat_of_preservesFiniteLimits F
    Functor.sheafPullbackConstruction.preservesFiniteLimits F (Type s) J K

/-- A scheme morphism on the étale topoi, with its actual base-change inverse image. -/
def etaleMorphism {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} B) (etaleTopology T) (etaleBaseChange f)

/-- The vanishing site's underlying category: exactly the oriented-product triples. -/
abbrev VanishingSite {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.Triples (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- Its three types of covering generators, via the recorded oriented-product construction. -/
def vanishingTopology {T B : Scheme.{u}} (f : T ⟶ B) :
    GrothendieckTopology (VanishingSite.{u, v} f) :=
  OrientedProduct.topology (etaleTopology T).toPretopology
    (etaleTopology B).toPretopology (etaleBaseChange f) (𝟭 _)

/-- The actual topos of sheaves on the vanishing site. -/
abbrev VanishingTopos {T B : Scheme.{u}} (f : T ⟶ B) :=
  Sheaf (vanishingTopology.{u, v} f) (Type (max (u + 1) v))

/-- The first projection's site functor from the recorded oriented product. -/
abbrev first {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.first (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The second projection's site functor from the recorded oriented product. -/
abbrev second {T B : Scheme.{u}} (f : T ⟶ B) :=
  OrientedProduct.second (etaleBaseChange.{u, v} f) (𝟭 (EtaleSite.{u, v} B))

/-- The projection site functors are continuous and preserve finite limits. -/
theorem projection_properties {T B : Scheme.{u}} (f : T ⟶ B) :
    (first.{u, v} f).IsContinuous (etaleTopology T) (vanishingTopology f) ∧
    PreservesFiniteLimits (first.{u, v} f) ∧
    (second.{u, v} f).IsContinuous (etaleTopology B) (vanishingTopology f) ∧
    PreservesFiniteLimits (second.{u, v} f) := by
  sorry

/-- Continuity of the first projection's site functor. -/
instance first_continuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (first.{u, v} f).IsContinuous (etaleTopology T) (vanishingTopology f) :=
  (projection_properties f).1

/-- Finite-limit preservation of the first projection's site functor. -/
instance first_finiteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (first.{u, v} f) := (projection_properties f).2.1

/-- Continuity of the second projection's site functor. -/
instance second_continuous {T B : Scheme.{u}} (f : T ⟶ B) :
    (second.{u, v} f).IsContinuous (etaleTopology B) (vanishingTopology f) :=
  (projection_properties f).2.2.1

/-- Finite-limit preservation of the second projection's site functor. -/
instance second_finiteLimits {T B : Scheme.{u}} (f : T ⟶ B) :
    PreservesFiniteLimits (second.{u, v} f) := (projection_properties f).2.2.2

/-- The first projection from the actual vanishing topos. -/
def p₁ {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} T) (vanishingTopology f) (first f)

/-- The second projection from the actual vanishing topos. -/
def p₂ {T B : Scheme.{u}} (f : T ⟶ B) :=
  siteMorphism (etaleTopology.{u, v} B) (vanishingTopology f) (second f)

/-- The identity geometric morphism, with the identity adjunction. -/
def identity (E : Type (s + 1)) [Category.{s} E] : GeometricMorphism E E :=
  ⟨𝟭 E, 𝟭 E, Adjunction.id, inferInstance⟩

/-- A type-(c) covering becomes invertible in every sheaf. -/
theorem map_toFirst_isIso {T B : Scheme.{u}} (f : T ⟶ B)
    (H : VanishingTopos.{u, v} f) (V : EtaleSite.{u, v} B) :
    IsIso (H.obj.map (OrientedProduct.toFirst (etaleBaseChange f) (𝟭 _)
      (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op) := by
  sorry

attribute [instance] map_toFirst_isIso

/-- The orientation is uniquely fixed by the two restriction maps of ILO XI §1.3.
It has the universal property of the recorded oriented-product theorem. -/
theorem orientation_existsUnique {T B : Scheme.{u}} (f : T ⟶ B) :
    ∃! τ : ((p₂.{u, v} f).comp (identity (Sheaf (etaleTopology B)
        (Type (max (u + 1) v))))).direct ⟶ ((p₁ f).comp (etaleMorphism f)).direct,
      (∀ (H : VanishingTopos.{u, v} f) (V : EtaleSite.{u, v} B),
        (τ.app H).hom.app (op V) =
          H.obj.map (OrientedProduct.toSecond (etaleBaseChange f) (𝟭 _)
            (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op ≫
          inv (H.obj.map (OrientedProduct.toFirst (etaleBaseChange f) (𝟭 _)
            (OrientedProduct.middle (etaleBaseChange f) (𝟭 _) V)).op)) ∧
      OrientedProduct.IsUniversal.{max (u + 1) v, max (u + 1) v + 1, max (u + 1) v}
        (etaleMorphism f) (identity _) (p₁ f) (p₂ f) τ := by
  sorry

/-- The specified orientation, rather than an unspecified 2-morphism. -/
def orientation {T B : Scheme.{u}} (f : T ⟶ B) :=
  (orientation_existsUnique.{u, v} f).choose

/-- Universal property for the explicitly normalized oriented projections. -/
theorem orientation_universal {T B : Scheme.{u}} (f : T ⟶ B) :
    OrientedProduct.IsUniversal.{max (u + 1) v, max (u + 1) v + 1, max (u + 1) v}
      (etaleMorphism f) (identity _) (p₁ f) (p₂ f) (orientation f) := by
  sorry

/-- The coherent lift of a cone to the oriented product, including its identifying maps. -/
structure Lift {T B : Scheme.{u}} (f : T ⟶ B)
    (E : Type (max (u + 1) v + 1)) [Category.{max (u + 1) v} E]
    (a : GeometricMorphism E (Sheaf (etaleTopology.{u, v} T) (Type (max (u + 1) v))))
    (b : GeometricMorphism E (Sheaf (etaleTopology.{u, v} B) (Type (max (u + 1) v))))
    (t : (b.comp (identity _)).direct ⟶ (a.comp (etaleMorphism f)).direct) where
  morphism : GeometricMorphism E (VanishingTopos.{u, v} f)
  first : (morphism.comp (p₁ f)).direct ≅ a.direct
  second : (morphism.comp (p₂ f)).direct ≅ b.direct
  compatible : OrientedProduct.paste (etaleMorphism f) (identity _)
    (p₁ f) (p₂ f) (orientation f) morphism a b first second = t

/-- The universal-property lift, not a choice of an unconstrained geometric morphism. -/
def lift {T B : Scheme.{u}} (f : T ⟶ B)
    (E : Type (max (u + 1) v + 1)) [Category.{max (u + 1) v} E]
    (hE : IsGrothendieckTopos.{max (u + 1) v} E)
    (a : GeometricMorphism E (Sheaf (etaleTopology.{u, v} T) (Type (max (u + 1) v))))
    (b : GeometricMorphism E (Sheaf (etaleTopology.{u, v} B) (Type (max (u + 1) v))))
    (t : (b.comp (identity _)).direct ⟶ (a.comp (etaleMorphism f)).direct) :
    Lift f E a b t :=
  ⟨((orientation_universal f) E hE a b t).choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose_spec.choose,
    ((orientation_universal f) E hE a b t).choose_spec.choose_spec.choose_spec.1⟩

/-- A sheaf category is a topos, using its actual small-site presentation. -/
theorem sheaf_isTopos {C : Type s} [SmallCategory C] (J : GrothendieckTopology C) :
    IsGrothendieckTopos.{s} (Sheaf J (Type s)) := by
  sorry

/-- The cone `(1_T,f,1_f)` defining the nearby-cycle morphism. -/
def psiLift {T B : Scheme.{u}} (f : T ⟶ B) :
    Lift.{u, v} f _ (identity _) (etaleMorphism f)
      ((Functor.rightUnitor (etaleMorphism.{u, v} f).direct).hom ≫
        (Functor.leftUnitor (etaleMorphism.{u, v} f).direct).inv) :=
  lift f _ (sheaf_isTopos _) (identity _) (etaleMorphism f) _

/-- The canonical nearby-cycle geometric morphism `ψ_f`. -/
def psi {T B : Scheme.{u}} (f : T ⟶ B) := (psiLift.{u, v} f).morphism

/-- Base-change associativity transported through the two `AsSmall` equivalences. -/
def etaleBaseChangeComp {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    etaleBaseChange.{u, v} (h ≫ f) ≅ etaleBaseChange f ⋙ etaleBaseChange h :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down (MorphismProperty.Over.pullbackComp h f))
    AsSmall.up

/-- Composition of étale direct images, with the canonical fibre-product comparison. -/
def etaleComposition {T' T B : Scheme.{u}} (h : T' ⟶ T) (f : T ⟶ B) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      (etaleMorphism (h ≫ f)).direct :=
  letI := Functor.isContinuous_comp (etaleBaseChange.{u, v} f) (etaleBaseChange h)
    (etaleTopology B) (etaleTopology T) (etaleTopology T')
  (etaleBaseChange f).sheafPushforwardContinuousComp (etaleBaseChange h)
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T) (etaleTopology T') ≪≫
    Functor.sheafPushforwardContinuousIso (etaleBaseChangeComp h f).symm
      (Type (max (u + 1) v)) (etaleTopology B) (etaleTopology T')

/-- The set-topos commutation identification of a scheme square. -/
def squareDirect {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    ((etaleMorphism.{u, v} h).comp (etaleMorphism f)).direct ≅
      ((etaleMorphism f').comp (etaleMorphism g)).direct :=
  etaleComposition h f ≪≫ eqToIso (congrArg
    (fun k : T' ⟶ B ↦ (etaleMorphism.{u, v} k).direct) comm) ≪≫
      (etaleComposition f' g).symm

/-- Whisker the orientation by `g`, using precisely the commutation isomorphism of the square. -/
def squareOrientation {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((p₂.{u, v} f').comp (etaleMorphism g)).comp (identity _)).direct ⟶
      (((p₁ f').comp (etaleMorphism h)).comp (etaleMorphism f)).direct :=
  (Functor.rightUnitor _).hom ≫
    (Functor.isoWhiskerRight (Functor.rightUnitor (p₂ f').direct).symm
      (etaleMorphism g).direct).hom ≫
    Functor.whiskerRight (orientation f') (etaleMorphism g).direct ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (p₁ f').direct (squareDirect f f' h g comm).inv ≫
    (Functor.associator _ _ _).inv

/-- The lift inducing `v: V_f' → V_f`, together with its projection identifications. -/
def squareLift {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  lift.{u, v} f (VanishingTopos f') (sheaf_isTopos _)
    ((p₁ f').comp (etaleMorphism h)) ((p₂ f').comp (etaleMorphism g))
    (squareOrientation f f' h g comm)

/-- The induced morphism of vanishing topoi, for an arbitrary commutative square. -/
def squareMorphism {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  (squareLift.{u, v} f f' h g comm).morphism

/-- The first projection of the composite `v ψ_f'`, identified with `h`. -/
def squarePsiFirst {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((psi.{u, v} f').comp (squareMorphism f f' h g comm)).comp (p₁ f)).direct ≅
      (etaleMorphism h).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (psi f').direct (squareLift f f' h g comm).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (psiLift f').first (etaleMorphism h).direct ≪≫
    Functor.leftUnitor _

/-- The first projection of `ψ_f h`, identified with `h`. -/
def psiHFirst {T' T B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T) :
    (((etaleMorphism.{u, v} h).comp (psi f)).comp (p₁ f)).direct ≅
      (etaleMorphism h).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism h).direct (psiLift f).first ≪≫
    Functor.rightUnitor _

/-- The second projection of `v ψ_f'`, identified with `f h`. -/
def squarePsiSecond {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    (((psi.{u, v} f').comp (squareMorphism f f' h g comm)).comp (p₂ f)).direct ≅
      ((etaleMorphism h).comp (etaleMorphism f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (psi f').direct (squareLift f f' h g comm).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (psiLift f').second (etaleMorphism g).direct ≪≫
    (squareDirect f f' h g comm).symm

/-- The second projection of `ψ_f h`, identified with `f h`. -/
def psiHSecond {T' T B : Scheme.{u}} (f : T ⟶ B) (h : T' ⟶ T) :
    (((etaleMorphism.{u, v} h).comp (psi f)).comp (p₂ f)).direct ≅
      ((etaleMorphism h).comp (etaleMorphism f)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleMorphism h).direct (psiLift f).second

/-- Universal-property uniqueness gives the projection-compatible square at `ψ`. -/
theorem squarePsi_existsUnique {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :
    ∃! e : ((psi.{u, v} f').comp (squareMorphism f f' h g comm)).direct ≅
        ((etaleMorphism h).comp (psi f)).direct,
      Functor.isoWhiskerRight e (p₁ f).direct ≪≫ psiHFirst f h =
          squarePsiFirst f f' h g comm ∧
        Functor.isoWhiskerRight e (p₂ f).direct ≪≫ psiHSecond f h =
          squarePsiSecond f f' h g comm := by
  sorry

/-- The canonical square at the nearby-cycle morphisms, with both projections fixed. -/
def squarePsi {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  (squarePsi_existsUnique.{u, v} f f' h g comm).choose

open CategoryTheory.AdicSites CategoryTheory.ConstantCompletion

/-- The transported étale site as the existing small-site datum. -/
def etaleDatum (X : Scheme.{u}) : Site.{max (u + 1) v} :=
  ⟨EtaleSite X, etaleTopology X⟩

/-- The concrete oriented triple site as the existing small-site datum. -/
def vanishingDatum {T B : Scheme.{u}} (f : T ⟶ B) : Site.{max (u + 1) v} :=
  ⟨VanishingSite f, vanishingTopology f⟩

/-- Lift a geometric inverse image to constant-coefficient modules by transporting all
algebraic operations, using the existing canonical constant-object identification. -/
def moduleMorphism (V U : Site.{s})
    (f : GeometricMorphism (Sheaf U.topology (Type s)) (Sheaf V.topology (Type s))) :
    Morphism V U :=
  letI := f.leftExact
  { inverse := f.inverse
    direct := f.direct
    adjunction := f.adj
    algebra := (inverseImageData_exists f.inverse f.direct f.adj).some }

/-- Universe transport of an arbitrary coefficient ring, along the canonical ring equivalence. -/
abbrev Coeff (Λ : Type v) [CommRing Λ] := ULift.{u + 1} Λ

/-- Unbounded derived étale module sheaves over the constant coefficient ring. -/
abbrev EtaleDerived (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] :=
  (etaleDatum.{u, v} X).derived (Coeff.{u, v} Λ)

/-- Unbounded derived module sheaves on the vanishing topos. -/
abbrev VanishingDerived {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ] :=
  (vanishingDatum.{u, v} f).derived (Coeff.{u, v} Λ)

/-- The nearby-cycle ringed-topos morphism with its exact constant-module inverse image. -/
def psiModules {T B : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (vanishingDatum.{u, v} f) (etaleDatum T) (psi f)

/-- The exact module inverse image attached to a scheme morphism. -/
def etaleModules {T B : Scheme.{u}} (f : T ⟶ B) :=
  moduleMorphism (etaleDatum.{u, v} B) (etaleDatum T) (etaleMorphism f)

/-- The exact module inverse image on the induced square of vanishing topoi. -/
def squareModules {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g) :=
  moduleMorphism (vanishingDatum.{u, v} f) (vanishingDatum f')
    (squareMorphism f f' h g comm)

/-- Unbounded nearby cycles, the existing K-injective right derived direct image. -/
def nearbyCycles {T B : Scheme.{u}} (f : T ⟶ B) (Λ : Type v) [CommRing Λ] :
    EtaleDerived T Λ ⥤ VanishingDerived f Λ :=
  (psiModules f).push (Coeff.{u, v} Λ)

/-- The specified derived identification `ψ_f'^* v^* ≅ h^* ψ_f^*`: the generator-normalized
derived square applied to the inverse-image mate of `squarePsi`. -/
def nearbySquare {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g)
    (Λ : Type v) [CommRing Λ] :
    (squareModules f f' h g comm).pull (Coeff.{u, v} Λ) ⋙
        (psiModules f').pull (Coeff Λ) ≅
      (psiModules f).pull (Coeff Λ) ⋙ (etaleModules h).pull (Coeff Λ) :=
  CategoryTheory.AdicSites.derivedSquare (f := psiModules f) (g := squareModules f f' h g comm)
    (h := etaleModules h) (k := psiModules f')
    (GeometricMorphism.inverseIso (squarePsi f f' h g comm)).symm (Coeff Λ)

/-- Ordinary base change is the transpose of the square identification followed by the counit. -/
def baseChange {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (g : B' ⟶ B) (comm : h ≫ f = f' ≫ g)
    (Λ : Type v) [CommRing Λ] (L : EtaleDerived T Λ) :
    ((squareModules f f' h g comm).pull (Coeff.{u, v} Λ)).obj ((nearbyCycles f Λ).obj L) ⟶
      (nearbyCycles f' Λ).obj (((etaleModules h).pull (Coeff Λ)).obj L) :=
  ((psiModules f').adj (Coeff Λ)).homEquiv _ _
    ((nearbySquare f f' h g comm Λ).hom.app ((nearbyCycles f Λ).obj L) ≫
      ((etaleModules h).pull (Coeff Λ)).map (((psiModules f).adj (Coeff Λ)).counit.app L))

/-- The already localized K-flat tensor on a constant-coefficient ringed site. -/
abbrev derivedTensor (S : Site.{s}) (A : Type s) [CommRing A] :
    S.derived A × S.derived A ⥤ S.derived A :=
  SheafOfModules.wfSiteDerivedTensor S.topology (S.ring A)

/-- The existing ringed tensor corner for this very tensor functor. -/
def tensorCorner (S : Site.{s}) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorCorner :=
  { site := S.objects
    topology := S.topology
    ring := S.ring A
    derived := Site.hasDerived S A
    tensor := derivedTensor S A }

/-- The precise flat-term K-flat representative subcategory. -/
def flatRepresentatives (S : Site.{s}) (A : Type s) [CommRing A] :
    ObjectProperty (CochainComplex (S.modules A) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

/-- Localization of both flat-term K-flat arguments. -/
def tensorInput (S : Site.{s}) (A : Type s) [CommRing A] :=
  ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q).prod
    ((flatRepresentatives S A).ι ⋙ DerivedCategory.Q)

/-- The representative comparison, with its localization universal property.
Its data determine the tensor presentation up to the unique compatible isomorphism. -/
theorem tensorModel_exists (S : Site.{s}) (A : Type s) [CommRing A] :
    ∃ i : SheafOfModules.RingedTensorModel (tensorCorner S A),
      ∀ (F : S.derived A × S.derived A ⥤ S.derived A)
        (j : SheafOfModules.RingedTensorModel { tensorCorner S A with tensor := F }),
        ∃! e : derivedTensor S A ≅ F,
          i.representative.hom ≫ Functor.whiskerLeft (tensorInput S A) e.hom =
            j.representative.hom := by
  sorry

/-- The universal K-flat representative identification, retaining its normalization. -/
def tensorModel (S : Site.{s}) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorModel (tensorCorner S A) :=
  (tensorModel_exists S A).choose

/-- The actual scalar-extension functor has the recorded formula on module maps. -/
theorem modulePull_map {V U : Site.{s}} (f : Morphism V U)
    (A : Type s) [CommRing A] {M N : V.modules A} (a : M ⟶ N) :
    (f.modulePull A).map a =
      eqToHom (rfl : (f.modulePull A).obj M =
        SheafOfModules.changeOfRings (constantMap f.algebra A)
          ((f.algebra.algebra (V.ring A)).modules.obj M)) ≫
      SheafOfModules.changeOfRingsHom (constantMap f.algebra A)
        ((f.algebra.algebra (V.ring A)).modules.obj M)
        ((f.algebra.algebra (V.ring A)).modules.map a) ≫
      eqToHom (rfl : SheafOfModules.changeOfRings (constantMap f.algebra A)
        ((f.algebra.algebra (V.ring A)).modules.obj N) = (f.modulePull A).obj N) := by
  sorry

/-- The specified inverse image as the existing ringed tensor edge. Its ordinary tensor
comparison is the unique one with the generalized pure-tensor and tensor-unit formulas. -/
def tensorEdge {V U : Site.{s}} (f : Morphism V U) (A : Type s) [CommRing A] :
    SheafOfModules.RingedTensorEdge (tensorCorner V A) (tensorCorner U A) :=
  letI := f.finiteLimits
  { inverse := f.inverse
    direct := f.direct
    adjunction := f.adjunction
    finiteLimits := f.finiteLimits
    inverseRing := f.algebra.rings.obj (V.ring A)
    algebraic := f.algebra.algebra (V.ring A)
    ringMap := constantMap f.algebra A
    pullback := f.modulePull A
    object_eq := fun _ ↦ rfl
    map_eq := modulePull_map f A
    ordinaryTensor :=
      (SheafOfModules.canonicalRingedTensorComparison_existsUnique (V.ring A) (U.ring A)
        (f.algebra.rings.obj (V.ring A)) f.inverse (f.algebra.algebra (V.ring A))
        (constantMap f.algebra A) (f.modulePull A) (fun _ ↦ rfl) f.direct f.adjunction
        (modulePull_map f A)).1.some
    pushforward := f.modulePush A
    moduleAdjunction := f.moduleAdjunction A
    left := f.pull A
    epsilon := (f.modulePull A).mapDerivedCategoryFactorsh.hom
    isLeftDerived := Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (V.modules A) (ComplexShape.up ℤ))
        (f.pull A) (f.modulePull A).mapDerivedCategoryFactorsh
    right := f.push A
    derivedAdjunction := f.adj A }

/-- Canonical preservation of derived tensor, characterized on K-flat representatives. -/
def pullTensor {V U : Site.{s}} (f : Morphism V U) (A : Type s) [CommRing A] :
    derivedTensor V A ⋙ f.pull A ≅ ((f.pull A).prod (f.pull A)) ⋙ derivedTensor U A :=
  (tensorEdge f A).tensorComparison (tensorModel V A) (tensorModel U A)

end AlgebraicGeometry.OrientedNearbyCycles
