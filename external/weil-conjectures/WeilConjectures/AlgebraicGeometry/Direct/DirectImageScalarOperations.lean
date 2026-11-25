/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange

/-! # Constant-coefficient scalar operations

The canonical constructions used by scalar exchange and its pullback cube.
Source: Stacks Tags 03EL, 06YY, 07A6, and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The universal derived extension along the actual map of constant ring sheaves.
The defining functor carries its universal counit and K-flat tensor computation.
Source: Stacks Tag 06YY (blueprint: lem-fix-direct-image-scalar-exchange). -/
abbrev directImageScalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B :=
  Scheme.proEtaleRingDerivedExtension (Scheme.proEtaleConstantRingMap (T := T) φ)

/-- Canonical constant-coefficient derived direct image, using its normalized adjunction.
This is a specialization of the existing ordinary, uncompleted ringed direct image.
Source: Stacks Tags 07A5 and 07A6 (blueprint: lem-fix-direct-image-scalar-exchange). -/
abbrev directImageConstantPush (A : Type u) [CommRing A]
    {T V : Scheme.{u}} (f : T ⟶ V) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory V A :=
  Scheme.proEtaleRingDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The actual canonical geometric adjunction, with its constant-coefficient
functors explicit in the interface. This preserves the original normalized data.
Source: Stacks Tags 07A5 and 07A6
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageConstantAdjunction (A : Type u) [CommRing A]
    {T V : Scheme.{u}} (f : T ⟶ V) :
    Scheme.proEtaleConstantRingDerivedPullback A f ⊣ directImageConstantPush A f :=
  Scheme.proEtaleRingDerivedAdjunction f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)

/-- The canonical scalar/inverse-image isomorphism. The existing reduction/pullback
construction is the inverse mate of the exact restriction comparison, whose ordinary
map is fixed by identity on sections. Its tensor-unit normalization is the balancing
map on flat K-flat representatives, sending the pullback of x tensor b to the
pullback of x tensor b. Naturality of the constant-section comparison supplies the
coefficient square, with no extra hypothesis.
Source: Stacks Tags 03EL, 06YY and 0D6D
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageScalarPullbackIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageScalarExtension φ V ⋙ Scheme.proEtaleConstantRingDerivedPullback B f ≅
      Scheme.proEtaleConstantRingDerivedPullback A f ⋙ directImageScalarExtension φ T :=
  Scheme.proEtaleReductionPullbackIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- The direct-image scalar map chi is the mate of the specified tensor comparison,
under the canonical tensor-unit-normalized geometric adjunctions.
Source: Stacks Tag 0E47 (blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageScalarComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {T V : Scheme.{u}} (f : T ⟶ V) :
    directImageConstantPush A f ⋙ directImageScalarExtension φ V ⟶
      directImageScalarExtension φ T ⋙ directImageConstantPush B f :=
  (mateEquiv
    (directImageConstantAdjunction A f)
    (directImageConstantAdjunction B f)
    (directImageScalarPullbackIso φ f).hom)

/-- The canonical geometric pullback-square comparison with constant coefficients.
Source: Stacks Tag 0D6D (blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageConstantPullbackIso (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    Scheme.proEtaleConstantRingDerivedPullback A g ⋙
      Scheme.proEtaleConstantRingDerivedPullback A f' ≅
        Scheme.proEtaleConstantRingDerivedPullback A f ⋙
          Scheme.proEtaleConstantRingDerivedPullback A h :=
  Scheme.proEtaleAmbientRingedPullbackComparison sq
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing Y A)
    (Scheme.proEtaleConstantRing X' A) (Scheme.proEtaleConstantRing Y' A)
    (Scheme.proEtaleConstantRingComparison f A)
    (Scheme.proEtaleConstantRingComparison g A)
    (Scheme.proEtaleConstantRingComparison h A)
    (Scheme.proEtaleConstantRingComparison f' A)
    ((heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq h f A)).trans
      ((congr_arg_heq (fun q : X' ⟶ Y ↦ Scheme.proEtaleConstantRingComparison q A)
        sq.w).trans
          (heq_of_eq (Scheme.proEtaleConstantRingCompositeCoefficients_eq f' g A)).symm))

/-- The ambient ringed exchange specialized to the canonical constant rings.
Its pullback square is built from the canonical composition comparisons. The two
composite coefficient identifications are the constant comparison for the same
scheme map; the proof below supplies that compatibility, rather than assuming it.
Source: Stacks Tags 07A7, 0D6D and 0E47
(blueprint: lem-fix-direct-image-scalar-exchange). -/
def directImageConstantExchange (A : Type u) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare h f' f g) :
    directImageConstantPush A f ⋙ Scheme.proEtaleConstantRingDerivedPullback A g ⟶
      Scheme.proEtaleConstantRingDerivedPullback A h ⋙ directImageConstantPush A f' :=
  (mateEquiv
    (directImageConstantAdjunction A f)
    (directImageConstantAdjunction A f')
    (directImageConstantPullbackIso A sq).hom)

end AlgebraicGeometry.ProEtale
