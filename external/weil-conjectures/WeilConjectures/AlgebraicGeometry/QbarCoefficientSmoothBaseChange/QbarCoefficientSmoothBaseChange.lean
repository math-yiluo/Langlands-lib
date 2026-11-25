/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientCompleteCoefficientCategories
public import WeilConjectures.SmoothBaseChange.ECoefficientSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.IntegralLattice.AdmissibleLattices
public import WeilConjectures.SmoothBaseChange.SbcCompletedOperations
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.Tactic.Choose
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.CategoryTheory.ScalarLocalization.FiniteStageRationalExchangeCoherence

/-! # Smooth base change with algebraically closed ℓ-adic coefficients

The presentation specifies the finite-stage exchange and tensor comparisons.
Its descent through both ambient Karoubi layers retains the canonical arrow
and independence of the finite stage and admissible lattice.
No constructible landing of the ambient direct images is included.

## Main definitions

* `IntegralComparisons`: scalar comparisons fixed by the tensor maps.
* `Presentation`: the completed composites and canonical compatible exchange.
* `Presentation.exchange`: descent through the ambient pair and Karoubi categories.

## Main statements

* `qbarCoefficientSmoothBaseChange`: invertibility and stage/lattice independence.

## References

* Stacks 099N
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem cancelMappedInverse
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} (i : X ≅ Y) {Z W : B} (p : Z ⟶ F.obj X)
    (q : Z ⟶ W) (r : W ⟶ F.obj Y) (h : HEq p (q ≫ r ≫ F.map i.inv)) :
    p ≫ F.map i.hom = q ≫ r := by
  rw [eq_of_heq h]
  simp only [Category.assoc, ← F.map_comp, i.inv_hom_id, F.map_id, Category.comp_id]

namespace AlgebraicGeometry.Scheme

namespace QbarCoefficientSmoothBaseChange

/-- The finite-stage completed pullback/direct-image composite for the square. -/
abbrev smoothLeftStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g))

/-- The finite-stage direct-image/pullback composite for the square. -/
abbrev smoothRightStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (_sq : ChosenCartesianSquare h e f g) :
    pbcAmbientCompleteKaroubiStage l Ω T E ⥤
      pbcAmbientCompleteKaroubiStage l Ω X E :=
  (Idempotents.functorExtension₂ _ _).obj
    (WeilConjectures.sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h))

/-- The canonical finite-stage smooth exchange transformation. -/
abbrev smoothExchangeStage (l : ℕ) [Fact l.Prime] (Ω : Type v)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Padic.FiniteCoefficientFields l Ω)
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) :
  smoothLeftStage l Ω E sq ⟶ smoothRightStage l Ω E sq :=
  (Idempotents.functorExtension₂ _ _).map
    (WeilConjectures.sbcRationalExchange l (pbcFiniteField.{u} l Ω E) sq)

end QbarCoefficientSmoothBaseChange

open WeilConjectures

namespace QbarCoefficientSmoothBaseChange

section Models
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U V : Scheme.{u}} (q : U ⟶ V)

/-- The right-adjoint comparison is the mate of the normalized ordinary tensor comparison. -/
@[irreducible] def pushModel :
    sbcAmbientPush l E q ≅ pbcActualDerivedPush q (pbcIntegralDatum l E) :=
  conjugateIsoEquiv
    (proEtaleRingDerivedAdjunction q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q))
    (pbcActualDerivedAdjunction q (pbcIntegralDatum l E)) (sbcOrdinaryDerivedIso l E q)

/-- The completed pullback comparison, obtained from the strict-tower/reflector comparison
`pbcActualCompletedPullback_tower` by reassociation. -/
@[irreducible] def pullModel :
    sbcPull l E q ⋙ ObjectProperty.ι (IsPbcComplete l E U) ≅
      ObjectProperty.ι (IsPbcComplete l E V) ⋙
        pbcActualCompletedPull q (pbcIntegralDatum l E) :=
  Functor.isoWhiskerLeft (ObjectProperty.ι (IsPbcComplete l E V))
      (Functor.associator (completedReductionTower V (pbcIntegralDatum l E))
        (completedTowerPullback q (pbcIntegralDatum l E))
        (completedTowerRlim (pbcIntegralDatum l E) U)).symm ≪≫
    (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) q).exists.choose
end Models

section Scalar
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)
  {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)

private theorem levelComparison_hom (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison W d n).hom =
      @AdicCoefficients.constantComparison W (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings W d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison W d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient scalar extension agrees with the embedding tensor along `E ≤ M`. -/
theorem tensorModel_eq (W : Scheme.{u}) :
    pbcAmbientScalarExtension l Ω W a =
      pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W := by
  apply congrArg pbcDerivedExtend
  apply (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
    (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W).unique
  · intro n
    unfold pbcCompletedScalarMap
    rw [(pbcCompletedScalarMap_exists l Ω W a).exists.choose_spec n]
    congr 1
    unfold pbcFiniteScalarMap
    rw [← cancel_epi (pbcLevelConstantComparison W (pbcStageDatum l Ω E) n).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [levelComparison_hom, levelComparison_hom]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  · exact (pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) W).exists.choose_spec

/-- Transport between the two identical finite-projection-normalized tensors. -/
@[irreducible] def tensorModel (W : Scheme.{u}) := eqToIso (tensorModel_eq l Ω a W)

/-- The specified scalar mate equation for an integral direct-image comparison. -/
@[irreducible] def IntegralPushNormalization (push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) U,
    HEq (push.hom.app K).hom
      ((tensorModel l Ω a V).hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) V).map
          ((pushModel l (pbcFiniteField.{u} l Ω E) q).hom.app K.obj) ≫
        (pbcScalarDirectImageIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).hom.app K.obj ≫
        (pushModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          ((pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).obj K.obj) ≫
        (sbcAmbientPush l (pbcFiniteField.{u} l Ω M) q).map
          ((tensorModel l Ω a U).inv.app K.obj))

/-- The unit-normalized tensor equation for an integral completed-pullback comparison. -/
@[irreducible] def IntegralPullNormalization (pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q) : Prop :=
  ∀ K : PbcComplete l (pbcFiniteField.{u} l Ω E) V,
    HEq (pull.hom.app K).hom
      ((tensorModel l Ω a U).hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) q).obj K).obj ≫
        (pbcEmbeddingAmbientTensor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) U).map
          ((pullModel l (pbcFiniteField.{u} l Ω E) q).hom.app K) ≫
        (pbcScalarCompletedPullIso l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω a) q).inv.app K.obj ≫
        (pbcActualCompletedPull q (pbcIntegralDatum l (pbcFiniteField.{u} l Ω M))).map
          ((tensorModel l Ω a V).inv.app K.obj) ≫
        (pullModel l (pbcFiniteField.{u} l Ω M) q).inv.app
          (⟨(pbcAmbientScalarExtension l Ω V a).obj K.obj,
            pbcAmbientCompleteTensor_preserves l Ω V a K⟩))

/-- The canonical integral comparisons, specified by the scalar mate and
unit-normalized completed tensor comparison. -/
structure IntegralComparisons where
  push : sbcPush l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω V a ≅
    pbcAmbientCompleteIntegralTransition l Ω U a ⋙
      sbcPush l (pbcFiniteField.{u} l Ω M) q
  pull : sbcPull l (pbcFiniteField.{u} l Ω E) q ⋙
      pbcAmbientCompleteIntegralTransition l Ω U a ≅
    pbcAmbientCompleteIntegralTransition l Ω V a ⋙
      sbcPull l (pbcFiniteField.{u} l Ω M) q
  push_eq : IntegralPushNormalization l Ω q a push
  pull_eq : IntegralPullNormalization l Ω q a pull

attribute [local irreducible] Functor.rightDerivedFunctor

end Scalar

section Descent
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iS : Fact (∀ x : S, IsUnit (l : S.presheaf.stalk x))]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]
  [iY : Fact (∀ x : Y, IsUnit (l : Y.presheaf.stalk x))]
  (sq : ChosenCartesianSquare h e f g)

/-- Normalization of the left rational comparison by the two integral comparisons. -/
@[irreducible] def LeftBetaNormalization
    (cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a)
    (cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a)
    (leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (leftBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPull l (pbcFiniteField.{u} l Ω E) f).obj
            ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((cf a).pull.hom.app ((sbcPush l (pbcFiniteField.{u} l Ω E) g).obj K) ≫
            (sbcPull l (pbcFiniteField.{u} l Ω M) f).map ((cg a).push.hom.app K))

/-- Normalization of the right rational comparison by the two integral comparisons. -/
@[irreducible] def RightBetaNormalization
    (ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a)
    (ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a)
    (rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)) : Prop :=
  ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M)
      (K : PbcComplete l (pbcFiniteField.{u} l Ω E) T),
    (rightBeta a).hom.app ((pbcAmbientCompleteLocalization l Ω T E).obj K) ≫
        (sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)).map
          ((pbcAmbientCompleteIntegralComparison l Ω T a).hom.app K) =
      (pbcAmbientCompleteIntegralComparison l Ω X a).hom.app
          ((sbcPush l (pbcFiniteField.{u} l Ω E) h).obj
            ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K)) ≫
        (pbcAmbientCompleteLocalization l Ω X M).map
          ((ch a).push.hom.app ((sbcPull l (pbcFiniteField.{u} l Ω E) e).obj K) ≫
            (sbcPush l (pbcFiniteField.{u} l Ω M) h).map ((ce a).pull.hom.app K))

/-- A presentation of the specified ambient exchange and its scalar descent: integral
comparisons fixed by the scalar mate and completion units, raw comparisons localizing their
composites, and stage operations given by their Karoubi extensions. -/
structure Presentation where
  cf : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω f a
  cg : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω g a
  ch : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω h a
  ce : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    IntegralComparisons l Ω e a
  leftBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalLeft l (pbcFiniteField.{u} l Ω E) (f := f) (g := g) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalLeft l (pbcFiniteField.{u} l Ω M) (f := f) (g := g)
  rightBeta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    sbcRationalRight l (pbcFiniteField.{u} l Ω E) (e := e) (h := h) ⋙
        pbcAmbientCompleteRawTransition l Ω X a ≅
      pbcAmbientCompleteRawTransition l Ω T a ⋙
        sbcRationalRight l (pbcFiniteField.{u} l Ω M) (e := e) (h := h)
  leftBeta_eq : LeftBetaNormalization l Ω cf cg leftBeta
  rightBeta_eq : RightBetaNormalization l Ω ch ce rightBeta
  F : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  G : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω T) (pbcAmbientCompleteSystem l Ω X)
  F_eq : ∀ E, F.Φ E = smoothLeftStage l Ω E sq
  G_eq : ∀ E, G.Φ E = smoothRightStage l Ω E sq
  F_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (F.β a) ((Idempotents.functorExtension₂ _ _).mapIso (leftBeta a))
  G_beta : ∀ {E M : Padic.FiniteCoefficientFields l Ω} (a : E ≤ M),
    HEq (G.β a) ((Idempotents.functorExtension₂ _ _).mapIso (rightBeta a))
  alpha : StageSystem.Morphism.Hom F G
  alpha_eq : ∀ E, HEq (alpha.τ E) (smoothExchangeStage l Ω E sq)

namespace Presentation
variable (P : Presentation l Ω sq)

/-- Extend the descended exchange to the ambient outer Karoubi envelope. -/
def ambientExchange :
    (Idempotents.functorExtension₂ _ _).obj P.F.functor ⟶
      (Idempotents.functorExtension₂ _ _).obj P.G.functor :=
  (Idempotents.functorExtension₂ _ _).map (StageSystem.Morphism.descNatTrans P.alpha)

/-- The exchange on the raw Qbar category, restricted along its inclusion
through the finite-stage and outer identity projectors. -/
def exchange :=
  Functor.whiskerLeft
    (pbcRawQbarToComplete l Ω T ⋙ pbcConstructibleCompleteQbarInclusion l Ω T)
    P.ambientExchange

attribute [local irreducible] pbcRationalInclusion
attribute [local irreducible] sbcRationalLeft sbcRationalRight sbcRationalExchange
attribute [local irreducible] ScalarLocalization.between ScalarLocalization.betweenNat
attribute [local irreducible] sbcPush sbcPull sbcExchange

end Presentation
end Descent

end QbarCoefficientSmoothBaseChange

open QbarCoefficientSmoothBaseChange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
  [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dS : Fact (∃ n : ℕ, topologicalKrullDim S ≤ n)]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  (sq : ChosenCartesianSquare h e f g)

attribute [local irreducible] pbcRationalInclusion
attribute [local irreducible] sbcRationalLeft sbcRationalRight sbcRationalExchange
attribute [local irreducible] ScalarLocalization.between ScalarLocalization.betweenNat
attribute [local irreducible] sbcPush sbcPull sbcExchange

end AlgebraicGeometry.Scheme
