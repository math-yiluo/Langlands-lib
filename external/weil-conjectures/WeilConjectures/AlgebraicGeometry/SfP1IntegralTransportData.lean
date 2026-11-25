/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
public import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryProperForgetComparison
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
public import WeilConjectures.AlgebraicGeometry.SfP1SupportedExtMapData

/-! # Explicit maps for projective-line integral transport

The self-product map, coefficient comparisons, supported class, and trace are
constructed from the canonical derived functors. No integral identity is used.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, coordinate comparisons.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfP1Transport

/-- Compose the inverse coefficient comparison with projection exchange.
Keeping this composition abstract prevents expansion of a concrete coefficient iso.
Source: the intermediate comparison in the diagonal integral transport.
(auxiliary; not a blueprint node). -/
@[irreducible]
def middleComposite
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    {F : C ⥤ D} {H : C ⥤ E} {P : E ⥤ T} (R : D ⥤ T)
    (b : F ⋙ R ≅ H ⋙ P) {W : C} {B : D} (e : F.obj W ≅ B) :
    R.obj B ⟶ P.obj (H.obj W) :=
  R.map e.inv ≫ b.hom.app W

/-- A trace transported through forget-supports and an inverse line comparison.
Source: the ordered factors of the explicit projective-line trace construction.
Keeping the categorical composition polymorphic prevents repeated normalization
of its concrete shifted coefficient objects.
(auxiliary; not a blueprint node). -/
@[irreducible]
def traceComposite
    {D E : Type*} [Category D] [Category E]
    (T T₀ : D ⥤ E) (z : T ≅ T₀) {B B' : D} (l : B ≅ B')
    {H J J' : E} (g : T₀.obj B ⟶ H) (τ : H ⟶ J) (u : J ⟶ J') :
    T.obj B' ⟶ J' :=
  z.hom.app B' ≫ T₀.map l.inv ≫ g ≫ τ ≫ u

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
variable (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)

/-- The projection selected by the same Boolean convention as the ordinary integral. -/
@[irreducible]
def projection (a : Bool) : pullback f f ⟶ X :=
  match a with
  | false => pullback.fst f f
  | true => pullback.snd f f

instance (priority := 1) projection_isProper (a : Bool) : IsProper (projection f a) := by
  cases a <;> unfold projection <;> infer_instance

/-- The self-product of the specified isomorphism over S. -/
@[irreducible]
def productMap : pullback f f ⟶
    pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) :=
  pullback.map f f (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)
    i.hom i.hom (𝟙 S) (by simpa using hi.symm) (by simpa using hi.symm)

instance (priority := 1) productMap_isIso : IsIso (productMap f i hi) := by
  unfold productMap
  infer_instance

omit [IsProper f] in
/-- The two Cartesian projection squares induced by the self-product isomorphism. -/
theorem projectionSquare (a : Bool) :
    IsPullback (productMap f i hi) (projection f a)
      (projectiveLineDiagonalProjection S a) i.hom := by
  apply IsPullback.of_horiz_isIso
  constructor
  change productMap f i hi ≫ projectiveLineDiagonalProjection S a = projection f a ≫ i.hom
  cases a <;> simp [productMap, projection, projectiveLineDiagonalProjection, pullback.map]

omit [IsProper f] in
/-- The Cartesian diagonal square induced by the self-product isomorphism. -/
theorem diagonalSquare :
    IsPullback i.hom (TraceDiagonalDatum.diagonal f)
      (pullback.diagonal (ProjectiveLine S ↘ S)) (productMap f i hi) := by
  apply IsPullback.of_horiz_isIso
  constructor
  apply pullback.hom_ext <;>
    simp [productMap, TraceDiagonalDatum.diagonal, pullback.map, Category.assoc]

instance (priority := 1) diagonal_isProper : IsProper (TraceDiagonalDatum.diagonal f) := by
  dsimp only [TraceDiagonalDatum.diagonal]
  infer_instance

instance (priority := 1) projectiveProjection_isProper (S : Scheme.{u}) (a : Bool) :
    IsProper (projectiveLineDiagonalProjection S a) := by
  cases a <;> dsimp only [projectiveLineDiagonalProjection] <;> infer_instance

/-- Proper exchange, kept as an isomorphism with explicit functor endpoints. -/
@[irreducible]
def properExchange {Y Y' Z Z' : Scheme.{u}}
    {g : Y ⟶ Z} {g' : Y' ⟶ Z'} {v : Y' ⟶ Y} {w : Z' ⟶ Z}
    [IsProper g] (sq : IsPullback v g' g w) :
    ordinaryFinitePushforward A g ⋙ ordinaryFinitePullback A w ≅
      ordinaryFinitePullback A v ⋙ ordinaryFinitePushforward A g' :=
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite sq
  asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)

/-- The constant complex is the derived tensor unit, through the sheaf unit. -/
@[irreducible]
def constantUnit (T : Scheme.{u}) :
    ordinaryFiniteUnit A T ≅ derivedTensorUnit (ModuleCat.{u + 1} A) T :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} A))).symm ≪≫
    singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T

/-- The constant-object comparison used to conjugate the two integral maps. -/
@[irreducible]
def constantComparison :
    (ordinaryFinitePullback A i.hom).obj (ordinaryFiniteUnit A (ProjectiveLine S)) ≅
      derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  ordinaryFiniteUnitPullback A i.hom ≪≫ constantUnit A X

/-- Pushforward after pullback along an isomorphism, from the inverse morphism. -/
@[irreducible]
def pushPull : ordinaryFinitePullback A i.hom ⋙ ordinaryFinitePushforward A i.hom ≅
    𝟭 (DerivedCategoryModule A (ProjectiveLine S)) :=
  have : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i.hom) :=
    preservesFiniteColimits_of_natIso (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} A) i)
  let e : ordinaryFinitePushforward A i.hom ≅ ordinaryFinitePullback A i.inv :=
    Functor.rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} A) i).symm ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) i.inv).symm
  Functor.isoWhiskerLeft _ e ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.inv i.hom
      (𝟙 (ProjectiveLine S)) (by simp)).symm ≪≫
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) _ ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) _) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Compare the pulled-back product line with the second-coordinate line. -/
@[irreducible]
def coefficientComparison (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFinitePullback A (productMap f i hi)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ≅
    (CoordinateTrace.pull A (pullback.snd f f)).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  ordinaryFiniteShiftedLinePullback A N hA t (productMap f i hi)
      (finiteP1_unitOnPullback N
        ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
          (ProjectiveLine S ↘ S)) hS) ≪≫
    (ordinaryFiniteShiftedLinePullback A N hA t (pullback.snd f f)
      (finiteP1_unitOnPullback N f hS)).symm

section

attribute [local irreducible] ordinaryFinitePushforward

/-- Transport of the supported source, before applying any Ext representative.
Source: blueprint thm-amb-p1-adjunction.proof.md, the supported diagonal morphism.
(auxiliary; not a blueprint node). -/
@[irreducible]
def diagonalLift :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (TraceDiagonalDatum.diagonal f)).obj
      (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
    (ordinaryFinitePullback A (productMap f i hi)).obj
      ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  (ordinaryProperForgetComparison A (TraceDiagonalDatum.diagonal f)).hom.app
      (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
    (ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
      (constantComparison A i).inv ≫
    (properExchange A (diagonalSquare f i hi)).inv.app
      (ordinaryFiniteUnit A (ProjectiveLine S))

/-- Projection exchange with proper forget-supports, natural in the product complex. -/
@[irreducible]
def projectionComparison (a : Bool) :
    ordinaryFinitePullback A (productMap f i hi) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a) ≅
    ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a) ⋙
      ordinaryFinitePullback A i.hom :=
  Functor.isoWhiskerLeft _ (ordinaryProperForgetComparison A (projection f a)) ≪≫
    (properExchange A (projectionSquare f i hi a)).symm

end

/-- Pull an arbitrary supported Ext representative across the diagonal square. -/
@[irreducible]
def diagonalClass (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (TraceDiagonalDatum.diagonal f)).obj
      (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
    (CoordinateTrace.pull A (pullback.snd f f)).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  diagonalLift A f i hi ≫
    (ordinaryFinitePullback A (productMap f i hi)).map
      (X := (ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)))
      (Y := (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
      (supportedMap A N hA S κ) ≫
    (coefficientComparison A N hA t f i hi hS).hom

/-- Direct-image composition and inverse-image/direct-image cancellation along i.
Source: the explicit trace construction, before the final trace arrow is inserted.
(auxiliary; not a blueprint node). -/
@[irreducible]
def presentationTrace (B : DerivedCategoryModule A (ProjectiveLine S)) :
    (ordinaryFinitePushforward A f).obj ((ordinaryFinitePullback A i.hom).obj B) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B :=
  (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi).inv.app
        ((ordinaryFinitePullback A i.hom).obj B) ≫
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
      ((pushPull A i).hom.app B)

omit [Finite A] [IsProper f] in
/-- The named comparison retains the original order of direct-image factors.
Source: the explicit trace formula and associativity of composition.
Proof: unfold the two-factor comparison and reassociate with the final arrow.
(auxiliary; not a blueprint node). -/
theorem presentationTrace_assoc
    (B : DerivedCategoryModule A (ProjectiveLine S))
    {K : DerivedCategoryModule A S}
    (τ : (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj B ⟶ K) :
    presentationTrace A f i hi B ≫ τ =
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi).inv.app
          ((ordinaryFinitePullback A i.hom).obj B) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
          ((pushPull A i).hom.app B) ≫ τ := by
  unfold presentationTrace
  exact Category.assoc _ _ _

/-- Transport the given ordinary trace through the isomorphism over the base. -/
@[irreducible]
def trace (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) S :=
  traceComposite
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (ordinaryFinitePushforward A f)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (ordinaryFiniteShiftedLinePullback A N hA t i.hom
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS))
    (presentationTrace A f i hi
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    τ (constantUnit A S).hom

/-- The concrete trace-diagonal datum transported across the specified isomorphism.
Source: the supported diagonal construction and transported trace of P1 adjunction.
(auxiliary; not a blueprint node). -/
@[irreducible]
def datum (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    TraceDiagonalDatum A f ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) :=
  { trace := trace A N hA t f i hi hS τ
    diagonalClass := diagonalClass A N hA t f i hi hS κ }

/-- The class field of the concrete datum is the constructed supported class.
Source: the explicit datum constructor.
(auxiliary; not a blueprint node). -/
theorem datum_diagonalClass (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    (datum A N hA t f i hi hS τ κ).diagonalClass =
      diagonalClass A N hA t f i hi hS κ := by
  unfold datum
  rfl

/-- The trace field of the concrete datum is the constructed transported trace.
Source: the explicit datum constructor.
(auxiliary; not a blueprint node). -/
theorem datum_trace (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    (datum A N hA t f i hi hS τ κ).trace = trace A N hA t f i hi hS τ := by
  unfold datum
  rfl

/-- The comparison at the intermediate object between class and trace. -/
@[irreducible]
def middleComparison (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj
        ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) ⟶
    (ordinaryFinitePullback A i.hom).obj (ordinaryFiniteP1DiagonalTarget A N hA S a) :=
  middleComposite
    (F := ordinaryFinitePullback A (productMap f i hi))
    (H := ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a))
    (P := ordinaryFinitePullback A i.hom)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a))
    (projectionComparison A f i hi a) (coefficientComparison A N hA t f i hi hS)

/-- The section source map for either compact-support projection. -/
@[irreducible]
def diagonalUnit (a : Bool) :
    derivedTensorUnit (ModuleCat.{u + 1} A) X ⟶
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (TraceDiagonalDatum.diagonal f)).obj (derivedTensorUnit (ModuleCat.{u + 1} A) X)) :=
  by
    cases a
    · unfold projection
      exact (SfDiagonalKernel.diagonalFirst A f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X)
    · unfold projection
      exact (TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X)

/-- The coordinate trace obtained from a fixed ordinary trace, without a class. -/
@[irreducible]
def coordinateTrace (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) (a : Bool) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj
        ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) ⟶
    derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  by
    cases a
    · unfold projection
      exact (SfDiagonalKernel.exchangeFirst A f).inv.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
        (CoordinateTrace.pull A f).map (trace A N hA t f i hi hS τ) ≫
          (leftDerivedUpperStarDerivedTensorUnitIso f).hom
    · unfold projection
      exact (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
          (SfDiagonalKernel.coordinate A f
            (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
            (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm).inv ≫
        (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
          (CoordinateTrace.pull A f).map (trace A N hA t f i hi hS τ) ≫
            (leftDerivedUpperStarDerivedTensorUnitIso f).hom

end AlgebraicGeometry.Etale.SfP1Transport
