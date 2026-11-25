/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.SfDiagonalKernelIntegrals
import WeilConjectures.AlgebraicGeometry.SfP1IntegralSectionComparison
import WeilConjectures.AlgebraicGeometry.SfP1IntegralTraceComparison

/-! # Comparison of ordinary and compact-support projective-line integrals

This comparison transports arbitrary supported Ext maps. It does not assert that
an integral is identity, or require that the Ext map is a Kummer class.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace projectiveLineTraceTransport

private theorem ordinary_supported_map_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (a : Bool)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ =
      projectiveLineDiagonalAlpha A S a ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
          (X := (ordinaryFinitePushforward A
            (pullback.diagonal (ProjectiveLine S ↘ S))).obj
              (ordinaryFiniteUnit A (ProjectiveLine S)))
          (Y := (ordinaryFiniteLine A N hA
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
          (SfP1Transport.supportedMap A N hA S κ) := by
  with_unfolding_all exact Eq.refl (ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ)

-- Use the derived-category instance witnesses captured by the library abbreviation.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  derivedTensorUnit rightDerivedLowerShriek

private theorem transport_supported_map
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    (F : C ⥤ D) (R : D ⥤ T) (H : C ⥤ E) (P : E ⥤ T) (b : F ⋙ R ≅ H ⋙ P)
    {U : T} {Z : D} {V W : C} {B : D} {K : E}
    (α : U ⟶ R.obj Z) (l : Z ⟶ F.obj V) (c : P.obj K ≅ U) (σ : K ⟶ H.obj V)
    (δ : V ⟶ W) (e : F.obj W ≅ B)
    (h : α ≫ R.map l ≫ b.hom.app V = c.inv ≫ P.map σ) :
    α ≫ R.map (l ≫ F.map δ ≫ e.hom) ≫
        SfP1Transport.middleComposite (F := F) (H := H) (P := P) R b e =
      c.inv ≫ P.map (σ ≫ H.map δ) := by
  unfold SfP1Transport.middleComposite
  calc
    _ = α ≫ R.map l ≫ R.map (F.map δ) ≫ b.hom.app W := by
      have hc : R.map e.hom ≫ R.map e.inv ≫ b.hom.app W = b.hom.app W := by
        rw [← R.map_comp_assoc, e.hom_inv_id, R.map_id, Category.id_comp]
      simp only [Functor.map_comp, Category.assoc, hc]
    _ = α ≫ R.map l ≫ b.hom.app V ≫ P.map (H.map δ) := by
      rw [show R.map (F.map δ) ≫ b.hom.app W =
        b.hom.app V ≫ P.map (H.map δ) from b.hom.naturality δ]
    _ = c.inv ≫ P.map σ ≫ P.map (H.map δ) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ P.map (H.map δ)) h
    _ = c.inv ≫ P.map (σ ≫ H.map δ) := by
      rw [P.map_comp]

private theorem transport_supported_map_of_eq
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    (F : C ⥤ D) (R : D ⥤ T) (H : C ⥤ E) (P : E ⥤ T) (b : F ⋙ R ≅ H ⋙ P)
    {U : T} {Z : D} {V W : C} {B : D} {K : E}
    (α : U ⟶ R.obj Z) (l : Z ⟶ F.obj V) (c : P.obj K ≅ U) (σ : K ⟶ H.obj V)
    (δ : V ⟶ W) (e : F.obj W ≅ B)
    (k : Z ⟶ B) (m : R.obj B ⟶ P.obj (H.obj W)) (s : K ⟶ H.obj W)
    (hk : k = l ≫ F.map δ ≫ e.hom)
    (hm : m = SfP1Transport.middleComposite (F := F) (H := H) (P := P) R b e)
    (hs : s = σ ≫ H.map δ)
    (h : α ≫ R.map l ≫ b.hom.app V = c.inv ≫ P.map σ) :
    α ≫ R.map k ≫ m = c.inv ≫ P.map s := by
  rw [hk, hm, hs]
  exact transport_supported_map F R H P b α l c σ δ e h

private theorem transport_composite
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V Z : D} {K L : C}
    (α : U ⟶ Z) (l : Z ⟶ V) (β : V ⟶ U) (b : V ⟶ F.obj L)
    (c : F.obj K ≅ U) (s : K ⟶ L) (t : L ⟶ K)
    (hs : α ≫ l ≫ b = c.inv ≫ F.map s)
    (ht : b ≫ F.map t ≫ c.hom = β) :
    α ≫ l ≫ β = c.inv ≫ F.map (s ≫ t) ≫ c.hom := by
  rw [← ht]
  calc
    _ = (α ≫ l ≫ b) ≫ F.map t ≫ c.hom := by simp only [Category.assoc]
    _ = (c.inv ≫ F.map s) ≫ F.map t ≫ c.hom := by rw [hs]
    _ = _ := by simp only [F.map_comp, Category.assoc]

/-- Rename a projective line over its base and compare the two compact-support
composites with the ordinary chart composites, for an arbitrary supported Ext class.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, base-change identification of the two projection traces;
sec-six-functors-basics/sk-prop-geo-p1-adjunction/lem-amb-p1-diagonal-integrals.proof.md,
exact closed image and the section comparisons.
(auxiliary; not a blueprint node).

Proof: Pull the given Ext representative along the product isomorphism induced by i.
Exact closed direct image and its derived comparison identify its source with the
pushforward of the constant complex along the diagonal. The normalized twist
comparison identifies its target with the inverse image of the shifted line along
p2. Use the proper forget-supports isomorphism to obtain the diagonalClass arrow.
Transport (d S hS).trace along i, the derived composition comparison and proper
forget-supports to obtain the trace arrow. These two arrows define D. The constant
inverse-image comparison for i, followed by the identification of the degree-zero
constant complex with the derived tensor unit, defines c.

For each projection, paste its Cartesian square with the isomorphism i and its
self-product. The defining exchange mate is preserved by this pasting: substitute
the pullback counit and use the composite-adjunction counit formula. The trace
base-change equation hbc identifies this mate followed by pullback of the trace
with the trace over ProjectiveLine S, transported along its canonical P1 chart.
For p2 the equality of the two maps to S gives exactly the extra coordinate
comparison in traceSecond. Normalization on roots and their scalar generators
makes the three twist comparisons in this pasting agree. The composite adjunction
unit for p_a Delta = id identifies the ordinary alpha with diagonalFirst or
idIsoDiagonalSnd, respectively. The proper forget-supports comparison commutes
with these exchange, composition and section maps. Naturality with respect to the
arbitrary Ext representative now gives the two displayed equalities, conjugated
by c. This is a comparison of composites only; no integral is evaluated here.
Everything is linear in the Ext representative. Neither a nonempty base nor
nonzero coefficients are required. -/
theorem sfP1IntegralTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting A N hA t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange A N hA t d)
    (S X : Scheme.{u}) (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    ∃ D : TraceDiagonalDatum A f ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧),
      ∃ c : (ordinaryFinitePullback A i.hom).obj
          (ordinaryFiniteUnit A (ProjectiveLine S)) ≅
            derivedTensorUnit (ModuleCat.{u + 1} A) X,
        ((SfDiagonalKernel.diagonalFirst A f).hom.app
            (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f)).map
            D.diagonalClass ≫ SfDiagonalKernel.traceFirst A D =
          c.inv ≫ (ordinaryFinitePullback A i.hom).map
            (ordinaryFiniteP1DiagonalSupportedMap A N hA S false κ ≫
              arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS false) ≫ c.hom) ∧
        ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
            (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
            D.diagonalClass ≫
          SfDiagonalKernel.traceSecond A D
            (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
            (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm =
          c.inv ≫ (ordinaryFinitePullback A i.hom).map
            (ordinaryFiniteP1DiagonalSupportedMap A N hA S true κ ≫
              arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS true) ≫ c.hom) := by
  refine ⟨SfP1Transport.datum A N hA t f i hi hS (d S hS).trace κ,
    SfP1Transport.constantComparison A i, ?_⟩
  generalize hD : SfP1Transport.datum A N hA t f i hi hS (d S hS).trace κ = D
  have hclass : D.diagonalClass = SfP1Transport.diagonalClass A N hA t f i hi hS κ := by
    rw [← hD]
    exact SfP1Transport.datum_diagonalClass A N hA t f i hi hS (d S hS).trace κ
  have htrace : D.trace = SfP1Transport.trace A N hA t f i hi hS (d S hS).trace := by
    rw [← hD]
    exact SfP1Transport.datum_trace A N hA t f i hi hS (d S hS).trace κ
  have hcoordinate (a : Bool) :
      SfP1Transport.diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (SfP1Transport.projection f a)).map D.diagonalClass ≫
        SfP1Transport.coordinateTrace A N hA t f i hi hS (d S hS).trace a =
      (SfP1Transport.constantComparison A i).inv ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
            arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a) ≫
        (SfP1Transport.constantComparison A i).hom := by
    have hs' : SfP1Transport.diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (SfP1Transport.projection f a)).map D.diagonalClass ≫
        SfP1Transport.middleComparison A N hA t f i hi hS a =
      (SfP1Transport.constantComparison A i).inv ≫
        (ordinaryFinitePullback A i.hom).map
          (ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ) := by
      exact transport_supported_map_of_eq
        (C := DerivedCategoryModule A
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
        (D := DerivedCategoryModule A (pullback f f))
        (E := DerivedCategoryModule A (ProjectiveLine S)) (T := DerivedCategoryModule A X)
        (V := (ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S)))
        (W := (ordinaryFiniteLine A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
        (ordinaryFinitePullback A (SfP1Transport.productMap f i hi))
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (SfP1Transport.projection f a))
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a))
        (ordinaryFinitePullback A i.hom)
        (SfP1Transport.projectionComparison A f i hi a)
        (SfP1Transport.diagonalUnit A f a) (SfP1Transport.diagonalLift A f i hi)
        (SfP1Transport.constantComparison A i) (projectiveLineDiagonalAlpha A S a)
        (SfP1Transport.supportedMap A N hA S κ)
        (SfP1Transport.coefficientComparison A N hA t f i hi hS)
        D.diagonalClass (SfP1Transport.middleComparison A N hA t f i hi hS a)
        (ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ)
        (hclass.trans (by
          with_unfolding_all
            exact Eq.refl (SfP1Transport.diagonalClass A N hA t f i hi hS κ)))
        (by
          with_unfolding_all
            exact Eq.refl (SfP1Transport.middleComparison A N hA t f i hi hS a))
        (ordinary_supported_map_eq A N hA S a κ)
        (SfP1Transport.sectionComparison A f i hi a)
    have ht := SfP1Transport.traceComparison A N hA t d hbc f i hi hS a
    have h := transport_composite
      (C := DerivedCategoryModule A (ProjectiveLine S)) (D := DerivedCategoryModule A X)
      (ordinaryFinitePullback A i.hom)
      (SfP1Transport.diagonalUnit A f a)
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (SfP1Transport.projection f a)).map D.diagonalClass)
      (SfP1Transport.coordinateTrace A N hA t f i hi hS (d S hS).trace a)
      (SfP1Transport.middleComparison A N hA t f i hi hS a)
      (SfP1Transport.constantComparison A i)
      (ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ)
      (arbitraryBaseFiniteP1DiagonalTrace A N hA t d S hS a)
      hs' ht
    exact h
  constructor
  · unfold SfDiagonalKernel.traceFirst
    rw [htrace]
    have h := hcoordinate false
    unfold SfP1Transport.diagonalUnit SfP1Transport.coordinateTrace
      SfP1Transport.projection at h
    exact h
  · unfold SfDiagonalKernel.traceSecond
    rw [htrace]
    have h := hcoordinate true
    unfold SfP1Transport.diagonalUnit SfP1Transport.coordinateTrace
      SfP1Transport.projection at h
    exact h

end AlgebraicGeometry.Etale
