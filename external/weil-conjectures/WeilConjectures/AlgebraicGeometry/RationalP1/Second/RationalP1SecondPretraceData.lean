/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientTail

/-! # Maps for the trace-free second projective-line calculation
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The specified shifted Tate comparison on the first projection. -/
@[irreducible]
def firstLineComparisonForTrace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
        (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧ := by
  letI : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  letI : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (firstProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  exact shiftedLineComparison l c (firstProjection Y)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})

/-- Cache the actual canonical monoidal structure through the fixed functor names. -/
@[irreducible]
def secondTracePullMonoidal :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).Monoidal := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle moduleObjectDerivedPullback
  exact monoidal_leftDerivedUpperStar Λ (ProjectiveLine Y ↘ Y)

/-- Cache the native derived Koszul braiding through the fixed tensor interface. -/
@[irreducible]
def secondTraceBraided : BraidedCategory (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1}) :=
    { sheafSymmetricCategory (ProjectiveLine Y) with
      toBraidedCategory := sheafBraidedCategory Ab.{u + 1} (ProjectiveLine Y) }
  exact DerivedCategory.braidedCategory' (Modules Λ (ProjectiveLine Y))

/-- The inverse unitator of the canonical monoidal derived pullback. -/
@[irreducible]
def secondTraceUnitIso :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      (𝟙_ (DerivedCategory (Modules Λ Y))) ≅
      𝟙_ (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  letI := secondTracePullMonoidal Λ Y
  exact (Functor.Monoidal.εIso
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y))).symm

/-- The tensorator of the canonical monoidal derived pullback, in the fixed interface. -/
@[irreducible]
def secondTraceTensorIso (K V : DerivedCategory (Modules Λ Y)) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K ⊗
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ≅
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj (K ⊗ V) := by
  letI := secondTracePullMonoidal Λ Y
  exact Functor.Monoidal.μIso
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)) K V

/-- The native Koszul symmetry in the fixed tensor interface. -/
@[irreducible]
def secondTraceSwap (A B : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    A ⊗ B ≅ B ⊗ A := by
  letI := secondTraceBraided Λ Y
  exact β_ A B

/-- Extract a further pulled factor from a twisted pulled object, before evaluation.
This is the tensorator, associators and native symmetry, conjugated by tensorShiftIso. -/
@[irreducible]
def secondTraceStrength (L : Modules Λ (ProjectiveLine Y))
    (K V : DerivedCategory (Modules Λ Y)) :
    (twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K) ⊗
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ≅
    (twist Λ (ProjectiveLine Y) L).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj (K ⊗ V)) :=
  let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
  let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
    ⟦(2 : ℤ)⟧
  tensorIso (tensorShiftIso Λ (ProjectiveLine Y) L (F.obj K)).symm (Iso.refl _) ≪≫
    (α_ (F.obj K) T (F.obj V)) ≪≫
    tensorIso (Iso.refl _) (secondTraceSwap Λ Y T (F.obj V)) ≪≫
    (α_ (F.obj K) (F.obj V) T).symm ≪≫
    tensorIso (secondTraceTensorIso Λ Y K V) (Iso.refl T) ≪≫
    tensorShiftIso Λ (ProjectiveLine Y) L (F.obj (K ⊗ V))

/-- The projection part of the counit, before any scalar trace is applied. -/
@[irreducible]
def counitProjectionPart (L : Modules Λ (ProjectiveLine Y))
    (K : DerivedCategory (Modules Λ Y))
    (hq : IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
        ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      ((twist Λ (ProjectiveLine Y) L).obj
        ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)) ⟶
    K ⊗ (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj L)
        ⟦(2 : ℤ)⟧) :=
  haveI := hq
  (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (tensorShiftIso Λ (ProjectiveLine Y) L _).inv ≫
    inv (projectionMap Λ (ProjectiveLine Y ↘ Y) K _)

/-- The literal trace-free equation, checked before substituting a coefficient ring.
Its sole field is an equality of the specified maps, with no additional data. -/
structure SecondPretraceEquation (L : ∀ X : Scheme.{u}, Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
        (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    (M N X : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (V : DerivedCategory (Modules Λ Y))
    (f : (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) ⟶ N)
    (x : X ⟶ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V)
    (S : M ⊗ (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj V ⟶ N)
    (J : M ⊗ X ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) : Prop where
  equation
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
    (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
      (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M))) :
    J ≫ unitTail Λ Y L e M hb hp ≫ f = (M ◁ x) ≫ S

/-- The native self-square exchange, with the fixed module-object endpoints. -/
@[irreducible]
def secondPretraceExchangeMap (M : DerivedCategory (Modules Λ (ProjectiveLine Y))) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M) ⟶
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M) := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact (condensedAmbientExchange Λ (square Y)).app M

/-- Transfer invertibility of the native exchange to its literal fixed-endpoint wrapper. -/
theorem secondPretraceExchangeMap_isIso
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M)) :
    IsIso (secondPretraceExchangeMap Λ Y M) := by
  unfold secondPretraceExchangeMap
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact hb

/-- The fixed ambient inverse is the inverse of the literal exchange wrapper. -/
theorem secondPretraceExchangeMap_inverse
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M)) :
    ambientExchangeInverse Λ (square Y) M hb =
      @inv _ _ _ _ (secondPretraceExchangeMap Λ Y M)
        (secondPretraceExchangeMap_isIso Λ Y M hb) := by
  have := hb
  have := secondPretraceExchangeMap_isIso Λ Y M hb
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  unfold ambientExchangeInverse secondPretraceExchangeMap
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact IsIso.hom_inv_id ((condensedAmbientExchange Λ (square Y)).app M)

/-- The forward scalar exchange on the shifted line, with its fixed root comparison. -/
@[irreducible]
def secondTraceExchange
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)) ⟶
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
        0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) :=
  secondPretraceExchangeMap (coefficient l c).X Y _ ≫
    (moduleObjectDerivedPushforward (coefficient l c).X
      (secondProjection Y)).map (firstLineComparisonForTrace l c k p hpl Y).hom

/-- The forward projection with the untwisted factor q*K outside the second direct image.
The first pulled Tate line is identified with the fixed line on the self-product. -/
@[irreducible]
def secondExtractProjection
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K ⊗
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
        ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
            K))) :=
  let Λ := (coefficient l c).X
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  projectionMap Λ (secondProjection Y) A _ ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      (tensorHom ((ambientPullbackComparison Λ (square Y)).hom.app K) (𝟙 _) ≫
        (tensorShiftIso Λ (diagonalSurface Y) (line l c (diagonalSurface Y)) _).hom ≫
        (pullTwistIso Λ (firstProjection Y) (line l c (ProjectiveLine Y))
          (line l c (diagonalSurface Y)) (firstLineComparisonForTrace l c k p hpl Y) A).inv)

end AlgebraicGeometry.ProEtale.RationalP1
