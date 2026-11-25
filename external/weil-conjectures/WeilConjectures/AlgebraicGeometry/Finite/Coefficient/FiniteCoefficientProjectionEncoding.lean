/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Finite coefficient encoding of the canonical projection arrow

The assertion compares invertibility of the actual arrows without assuming either side.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Invertibility of the canonical projection morphism, with the endpoint calculations
kept inside a named proposition. Source: proper-base-change-finite, clause (3).
(blueprint: lem-sfb-finite-coefficient-projection-encoding). -/
def finiteCoefficientProjectionIsIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) : Prop :=
  IsIso ((internalProjectionContext R p).projection K M)

/-- The named projection property is exactly invertibility of the published mate. -/
theorem finiteCoefficientProjectionIsIso_iff
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) :
    finiteCoefficientProjectionIsIso R p K M ↔
      IsIso ((((derivedUpperStarLowerStarAdjunction R p).rightAdjointProjectionMap
        (leftDerivedUpperStarTensor R p)).app K).app M) := by
  unfold finiteCoefficientProjectionIsIso internalProjectionContext
    Adjunction.ProjectionContext.projection
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- Invertibility of the ordinary fixed-scalar projection, with its endpoints hidden.
Source: the ordinary right-adjoint projection construction.
(blueprint: lem-sfb-finite-coefficient-projection-encoding). -/
def ordinaryFiniteCoefficientProjectionIsIso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) : Prop :=
  IsIso ((ordinaryProjectionContext A p).projection K M)

/-- The named ordinary property is exactly invertibility of its canonical projection. -/
theorem ordinaryFiniteCoefficientProjectionIsIso_iff
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    ordinaryFiniteCoefficientProjectionIsIso A p K M ↔
      IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app K).app M) := by
  unfold ordinaryFiniteCoefficientProjectionIsIso ordinaryProjectionContext
    Adjunction.ProjectionContext.projection
  rfl

/-- The ordinary projection property is invariant under isomorphisms in both inputs. -/
theorem ordinaryFiniteCoefficientProjectionIsIso_of_iso
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    {M M' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (eK : K ≅ K') (eM : M ≅ M')
    (h : ordinaryFiniteCoefficientProjectionIsIso A p K M) :
    ordinaryFiniteCoefficientProjectionIsIso A p K' M' := by
  have hK := (ordinaryFiniteCoefficientProjectionIsIso_iff A p K M).1 h
  let τ := rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p
  let t := Functor.whiskerRight τ ((evaluation _ _).obj M)
  have h' : IsIso ((τ.app K').app M) := (NatTrans.isIso_app_iff_of_iso t eK).1 hK
  exact (ordinaryFiniteCoefficientProjectionIsIso_iff A p K' M').2
    ((NatTrans.isIso_app_iff_of_iso (τ.app K') eM).1 h')

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

attribute [local irreducible] CategoryTheory.Adjunction.rightAdjointProjectionMap
  CondensedRing.derivedUpperStarLowerStarAdjunction CondensedRing.leftDerivedUpperStarTensor
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.leftDerivedUpperStarTensorComparison

/-- Normalized coefficient encoding preserves and reflects the canonical projection property.

Source: blueprint sk-thm-sfb-proper-base-change-finite.proof.md, step 8;
lem-sf-finite-discrete-encoding-tensor-tor, tensor comparison; Stacks Tags 03D3,
08BJ, 08FZ and 0F0G, together with the adjunction mate defining projection.
(blueprint: lem-sfb-finite-coefficient-projection-encoding).

Proof:
1. Scalar restriction along the inverse isomorphism, followed by the normalized
section-action equivalence, identifies the two module tensors by their universal
property for balanced bilinear maps. It carries a pure tensor to the same pure tensor.
The comparison respects the associator and unitors.
2. Apply these maps termwise to K-flat resolutions and totalize with the usual signs.
Exact equivalences preserve and reflect acyclicity and K-flatness, giving the derived
tensor comparisons on the specified unbounded derived categories.
3. Direct image is identified by the identity on sections over each fibre product.
Its adjoint pullback comparison satisfies the unit and counit equations. On pure
tensors its tensor comparison is the comparison of step 1; step 2 gives the same
equality after deriving.
4. Transpose the image of the internal projection under the ordinary geometric
adjunction. The counit equation and tensor equation identify its transpose with the
ordinary counit tensored with the identity, after the source and target comparisons.
Injectivity of the adjunction Hom equivalence identifies the projection arrows.
The two endpoint comparison isomorphisms give an arrow isomorphism. The encoding
is an equivalence, so it preserves and reflects invertibility. Conjugation by the
endpoint isomorphisms therefore gives the stated equivalence of invertibility.
No properness, boundedness or etale origin is used in this change of presentation. -/
theorem finiteCoefficientProjectionEncoding
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj R Y))) :
    CondensedRing.finiteCoefficientProjectionIsIso R p K M ↔
      ProEtale.ordinaryFiniteCoefficientProjectionIsIso (ULift.{u + 1} A) p
        ((coefficientEncoding A e X (E X)).obj K)
        ((coefficientEncoding A e Y (E Y)).obj M) := by
  obtain ⟨s⟩ := finiteCoefficientTensorPullbackEncoding A e E p
  exact Adjunction.ProjectionContext.projection_isIso_iff
    (internalProjectionContext R p) (ordinaryProjectionContext (ULift.{u + 1} A) p) s K M

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
