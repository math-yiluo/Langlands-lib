/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionLargeSets
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Affine étale inverse-image restriction units -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Topologies 04HR, Sites 00WX and 00X1;
Étale Cohomology 09YQ (blueprint: lem-weil-pbc-affine-etale-restriction-unit).
Proof: restriction along the full affine inclusions is an equivalence for sheaves of
sets in Type (u + 1): the affine refinement and special-cocontinuity argument of
04HR is independent of the coefficient universe. The identification t induces an
isomorphism between the two right-adjoint
composites, since their evaluations are the sections at the same base-change object.
Conjugate the given affine inverse-image adjunction by the restriction equivalences.
Uniqueness of left adjoints gives an isomorphism from full-site inverse image to this
conjugate, compatible with the units. Whisker with restriction and cancel its
quasi-inverse. Evaluating the resulting unit equation at V and s gives the formula
below, with the restriction along t expressing the right-adjoint identification. -/
theorem affineEtale_inverseImage_restriction_unit
    (U : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        X.FullAffineEtale ⥤ Y.FullAffineEtale)
      (t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        U h ⋙ fullAffineEtaleInclusion Y ≅
          fullAffineEtaleInclusion X ⋙ (MorphismProperty.Over.pullback @Etale ⊤ h))
    [hu : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h],
      (U h).IsContinuous (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)]
    (L : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        Sheaf (fullAffineEtaleTopology X) (Type (u + 1)) ⥤
          Sheaf (fullAffineEtaleTopology Y) (Type (u + 1)))
      (a : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        L h ⊣ (U h).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)) :
    ∃ (e : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        etaleSetPullback h ⋙ ((fullAffineEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Y) Y.smallEtaleTopology) ≅
          ((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology) ⋙ L h),
    (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)),
      ((e h).hom.app G).hom.app (op ((U h).obj V))
          (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
            ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V.obj) s)) =
        ((a h).unit.app (((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)).hom.app (op V) s) := by
  classical
  let rho := fun S : Scheme.{u} ↦
    (fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type (u + 1))
      (fullAffineEtaleTopology S) S.smallEtaleTopology
  have hrho (S : Scheme.{u}) : (rho S).IsEquivalence :=
    fullAffineEtale_large_sets_equivalence S
  let adj := fun {X Y : Scheme.{u}} (h : Y ⟶ X) ↦
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)
  have hpb {X Y : Scheme.{u}} (h : Y ⟶ X) :
      (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
        X.smallEtaleTopology Y.smallEtaleTopology :=
    Scheme.isContinuous_overPullback @Etale @Etale le_rfl h
  have hcomp {X Y : Scheme.{u}} (h : Y ⟶ X) :
      (fullAffineEtaleInclusion X ⋙
        MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
        (fullAffineEtaleTopology X) Y.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ (fullAffineEtaleTopology X)
      X.smallEtaleTopology Y.smallEtaleTopology
  have hcompU {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] :
      (U h ⋙ fullAffineEtaleInclusion Y).IsContinuous
        (fullAffineEtaleTopology X) Y.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ (fullAffineEtaleTopology X)
      (fullAffineEtaleTopology Y) Y.smallEtaleTopology
  let beta := fun {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] ↦
    (Functor.sheafPushforwardContinuousComp (fullAffineEtaleInclusion X)
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (fullAffineEtaleTopology X) X.smallEtaleTopology Y.smallEtaleTopology) ≪≫
    (Functor.sheafPushforwardContinuousIso (t h).symm (Type (u + 1))
      (fullAffineEtaleTopology X) Y.smallEtaleTopology) ≪≫
    (Functor.sheafPushforwardContinuousComp (U h) (fullAffineEtaleInclusion Y)
      (Type (u + 1)) (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)
      Y.smallEtaleTopology).symm
  let alpha := fun {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] ↦
    ((mateEquiv (adj h) (a h)).symm (beta h).hom)
  have halpha {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] : IsIso (alpha h) :=
    isIso_inverseMate_of_equivalences (adj h) (a h) (beta h)
  refine ⟨fun h ↦ (asIso (alpha h)).symm, ?_⟩
  intro X Y h _ G V s
  have eqn := unit_mateEquiv_symm (adj h) (a h) (beta h).hom G
  have sections := congrArg (fun f ↦ f.hom.app (op V) s) eqn
  change (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
      (((adj h).unit.app G).hom.app (op V.obj) s)) =
    ((alpha h).app G).hom.app (op ((U h).obj V))
      (((a h).unit.app ((rho X).obj G)).hom.app (op V) s) at sections
  change ((asIso (alpha h)).inv.app G).hom.app (op ((U h).obj V))
      (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
        (((adj h).unit.app G).hom.app (op V.obj) s)) =
    ((a h).unit.app ((rho X).obj G)).hom.app (op V) s
  rw [sections]
  exact congrArg (fun f ↦ f.hom.app (op ((U h).obj V))
    (((a h).unit.app ((rho X).obj G)).hom.app (op V) s))
    ((asIso (alpha h)).hom_inv_id_app G)

end AlgebraicGeometry.Scheme
