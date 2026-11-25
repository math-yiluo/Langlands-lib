/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap

/-! # Lifting the affine closed site

The base-change functor is
`closedSiteBaseChange`; `closedSiteLift` sends an affine object with coordinate algebra C to Spec
H_A(C), with the opposite induced maps.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.AffineProEt

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Base change to the closed subscheme Spec(A/I). -/
def closedSiteBaseChange :
    (Spec (.of A)).AffineProEt ⥤ (Spec (.of (A ⧸ I))).AffineProEt :=
  CategoryTheory.MorphismProperty.Over.pullback
    (P := proAffineEtale) (Q := ⊤) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The coordinates of an affine object over Spec(A/I), as an A-algebra via A → A/I. -/
def closedSiteCoordinates (V : (Spec (.of (A ⧸ I))).AffineProEt) : CommAlgCat.{u} A :=
  @CommAlgCat.of A _ Γ(V.left, ⊤) _
    (((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop).hom.toAlgebra)

/-- Pullback of functions commutes with the structural A-algebra maps. -/
theorem closedSiteCoordinates_commutes
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) (a : A) :
    f.left.appTop.hom (algebraMap A (closedSiteCoordinates A I W) a) =
      algebraMap A (closedSiteCoordinates A I V) a := by
  have h := CategoryTheory.MorphismProperty.Over.w f
  have h' := congrArg (fun q ↦ ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom a)
    (show f.left ≫ (W.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) from by
      rw [← Category.assoc, h])
  exact h'

/-- The coordinate map reverses a morphism in the affine basis. -/
def closedSiteCoordinatesMap {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    closedSiteCoordinates A I W →ₐ[A] closedSiteCoordinates A I V :=
  { f.left.appTop.hom with commutes' := closedSiteCoordinates_commutes A I f }

/-- The spectrum of the closed lift belongs to the affine ind-etale basis over A. -/
theorem closedSiteLift_mem (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    proAffineEtale (Spec.map (CommRingCat.ofHom
      (algebraMap A (Algebra.ClosedLift A (closedSiteCoordinates A I V))))) := by
  apply proAffineEtale_Spec_iff.mpr
  -- The existing closed-lift instance already packages its filtered etale presentation.
  exact (RingHom.IndEtale.algebraMap_iff _ _).mpr inferInstance

/-- Lift an affine closed-site object by taking Spec of its closed-lift algebra. -/
def closedSiteLiftObj (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    (Spec (.of A)).AffineProEt :=
  AffineProEt.mk _ (closedSiteLift_mem A I V)

/-- Opposite closed-lift algebra maps commute with the maps to Spec A. -/
theorem closedSiteLiftMap_over
    {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    Spec.map (CommRingCat.ofHom
      (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f)).toRingHom) ≫
      (closedSiteLiftObj A I W).hom = (closedSiteLiftObj A I V).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f)).commutes a

/-- Lift a map by the opposite of the induced closed-lift algebra map. -/
def closedSiteLiftMap {V W : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) :
    closedSiteLiftObj A I V ⟶ closedSiteLiftObj A I W :=
  CategoryTheory.MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Algebra.ClosedLift.map (closedSiteCoordinatesMap A I f)).toRingHom))
    (closedSiteLiftMap_over A I f)

/-- The lift preserves identities. -/
theorem closedSiteLiftMap_id (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    closedSiteLiftMap A I (𝟙 V) = 𝟙 (closedSiteLiftObj A I V) := by
  apply CategoryTheory.MorphismProperty.Over.Hom.ext
  change Spec.map _ = 𝟙 _
  have h : closedSiteCoordinatesMap A I (𝟙 V) =
      AlgHom.id A (closedSiteCoordinates A I V) := by
    ext x
    rfl
  rw [h, Algebra.ClosedLift.map_id]
  exact Spec.map_id _

/-- The lift preserves composition. -/
theorem closedSiteLiftMap_comp
    {V W T : (Spec (.of (A ⧸ I))).AffineProEt} (f : V ⟶ W) (g : W ⟶ T) :
    closedSiteLiftMap A I (f ≫ g) = closedSiteLiftMap A I f ≫ closedSiteLiftMap A I g := by
  apply CategoryTheory.MorphismProperty.Over.Hom.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  have h : closedSiteCoordinatesMap A I (f ≫ g) =
      (closedSiteCoordinatesMap A I f).comp (closedSiteCoordinatesMap A I g) := by
    ext x
    rfl
  rw [h, Algebra.ClosedLift.map_comp, ← Spec.map_comp]
  rfl

/-- The functor v from the affine closed-site basis to the affine basis over A:
V = Spec C is sent to Spec H_A(C), and maps are the opposite induced algebra maps. -/
def closedSiteLift :
    (Spec (.of (A ⧸ I))).AffineProEt ⥤ (Spec (.of A)).AffineProEt where
  obj := closedSiteLiftObj A I
  map := closedSiteLiftMap A I
  map_id := closedSiteLiftMap_id A I
  map_comp := closedSiteLiftMap_comp A I

end AlgebraicGeometry.Scheme.AffineProEt
