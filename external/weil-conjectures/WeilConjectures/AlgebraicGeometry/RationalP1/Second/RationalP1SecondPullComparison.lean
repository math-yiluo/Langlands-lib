/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback

/-! # The canonical comparison between the two pullbacks of a twisted base object
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

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The square comparison through the fixed module-object functor names. -/
@[irreducible]
def ambientPullbackComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f' ≅
      moduleObjectDerivedPullback Λ f ⋙ moduleObjectDerivedPullback Λ g' := by
  unfold moduleObjectDerivedPullback
  exact condensedAmbientPullbackComparison Λ sq

/-- The diagram's second direct image identified with the fixed module-object functor. -/
@[irreducible]
def secondDiagramPushIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.R₂.R ≅ moduleObjectDerivedPushforward Λ (secondProjection Y) := by
  unfold moduleObjectDerivedPushforward secondProjection
  exact eqToIso d.p₂_canonical

/-- Pullback commutes with the specified twist, using its native tensor and shift maps. -/
@[irreducible]
def pullTwistIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (LS : Modules Λ S) (LX : Modules Λ X)
    (e : (moduleObjectDerivedPullback Λ f).obj
      (((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj LX) ⟦(2 : ℤ)⟧)
    (A : DerivedCategory (Modules Λ S)) :
    (moduleObjectDerivedPullback Λ f).obj ((twist Λ S LS).obj A) ≅
      (twist Λ X LX).obj ((moduleObjectDerivedPullback Λ f).obj A) := by
  let F := moduleObjectDerivedPullback Λ f
  let T := ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj LS) ⟦(2 : ℤ)⟧
  refine F.mapIso (tensorShiftIso Λ S LS A).symm ≪≫ ?_ ≪≫
    tensorIso (Iso.refl (F.obj A)) e ≪≫ tensorShiftIso Λ X LX (F.obj A)
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
  exact ((traceTensorComparison Λ f).app A).app T

-- The comparisons cross the fixed native and bundled derived tensor interfaces.
/-- The comparison p1*M ≅ p2*M for M=q*K(1)[2], with no freely chosen map data. -/
@[irreducible]
def secondPullComparison
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    (moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ≅
    (moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y)).obj
      ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) := by
  let Λ := (coefficient l c).X
  letI : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      ((ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  letI : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residueIsUnit l k p hpl _
      (secondProjection Y ≫ (ProjectiveLine Y ↘ Y) ≫ (Y ↘ Spec (.of k))) x).invertible
  let a := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let b : (moduleObjectDerivedPullback Λ (firstProjection Y)).obj a ≅
      (moduleObjectDerivedPullback Λ (secondProjection Y)).obj a := by
    exact (ambientPullbackComparison Λ (square Y)).symm.app K
  exact pullTwistIso Λ (firstProjection Y) _ _
      (shiftedLineComparison l c (firstProjection Y)) a ≪≫
    (twist Λ (diagonalSurface Y) (line l c (diagonalSurface Y))).mapIso
      b ≪≫
    (pullTwistIso Λ (secondProjection Y) _ _ (secondLineComparison l c k p hpl Y) a).symm

-- The comparisons cross the fixed native and bundled derived tensor interfaces.
/-- Forward p2 projection, followed by the canonical change from p2*M to p1*M.
This map has no diagonal class, trace, inverse projection, or invertibility hypothesis. -/
@[irreducible]
def secondForwardProjection
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K)) ⊗
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ⟶
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
      ((twist (coefficient l c).X (diagonalSurface Y) (line l c (diagonalSurface Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj
          ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
            ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
              K)))) :=
  projectionMap (coefficient l c).X (secondProjection Y) _ _ ≫
    (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
      (tensorHom (secondPullComparison l c k p hpl Y K).inv (𝟙 _) ≫
        (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
          (line l c (diagonalSurface Y)) _).hom)

end AlgebraicGeometry.ProEtale.RationalP1
