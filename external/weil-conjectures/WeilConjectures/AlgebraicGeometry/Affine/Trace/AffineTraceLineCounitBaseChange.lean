/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLineOpenCounitBaseChange

/-! # Base change for the affine trace tower -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem counitSquareComposite
    {C D E C' D' E' : Type*} [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    {L : D ⥤ C} {R : C ⥤ D} {J : E ⥤ D} {U : D ⥤ E}
    {L' : D' ⥤ C'} {R' : C' ⥤ D'} {J' : E' ⥤ D'} {U' : D' ⥤ E'}
    (a : L ⊣ R) (a' : L' ⊣ R') (j : J ⊣ U) (j' : J' ⊣ U')
    (B : C ⥤ C') (B1 : D ⥤ D') (B2 : E ⥤ E')
    (s : U ⋙ B2 ≅ B1 ⋙ U') (K : C)
    (c : B1.obj (R.obj K) ≅ R'.obj (B.obj K))
    (p : ∀ M : D, B.obj (L.obj M) ⟶ L'.obj (B1.obj M))
    (e : (J ⋙ L) ⋙ B ⟶ B2 ⋙ (J' ⋙ L'))
    (ho : ∀ M : D, e.app (U.obj M) ≫ (J' ⋙ L').map (s.hom.app M) ≫
      L'.map (j'.counit.app (B1.obj M)) =
      B.map (L.map (j.counit.app M)) ≫ p M)
    (hp : B.map (a.counit.app K) =
      p (R.obj K) ≫ L'.map c.hom ≫ a'.counit.app (B.obj K)) :
    e.app ((R ⋙ U).obj K) ≫
      (J' ⋙ L').map (affineTraceCompositeRightSquareIso s K c).hom ≫
      (affineTraceComposeAdjunction j' a').counit.app (B.obj K) =
        B.map ((affineTraceComposeAdjunction j a).counit.app K) := by
  have hn := congrArg (fun f ↦ L'.map f) (j'.counit.naturality c.hom)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
  rw [affineTraceComposeAdjunction_counit, affineTraceComposeAdjunction_counit]
  dsimp only [affineTraceCompositeRightSquareIso, affineTraceRightSquareIso]
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have hoK := ho (R.obj K)
  simp only [Functor.comp_map] at hoK
  rw [reassoc_of% hoK]
  rw [← hp]

/-- The affine-line counit square, before coordinate pasting.
Source: blueprint lemma-integral-linear-character--1, proof step 8
(blueprint: lem-amb-affine-trace-line-counit-base-change).

Proof: expand the compact-support exchange into proper exchange followed by the
inverse open exchange and the compactification comparison. The inverse open exchange
is the mate of the open unit; the two open counit composites therefore have the same
identity adjunct. Paste that equality with the normalized projective-line counit
square supplied by hD, and cancel the coherent compactification comparisons.
This is an equality of the defining unbounded mate formulas for every K. The empty
base, zero coefficient ring and identity base change use the same triangle identities. -/
theorem affineTraceLineCounit_baseChange (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (_hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (hD : OrdinaryFiniteP1BaseChange A N hA t D)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (K : DerivedCategoryModule A S) :
    affineTraceLineExchange A g ((affineTraceLineRight A N hA S).obj K) ≫
        (affineTraceLineLeft A S').map
          (affineTraceLineRightBaseChange A N hA t g
            (affineTraceProjectiveInvertible N S hS) K).hom ≫
        (affineTraceLineAdjunction A N hA t S'
          (affineTracePullbackInvertible N g hS) (D _ _)).counit.app
            ((ordinaryFinitePullback A g).obj K) =
      (ordinaryFinitePullback A g).map
        ((affineTraceLineAdjunction A N hA t S hS (D _ _)).counit.app K) := by
  unfold affineTraceLineExchange
  apply counitSquareComposite
    (C := DerivedCategoryModule A S) (D := DerivedCategoryModule A (ProjectiveLine S))
    (E := DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S))
    (C' := DerivedCategoryModule A S') (D' := DerivedCategoryModule A (ProjectiveLine S'))
    (E' := DerivedCategoryModule A (AffineSpace PUnit.{u + 1} S'))
    (L := ordinaryFinitePushforward A (ProjectiveLine S ↘ S))
    (R := ordinaryFiniteP1Right A N hA S)
    (J := affineTraceOpenLeft A S)
    (U := ordinaryFinitePullback A (ProjectiveLine.affineChart S))
    (L' := ordinaryFinitePushforward A (ProjectiveLine S' ↘ S'))
    (R' := ordinaryFiniteP1Right A N hA S')
    (J' := affineTraceOpenLeft A S')
    (U' := ordinaryFinitePullback A (ProjectiveLine.affineChart S'))
    (D S hS).adjunction
    (D S' (affineTracePullbackInvertible N g hS)).adjunction
    (affineTraceOpenAdjunction A S) (affineTraceOpenAdjunction A S')
    (ordinaryFinitePullback A g)
    (ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g))
    (ordinaryFinitePullback A (AffineSpace.map PUnit.{u + 1} g))
    (affineTraceOpenPullbackSquare A g) K
    (ordinaryFiniteP1RightBaseChange A N hA t g
      (affineTraceProjectiveInvertible N S hS) K)
    (fun M ↦ ordinaryFiniteP1Exchange A g M)
    (affineTraceLineExchangeTransformation A g)
  · intro M
    simpa only [affineTraceLineExchange] using affineTraceLineExchange_openCounit A g M
  · exact (hD g hS (affineTracePullbackInvertible N g hS)).2.2 K

end AlgebraicGeometry.Etale
