/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
import WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # The second coordinate contraction for a symmetric coefficient

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CoordinateTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

variable (A : Type (u + 1)) [CommRing A]

private theorem braided_self_symmetry
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
    {F : C ⥤ D} [F.Braided] (L : C)
    (h : (CategoryTheory.BraidedCategory.braiding L L).hom = 𝟙 _) :
    (CategoryTheory.BraidedCategory.braiding (F.obj L) (F.obj L)).hom = 𝟙 _ := by
  apply (cancel_mono (Functor.LaxMonoidal.μ F L L)).1
  rw [← Functor.LaxBraided.braided, h, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

private theorem pull_swap_identity
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (h : ((derivedTensorSymmetry B Y).app L).hom.app L = 𝟙 _) :
    ((derivedTensorSymmetry B X).app ((upperStar B f).leftDerivedFunctor.obj L)).hom.app
      ((upperStar B f).leftDerivedFunctor.obj L) = 𝟙 _ := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf Y.smallEtaleTopology B)
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology B)
  let := leftDerivedUpperStarMonoidal B f
  let : ((upperStar B f).leftDerivedFunctor).Braided :=
    { braided := leftDerivedUpperStar_μ_map_braiding_hom B f }
  exact braided_self_symmetry (F := (upperStar B f).leftDerivedFunctor) L h

private theorem combine
    {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (R : D ⥤ C) (V : C ⥤ D)
    {N : D} {M K L P : C} (c : N ≅ V.obj M) (e : P ≅ R.obj N)
    (π : (T.obj (R.obj N)).obj L ≅ R.obj ((S.obj N).obj (V.obj L)))
    (π' : (T.obj (R.obj (V.obj M))).obj L ⟶
      R.obj ((S.obj (V.obj M)).obj (V.obj L)))
    (a : P ⟶ K) (b : R.obj (V.obj M) ⟶ K)
    (q : R.obj ((S.obj (V.obj M)).obj (V.obj L)) ⟶ (T.obj K).obj L)
    (hb : e.inv ≫ a = R.map c.hom ≫ b)
    (hi : (T.map b).app L = π' ≫ q)
    (hn : (T.map (R.map c.hom)).app L ≫ π' =
      π.hom ≫ R.map ((S.map c.hom).app (V.obj L))) :
    π.inv ≫ (T.map e.inv).app L ≫ (T.map a).app L =
      R.map ((S.map c.hom).app (V.obj L)) ≫ q := by
  rw [← NatTrans.comp_app, ← T.map_comp, hb, T.map_comp, NatTrans.comp_app]
  rw [hi, reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]

/-- The second-coordinate contraction for any coefficient with identity self symmetry.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle before
using the diagonal integral; Stacks Tags 07A7 and 0B56.
(auxiliary; not a blueprint node).

Proof: base change of the single trace evaluation identifies inverse exchange
followed by f*evaluation with second-projection integration, using
traceBaseChangeEvaluation. Pullback preserves the identity self symmetry of L.
The projectionTraceTensorInterchange identity then moves the exterior f*L across
that integration. Naturality of the ordinary projection map in coordinateH makes
the two projection maps cancel. Functoriality of tensor combines inverse exchange
and f*evaluation; the resulting composite is exactly comparison followed by H of
evaluation. This uses neither the first-coordinate equation nor a diagonal class. -/
theorem secondCoordinateContraction [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (hL : (swap A Y L L).hom = 𝟙 _)
    (t : (push A f).obj ((pull A f).obj L) ⟶ constantComplex A Y)
    (t2 : (push A (pullback.snd f f)).obj
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L)) ⟶ constantComplex A X)
    (ht : (exchange2 A f ((pull A f).obj L)).hom ≫
        (push A (pullback.snd f f)).map (coordinate A f L).hom ≫ t2 =
      (pull A f).map t ≫ (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom) :
    ∀ K : DerivedCategoryModule A Y,
        (comparison A f L ((H A f L).obj K)).hom ≫
            (H A f L).map
              (evaluation A f L t K) =
          (push A (pullback.snd f f)).map
              (((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map
                (coordinateH A f L K).hom).app
                  ((pull A (pullback.snd f f)).obj ((pull A f).obj L))) ≫
            (orderedProjectionIso A (pullback.snd f f) ((H A f L).obj K)
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).inv ≫
                ((derivedTensor (ModuleCat.{u + 1} A) X).obj
                  ((H A f L).obj K)).map t2 ≫
                  (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X
                    ((H A f L).obj K)).hom := by
  intro K
  have hLX : (swap A X ((pull A f).obj L) ((pull A f).obj L)).hom = 𝟙 _ :=
    pull_swap_identity (ModuleCat.{u + 1} A) f L hL
  have hp := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    A isAddTorsion_of_finite (pullback.snd f f)
      ((pull A (pullback.fst f f)).obj ((H A f L).obj K)) ((pull A f).obj L)
  simpa only [comparison, H, derivedTensorRight, Functor.comp_obj, Functor.comp_map,
    Functor.flip_obj_obj, Functor.flip_obj_map, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    (combine (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f f))
    (push A (pullback.snd f f)) (pull A (pullback.snd f f))
    (coordinateH A f L K) (exchange2 A f ((H A f L).obj K))
    (asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (pullback.snd f f)).app
        ((pull A (pullback.fst f f)).obj ((H A f L).obj K))).app ((pull A f).obj L)))
    _ _ _ _
    (traceBaseChangeEvaluation A f L t t2 ht K)
    (projectionTraceTensorInterchange A (pullback.snd f f)
      ((pull A f).obj K) ((pull A f).obj L) hLX t2)
    (NatTrans.congr_app
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
        (pullback.snd f f)).naturality (coordinateH A f L K).hom) ((pull A f).obj L)))

end AlgebraicGeometry.Etale.CoordinateTrace
