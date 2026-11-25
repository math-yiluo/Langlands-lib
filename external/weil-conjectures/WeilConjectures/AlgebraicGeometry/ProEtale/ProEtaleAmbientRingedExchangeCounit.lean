/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange

/-! # The counit form of the ambient ringed exchange

A direct kernel check of `mateEquiv_counit` against `proEtaleAmbientRingedExchange`
times out. Going through the generic counit lemma for an arbitrary comparison and the
equation lemma of the definition (combined by `rw`) is cheap.

## References

* Stacks 07A7
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (θ : proEtaleRingDerivedPullback g R_Y R_Y' c_g ⋙
        proEtaleRingDerivedPullback f' R_Y' R_X' c_f' ≅
      proEtaleRingDerivedPullback f R_Y R_X c_f ⋙ proEtaleRingDerivedPullback g' R_X R_X' c_g')
    (K : DerivedCategory (proEtaleRingModules X R_X))

/-- The counit form of the mate of an arbitrary pullback comparison. -/
theorem mateEquiv_pullbackComparison_counit :
    (proEtaleRingDerivedPullback f' R_Y' R_X' c_f').map
        ((mateEquiv (proEtaleRingDerivedAdjunction f R_Y R_X c_f)
          (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f')
          (TwoSquare.mk _ _ _ _ θ.hom)).app K) ≫
      (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f').counit.app
        ((proEtaleRingDerivedPullback g' R_X R_X' c_g').obj K) =
      θ.hom.app ((proEtaleRingDerivedDirectImage f R_Y R_X c_f).obj K) ≫
        (proEtaleRingDerivedPullback g' R_X R_X' c_g').map
          ((proEtaleRingDerivedAdjunction f R_Y R_X c_f).counit.app K) :=
  mateEquiv_counit _ _ _ K

omit θ in
/-- The counit form of the mate of the ambient pullback comparison. -/
theorem proEtaleAmbientRingedPullbackComparison_mate_counit
    (sq : ChosenCartesianSquare g' f' f g)
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f')) :
    (proEtaleRingDerivedPullback f' R_Y' R_X' c_f').map
        ((mateEquiv (proEtaleRingDerivedAdjunction f R_Y R_X c_f)
          (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f') (TwoSquare.mk _ _ _ _
            (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
              c_f c_g c_g' c_f' hcoeff).hom)).app K) ≫
      (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f').counit.app
        ((proEtaleRingDerivedPullback g' R_X R_X' c_g').obj K) =
      (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
          c_f c_g c_g' c_f' hcoeff).hom.app
          ((proEtaleRingDerivedDirectImage f R_Y R_X c_f).obj K) ≫
        (proEtaleRingDerivedPullback g' R_X R_X' c_g').map
          ((proEtaleRingDerivedAdjunction f R_Y R_X c_f).counit.app K) :=
  mateEquiv_pullbackComparison_counit R_X R_Y R_X' R_Y' c_f c_g c_g' c_f'
    (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y' c_f c_g c_g' c_f' hcoeff) K

omit θ K in
/-- The ambient exchange is the mate of the ambient pullback comparison. -/
theorem proEtaleAmbientRingedExchange_eq_mate (sq : ChosenCartesianSquare g' f' f g)
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f')) :
    proEtaleAmbientRingedExchange sq R_X R_Y R_X' R_Y' c_f c_g c_g' c_f' hcoeff =
      (mateEquiv (proEtaleRingDerivedAdjunction f R_Y R_X c_f)
          (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f') (TwoSquare.mk _ _ _ _
            (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
              c_f c_g c_g' c_f' hcoeff).hom)) :=
  proEtaleAmbientRingedExchange.eq_1 _ _ _ _ _ _ _ _ _ _

omit θ in
/-- The ambient exchange is the mate of the pullback comparison: its counit form. -/
theorem proEtaleAmbientRingedExchange_counit (sq : ChosenCartesianSquare g' f' f g)
    (hcoeff : HEq
      (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f')) :
    (proEtaleRingDerivedPullback f' R_Y' R_X' c_f').map
        ((proEtaleAmbientRingedExchange sq R_X R_Y R_X' R_Y' c_f c_g c_g' c_f' hcoeff).app K) ≫
      (proEtaleRingDerivedAdjunction f' R_Y' R_X' c_f').counit.app
        ((proEtaleRingDerivedPullback g' R_X R_X' c_g').obj K) =
      (proEtaleAmbientRingedPullbackComparison sq R_X R_Y R_X' R_Y'
          c_f c_g c_g' c_f' hcoeff).hom.app
          ((proEtaleRingDerivedDirectImage f R_Y R_X c_f).obj K) ≫
        (proEtaleRingDerivedPullback g' R_X R_X' c_g').map
          ((proEtaleRingDerivedAdjunction f R_Y R_X c_f).counit.app K) := by
  rw [proEtaleAmbientRingedExchange_eq_mate]
  exact proEtaleAmbientRingedPullbackComparison_mate_counit R_X R_Y R_X' R_Y' c_f c_g c_g' c_f'
    K sq hcoeff

end AlgebraicGeometry.Scheme
