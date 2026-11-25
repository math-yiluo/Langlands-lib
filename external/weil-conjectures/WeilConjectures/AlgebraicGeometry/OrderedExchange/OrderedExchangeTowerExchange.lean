/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData

/-! # Restriction of the ambient exchange and the constant strict mate

The third strict coefficient equation `towerV'_delta` reduces, through the strict reduction
comparison `rho`, to the ambient-level equation `restriction_strictExchange` below. That
equation splits into the compatibility of scalar restriction with the ambient exchange
(`res_integralExchange`) and the constant-coefficient strict realization of the ambient
exchange (`constantExchange_reduction`).

## References

* Stacks 07A7, 0D6D, 0E48
* Stacks 07A7, 0B56, 099M

## Implementation details

`res_integralExchange` and `constantExchange_reduction` are not yet formalized. For the first,
both exchanges are mates of the canonical pullback-composition comparisons and `chi` is the mate
of the inverse of `alpha`, so pasting of mates reduces it to an ordinary identity-component cube
on K-flat flat-term models (compare `Functor.mapDerivedCategory_cube`). For the second,
transposing under the constant tower adjunction for `f'` reduces it to the compatibility of
`reductionPullIso` with the composition of pullbacks around the square, checked on K-flat
flat-term models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The ambient exchange with constant coefficients. -/
abbrev constantExchange (sq : ChosenCartesianSquare g' f' f g) :
    push (A := A) f ⋙ pull (A := A) g ⟶ pull (A := A) g' ⋙ push (A := A) f' :=
  proEtaleAmbientRingedExchange sq (exchangeConstantRing X A) (exchangeConstantRing Y A)
    (exchangeConstantRing X' A) (exchangeConstantRing Y' A) (exchangeConstantIso f A)
    (exchangeConstantIso g A) (exchangeConstantIso g' A) (exchangeConstantIso f' A)
    (exchangeConstant_coherent sq)

/-- The strict projection is natural in the ambient input. -/
theorem projection_naturality {U V : Scheme.{t}} (u : U ⟶ V) {M N : D (A := A) U}
    (a : M ⟶ N) :
    (reduction d V).map ((push (A := A) u).map a) ≫ projection d u N =
      projection d u M ≫ (exchangeConstantPush (A := A) u).map ((reduction d U).map a) := by
  let aj := exchangeTowerAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let ar := proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
    (exchangeConstantRing U A) (exchangeConstantIso u A)
  let pi0 := (mateEquiv ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom))
  have hpi (M : D (A := A) U) : pi0.app M = projection d u M := by
    apply (aj.homEquiv _ _).symm.injective
    change (aj.homEquiv _ _).symm (pi0.app M) =
      (aj.homEquiv _ _).symm ((aj.homEquiv _ _)
        ((reductionPullIso d u).hom.app ((push (A := A) u).obj M) ≫
          (reduction d U).map (ar.counit.app M)))
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact mateEquiv_counit ar aj (TwoSquare.mk _ _ _ _ (reductionPullIso d u).hom) M
  rw [← hpi, ← hpi]
  exact pi0.naturality a

/-- Scalar restriction carries the completed ambient exchange to the constant one,
conjugated by `alpha` and `chi`. -/
theorem res_integralExchange (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (res d Y').map ((d.integralExchange sq).app K) ≫
        (chi d f').hom.app ((d.pull g').obj K) ≫
        (push (A := A) f').map ((alpha d g').hom.app K) =
      (alpha d g).hom.app ((d.push f).obj K) ≫
        (pull (A := A) g).map ((chi d f).hom.app K) ≫
        (constantExchange (A := A) sq).app ((res d X).obj K) := by
  sorry

/-- The constant strict tower mate realizes the reduction of the constant ambient exchange
through the reduction/pullback comparisons and the strict projections. -/
theorem constantExchange_reduction (sq : ChosenCartesianSquare g' f' f g) (N : D (A := A) X) :
    (reduction d Y').map ((constantExchange (A := A) sq).app N) ≫
        projection d f' ((pull (A := A) g').obj N) ≫
        (exchangeConstantPush (A := A) f').map ((reductionPullIso d g').inv.app N) =
      (reductionPullIso d g).inv.app ((push (A := A) f).obj N) ≫
        (exchangeConstantPull (A := A) g).map (projection d f N) ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app ((reduction d X).obj N) := by
  sorry

/-- The ambient form of the third strict coefficient equation. -/
theorem restriction_strictExchange (sq : ChosenCartesianSquare g' f' f g) (K : d.derived X) :
    (reduction d Y').map ((res d Y').map ((d.integralExchange sq).app K)) ≫
        (reduction d Y').map ((chi d f').hom.app ((d.pull g').obj K)) ≫
        projection d f' ((res d X').obj ((d.pull g').obj K)) ≫
        (exchangeConstantPush (A := A) f').map ((reduction d X').map ((alpha d g').hom.app K)) ≫
        (exchangeConstantPush (A := A) f').map ((reductionPullIso d g').inv.app ((res d X).obj K)) =
      (reduction d Y').map ((alpha d g).hom.app ((d.push f).obj K)) ≫
        (reductionPullIso d g).inv.app ((res d Y).obj ((d.push f).obj K)) ≫
        (exchangeConstantPull (A := A) g).map ((reduction d Y).map ((chi d f).hom.app K)) ≫
        (exchangeConstantPull (A := A) g).map (projection d f ((res d X).obj K)) ≫
        (exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K)) := by
  have hA := congrArg (reduction d Y').map (res_integralExchange d sq K)
  simp only [Functor.map_comp] at hA
  have hB := constantExchange_reduction d sq ((res d X).obj K)
  have hP := projection_naturality d f' ((alpha d g').hom.app K)
  have hR := (reductionPullIso d g).inv.naturality ((chi d f).hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hR
  rw [← reassoc_of% hP, reassoc_of% hA, hB, reassoc_of% hR]

end AlgebraicGeometry.Scheme.OrderedExchange
