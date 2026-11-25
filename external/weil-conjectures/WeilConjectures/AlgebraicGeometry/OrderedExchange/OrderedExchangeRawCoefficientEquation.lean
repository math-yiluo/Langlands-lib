/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeStrictCoefficientEquations
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeReconstructionEquations

/-! # rawCoefficientEquation

## References

* Stacks 0E48
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

/-- The final cancellation of the ordered comparison maps, at one complete input. -/
theorem rawCoefficientEquation (sq : ChosenCartesianSquare g' f' f g)
    (K : AComplete d X) : rawComponent d sq K = constantComponent d sq K := by
  obtain ⟨-, -, hV⟩ := strictCoefficientEquations d sq K.obj K.property
  obtain ⟨-, -, hS, hT⟩ := reconstructionCoefficientEquations d sq K.obj K.property
  have hL := (lambda d Y').hom.naturality (d.towerV' sq K.obj)
  have hT' : (iotaT (f' := f') (g' := g') d K.obj K.property).hom =
      (res d Y').map (targetA (g' := g') (f' := f') d K.obj).hom ≫
        (lambda d Y').hom.app
          ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K.obj))) ≫
        (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K.obj).hom ≫
        (T (f' := f') (g' := g') d ((res d X).obj K.obj)).inv := by
    rw [reassoc_of% hT, Iso.hom_inv_id, Category.comp_id]
  have hE : (res d Y').map (d.completedExchange sq K.obj) =
      (res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K.obj).hom ≫
        (res d Y').map ((completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K.obj)) ≫
        (res d Y').map (targetA (g' := g') (f' := f') d K.obj).inv := by
    simp only [AdicCoefficientDatum.completedExchange, Functor.map_comp]
    rfl
  have hV' : (rlim (A := A) Y').map ((exchangeTowerRes d Y').map (d.towerV' sq K.obj)) ≫
      (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K.obj).hom =
      (rlim (A := A) Y').map (beta (f := f) (g := g) d K.obj).hom ≫
        (rlim (A := A) Y').map ((exchangeConstantSquare (A := A) sq).exchangeTowerMate.app
          ((reduction d X).obj ((res d X).obj K.obj))) := by
    rw [← Functor.map_comp, hV, Functor.map_comp]
  change (res d Y').map (d.completedExchange sq K.obj) ≫
      (iotaT (g' := g') (f' := f') d K.obj K.property).hom = _
  rw [hT', hE]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_map_assoc]
  erw [reassoc_of% hL]
  rw [reassoc_of% hV']
  erw [reassoc_of% hS]
  rfl

end AlgebraicGeometry.Scheme.OrderedExchange
