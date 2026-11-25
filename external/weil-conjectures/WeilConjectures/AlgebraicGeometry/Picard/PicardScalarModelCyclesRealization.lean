/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import WeilConjectures.AlgebraicGeometry.Picard.PicardScalarDerivedCycles
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageTestSections
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Realizing scalar cycles of a fixed perfect direct-image model

## References

* Stacks Project, Tag 0BF2, the lifting of a degree-zero cycle through the base-change comparison
* Stacks Project, Tag 0BF2, the paragraph after the chain-map calculation, with the arbitrary
  base-change comparison of Tag 0B91
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A connective strictly perfect model with a scalar degree-zero basis realizes its
scalar cycles as sections, compatibly with restriction to the marked residue fibre.
This fixes a model; it constructs no degree-one map and assumes no H¹ injectivity. -/
theorem picard_scalar_model_cycles_realization
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hneg : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
      DerivedCategory.Q.obj K))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
      ∃ c : Γ((Modules.tensorPullback
          (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤) ≃+
            W.residueField w,
        ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U),
          ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
            (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
              (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
                ∃ y, j y = x) ∧
            ∃ e : (Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
                (Modules.tensorPullback
                  (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
              ∀ a : Γ(W, V),
                (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
                ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
                  e.hom.app ⊤
                    (((Modules.tensorPullback j).obj
                      ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                        (homOfLE j.preimage_top.ge).op
                          (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                            ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                              (Opposite.op ⊤) σ)) =
                    c.symm (W.evaluation V w hwV a) := by
  classical
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  -- Keep the derived Hom types fixed while eliminating the existence statements.
  refine (picard_scalar_derived_cycles W E w U hwU hU m d K hK hneg
    e0 e1 hE hd hdw).elim fun c hc ↦ ?_
  refine (picard_direct_image_test_sections f L W k w).elim fun q hq ↦ ?_
  refine ⟨(q (W.fromSpecResidueField w)).symm.trans c, ?_⟩
  intro V hwV hVU
  refine (hq V hwV).elim fun j hj ↦ ?_
  refine hj.2.elim fun e he ↦ ?_
  refine ⟨j, hj.1, e, ?_⟩
  intro a ha
  refine (hc V hwV hVU a ha).elim fun ξ hξ ↦ ?_
  refine ⟨q V.ι ξ, ?_⟩
  exact (he ξ).trans (congrArg (q (W.fromSpecResidueField w)) hξ)

end AlgebraicGeometry.Scheme
