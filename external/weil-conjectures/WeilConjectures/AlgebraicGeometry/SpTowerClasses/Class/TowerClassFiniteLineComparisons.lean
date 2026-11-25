/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-! # Finite root-line comparisons in the coefficient-tower coordinates

Source: current classes blueprint, clause (2), scalar extension of the root tower.
(blueprint: lem-sfb-tower-class-finite-line-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite inverse image of the scalar-extended root line, with its tensor formula.

Source: current blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension of the root tower; the existing finite Tate comparison.
(blueprint: lem-sfb-tower-class-finite-line-comparisons).

Proof: map the global unit ell from Y to X, and then into every residue field.
The supplied finite coefficient quotients are finite by Base.finite. Apply
spFiniteTwists_cartesian with the n-th quotient as coefficient ring and exponent
n, and take its degree-one isomorphism. Its tensor formula uses the actual
constant coefficient direct-image map and the direct-image roots map. The unique
section characterization of the latter identifies it with restrictRoot through
the roots-section equivalence. This proves the displayed formula without any
tower assembly or compatibility assertion. No condition on the morphism is used.
-/
theorem finiteLineComparisons_exists
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (l : Γ(Y, ⊤))) :
    ∃ δ : ∀ n : ℕ,
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        (finiteLine l E Y n) ≅ finiteLine l E X n,
      ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
        (a : (SpTowerShriek.B l E Y n).obj.obj U)
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U),
        (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
          (δ n).hom).val.app U
            (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
              U.unop a z) =
          Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
            (chart f U).unop
            ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
              (CommRingCat.of (FiniteRing l E n))).hom.app U a)
            (restrictRoot l f n U z) := by
  let hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hY.map f.appTop.hom
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (show IsUnit (l : Y.residueField y) by
      simpa only [map_natCast] using hY.map (Y.Γevaluation y).hom).invertible
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) by
      simpa only [map_natCast] using hX.map (X.Γevaluation x).hom).invertible
  have (n : ℕ) : Finite (FiniteRing l E n) := inferInstance
  choose β hβ hκ using fun n ↦ spFiniteTwists_cartesian f l (FiniteRing l E n)
  refine ⟨fun n ↦ (β n n (finiteScalar l E n)).signed 1, ?_⟩
  intro n U a z
  have hp := hβ n n (finiteScalar l E n) U.unop a z
  have hr : (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U z =
      restrictRoot l f n U z := by
    apply (Scheme.proEtaleRootsOfUnitySections X (l ^ (n + 1)) (chart f U)).injective
    rw [restrictRoot, AddEquiv.apply_symm_apply]
    have hr :=
      (Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).exists
    exact hr.choose_spec U z
  simp only [coefficientTwistLine, coefficientTwistPower,
    SheafOfModules.scalarTensorPower, StrictTower.constantRingIso,
    proEtaleConstantRingAdjunction, proEtaleConstantRingPushforward,
    Scheme.proEtaleConstantRingComparison, Scheme.proEtaleCoefficientInverseImageMap,
    Scheme.proEtaleConstantRing, Scheme.tateFiniteCoefficient, finiteLine, FiniteRing,
    Scheme.proEtaleBaseChange, Functor.op_obj, unop_op, op_unop, hr] at hp ⊢
  convert hp using 1

end AlgebraicGeometry.ProEtale.SpTowerClasses
