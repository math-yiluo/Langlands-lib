/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1CommonMinimalModel
import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1FixedModelComparison
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local scalar models and degree-one comparison for Picard descent

## References

* Stacks Project, Tag 0BF2, the finite-free complexes and the representing chain maps
* Stacks Project, Tag 0BF2, through the displayed chain maps, using Tags 0B91, 0BCD and 08CR
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Construct the local finite-free model and its degree-one comparison square, without
assuming injectivity on H¹ and without realizing degree-zero cycles as sections. -/
theorem picard_h1_base_descent_local_model
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLi : ∀ i, ∃ (N : W.Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        (Modules.tensorPullback (pullback.snd (fi i) k)).obj N))
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    ∃ (U : W.Opens) (hwU : w ∈ U), IsAffineOpen U ∧
      ∃ (m q : ℕ) (d : Fin m → Γ(W, U))
        (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U)))
        (K : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ),
        IsStrictlyPerfect W U K ∧ (∀ i : ℤ, i < 0 → IsZero (K.X i)) ∧
        ∃ (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
          (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U))),
          Nonempty ((SheafOfModules.overFunctor.{v}
            (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
              ((schemeDerivedDirectImage (pullback.snd f k)).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{v}
                    (moduleRings (pullback f k).toRingedSpace)) 0).obj
                      ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
            DerivedCategory.Q.obj K) ∧
          (∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d) ∧
          (∀ i, W.evaluation U w hwU (d i) = 0) ∧ b d = 0 ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z) := by
  -- Explicit existential elimination avoids generalizing the large dependent conclusion.
  refine (picard_h1_common_minimal_model
    f Xi fi ui hui hO hOi L W k w s hw hLi hLs).elim fun U hmodel ↦ ?_
  refine hmodel.elim fun hwU hmodel ↦ ?_
  have hU := hmodel.1
  have htrivial := hmodel.2.1
  refine hmodel.2.2.elim fun m hmodel ↦ ?_
  refine hmodel.elim fun K hmodel ↦ ?_
  have hbounded := hmodel.1
  have hbetti := hmodel.2.1
  have hrank := hmodel.2.2.1
  refine hmodel.2.2.2.elim fun e0 hmodel ↦ ?_
  refine hmodel.elim fun e1 hmodel ↦ ?_
  have hE := hmodel.1
  have hdw := hmodel.2
  have hK : IsStrictlyPerfect W U K := by
    refine ⟨hbounded, fun j ↦ ?_⟩
    obtain ⟨e⟩ := hrank j
    exact ⟨_, e.hom, e.inv, e.hom_inv_id⟩
  have hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j) := by
    intro j hj
    obtain ⟨e⟩ := hrank j
    rw [hbetti j hj] at e
    have hfree : IsZero (SheafOfModules.free
        (R := (moduleRings W.toRingedSpace).over U)
        (ULift.{v} (Fin 0))) := by
      rw [IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext i
      exact Fin.elim0 i.down
    exact hfree.of_iso e
  refine (picard_h1_fixed_model_comparison f Xi fi ui hui hO hOi L W k w s hw hLs
    U hwU hU htrivial m K hK hnegative hrank e0 e1 hE).elim fun q hcomparison ↦ ?_
  refine hcomparison.elim fun b hcomparison ↦ ?_
  have hb := hcomparison.1
  let d := e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm 1))
  refine ⟨U, hwU, hU, m, q, d, b, K, hK, hnegative, e0, e1, hE, ?_, hdw,
    hb 1, hcomparison.2⟩
  intro a
  have ha : e0.symm a = a • e0.symm 1 := by
    rw [← e0.symm.map_smul]
    simp
  rw [ha]
  rw [map_smul, e1.map_smul]

end AlgebraicGeometry.Scheme
