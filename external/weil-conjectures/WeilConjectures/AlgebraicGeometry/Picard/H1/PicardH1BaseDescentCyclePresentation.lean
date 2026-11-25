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

import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1BaseDescentLocalModel
import WeilConjectures.AlgebraicGeometry.Picard.PicardScalarModelCyclesRealization

/-! # A degree-zero cycle presentation for the Picard H¹ argument

## References

* Stacks Project, Tag 0BF2, the finite-free complexes and their chain maps
* Stacks Project, Tag 0BF2, from the perfect models through the joint degree-one map
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Near `w` there are a vector `d` and a linear map `b` over `Γ(W, U)` with `b d = 0` and
injective residue map at `w`, such that every section `a` on an open `w ∈ V ≤ U` annihilating
`d` gives a section of the pullback of `L` restricting to `a(w)` on the fibre over `w`. -/
theorem picard_h1_base_descent_cycle_presentation {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
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
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (hH : Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1 ↦ fun i ↦
      structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f) (ui i) (hui i))).left) 1 x)) :
    ∃ (U : W.Opens) (hwU : w ∈ U) (m q : ℕ)
      (d : Fin m → Γ(W, U))
      (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      let p := RingHom.ker (W.evaluation U w hwU).hom
      ∃ hp : p.IsPrime,
        (letI := hp; Function.Injective (b.baseChange p.ResidueField)) ∧ b d = 0 ∧
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
                (∀ i, W.presheaf.map (homOfLE hVU).op (d i) * a = 0) →
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
  let : ∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.standard
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))
  let : ∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U)) :=
    fun Y U ↦ HasDerivedCategory.standard
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))
  obtain ⟨U, hwU, hU, m, q, d, b, K, hK, hneg, e0, e1, hE, hd, hdw, hbd,
      α, β, hcompare⟩ :=
    picard_h1_base_descent_local_model f Xi fi ui hui hO hOi L W k w s hw hLi hLs
  let p := RingHom.ker (W.evaluation U w hwU).hom
  have hp : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
  let : p.IsPrime := hp
  have hb : Function.Injective (b.baseChange p.ResidueField) := by
    intro x y hxy
    apply α.injective
    apply hH
    calc
      _ = β ((b.baseChange p.ResidueField) x) := (hcompare x).symm
      _ = β ((b.baseChange p.ResidueField) y) := congrArg β hxy
      _ = _ := hcompare y
  obtain ⟨c, hcycles⟩ :=
    picard_scalar_model_cycles_realization f L W k w U hwU hU m d K hK hneg
      e0 e1 hE hd hdw
  refine ⟨U, hwU, m, q, d, b, hp, hb, hbd, c, ?_⟩
  intro V hwV hVU
  obtain ⟨j, hj, e, hsection⟩ := hcycles V hwV hVU
  refine ⟨j, hj, e, ?_⟩
  intro a ha
  apply hsection a
  funext i
  change a * W.presheaf.map (homOfLE hVU).op (d i) = 0
  rw [mul_comm]
  exact ha i

end AlgebraicGeometry.Scheme
