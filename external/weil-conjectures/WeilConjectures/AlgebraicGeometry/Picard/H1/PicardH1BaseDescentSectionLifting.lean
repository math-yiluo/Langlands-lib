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
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

import WeilConjectures.AlgebraicGeometry.Picard.H1.PicardH1BaseDescentCyclePresentation
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalization
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Local lifting of arbitrary marked-fibre sections

## References

* Stacks Project, Tag 0BF2, the degree-zero differential argument
* Stacks Project, Tag 0BF2, the perfect-complex argument through d = 0
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Every marked-fibre section lifts after shrinking the base around the marked point.
This asserts surjectivity of restriction, not existence of a generating section. -/
theorem picard_h1_base_descent_section_lifting {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
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
    ∀ τ : Γ((Modules.tensorPullback
      (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤),
    ∃ (V : W.Opens) (hwV : w ∈ V),
      ∃ j : pullback f (W.fromSpecResidueField w ≫ k) ⟶ pullback f (V.ι ≫ k),
        (∀ x : (pullback f (V.ι ≫ k) : Scheme.{v}),
          (pullback.snd f (V.ι ≫ k)) x = (⟨w, hwV⟩ : V.toScheme) →
            ∃ y, j y = x) ∧
        ∃ e : (Modules.tensorPullback j).obj
          ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L) ≅
          (Modules.tensorPullback (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L,
            ∃ σ : Γ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L, ⊤),
              e.hom.app ⊤
                (((Modules.tensorPullback j).obj
                  ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).presheaf.map
                    (homOfLE j.preimage_top.ge).op
                      (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                        ((Modules.tensorPullback (pullback.fst f (V.ι ≫ k))).obj L)).val.app
                          (Opposite.op ⊤) σ)) = τ := by
  classical
  -- Explicit existential elimination avoids generalizing the dependent section types.
  refine (picard_h1_base_descent_cycle_presentation
    f Xi fi ui hui hO hOi L W k w s hw hLi hLs hH).elim fun U hU ↦ ?_
  refine hU.elim fun hwU hU ↦ ?_
  refine hU.elim fun m hU ↦ ?_
  refine hU.elim fun q hU ↦ ?_
  refine hU.elim fun d hU ↦ ?_
  refine hU.elim fun b hU ↦ ?_
  refine hU.elim fun hp hU ↦ ?_
  let A := Γ(W, U)
  let p : Ideal A := RingHom.ker (W.evaluation U w hwU).hom
  let : p.IsPrime := hp
  have hb := hU.1
  have hbd := hU.2.1
  refine hU.2.2.elim fun c hcycles ↦ ?_
  refine ((Module.finiteFreeMap_residue_localization m q b p).1 hb).elim fun r hr ↦ ?_
  have hbr := hr.2.1
  let B := Localization.Away r
  have hdB : (1 : B) ⊗ₜ[A] d = 0 := by
    apply hbr
    change (b.baseChange B) ((1 : B) ⊗ₜ[A] d) = (b.baseChange B) 0
    rw [LinearMap.baseChange_tmul, hbd, TensorProduct.tmul_zero, map_zero]
  have hd : ∀ i, algebraMap A B (d i) = 0 := by
    intro i
    have h := congrArg (fun z ↦ TensorProduct.piScalarRightHom A B B (Fin m) z i) hdB
    simpa [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def] using h
  have hwr : w ∈ W.basicOpen r := by
    apply (W.mem_basicOpen r w hwU).mpr
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    exact hr.1
  intro τ
  refine (W.residue_surjective w (c τ)).elim fun t ht ↦ ?_
  refine (W.presheaf.exists_le_germ_eq t hwr).elim fun V hV ↦ ?_
  have hVr := hV.1
  refine hV.2.elim fun hwV hV ↦ ?_
  refine hV.elim fun a ha ↦ ?_
  have hVU : V ≤ U := hVr.trans (W.basicOpen_le r)
  have hrV : IsUnit (W.presheaf.map (homOfLE hVU).op r) := by
    have hunit := W.toRingedSpace.isUnit_res_basicOpen r
    have hmap := hunit.map (W.presheaf.map (homOfLE hVr).op).hom
    change IsUnit ((W.presheaf.map (homOfLE hVr).op)
      ((W.presheaf.map (homOfLE (W.basicOpen_le r)).op) r)) at hmap
    rw [← CommRingCat.comp_apply, ← Functor.map_comp] at hmap
    exact hmap
  let ρ : B →+* Γ(W, V) :=
    IsLocalization.Away.lift r (g := (W.presheaf.map (homOfLE hVU).op).hom) hrV
  have hdV : ∀ i, W.presheaf.map (homOfLE hVU).op (d i) = 0 := by
    intro i
    have h := congrArg ρ (hd i)
    have hρ : ρ (algebraMap A B (d i)) =
        W.presheaf.map (homOfLE hVU).op (d i) :=
      IsLocalization.Away.lift_eq r hrV (d i)
    rw [hρ, map_zero] at h
    exact h
  refine (hcycles V hwV hVU).elim fun j hj ↦ ?_
  refine hj.2.elim fun e hσ ↦ ?_
  refine (hσ a (by intro i; rw [hdV i, zero_mul])).elim fun σ hσ ↦ ?_
  refine ⟨V, hwV, j, hj.1, e, σ, ?_⟩
  have heval : W.evaluation V w hwV a = c τ := by
    change W.residue w (W.presheaf.germ V w hwV a) = c τ
    rw [ha, ht]
  simpa only [heval, AddEquiv.symm_apply_apply] using hσ

end AlgebraicGeometry.Scheme
