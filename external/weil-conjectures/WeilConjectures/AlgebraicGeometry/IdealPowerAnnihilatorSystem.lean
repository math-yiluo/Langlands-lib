/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.AlgebraicGeometry.IdealPowerAnnihilatorQuasicoherent
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # IdealPowerAnnihilatorSystem

Source: Stacks Project, Properties, Lemma 01PQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The annihilator subsheaves of the powers form an increasing quasi-coherent system,
vanish on the specified open, and their cokernel projections are isomorphisms there.

Proof: For each n, form the subsheaf of F consisting of sections killed by every local
section of I^n on every smaller open. Closure under addition, scalars and restriction
is immediate; gluing holds by gluing in F and testing the products locally. This is
an actual subsheaf with its injective inclusion. On affine opens I^n is a finitely
generated ideal J^n and F is the sheaf of a module M. Finite generation permits
clearing one common denominator for all ideal generators, so localization of the
annihilator equals the annihilator of the localized ideal. Thus the subsheaf is
quasi-coherent. The inclusion I^m -> I^n for n <= m makes the annihilators increasing.
On W contained in U, the power inclusion is bijective, so lift 1 and test annihilation
on W itself: every section of the annihilator is zero. Restriction to U preserves
cokernels, and the annihilator restricts to the zero module. Therefore its cokernel
projection restricts to an isomorphism; evaluating on any W contained in U gives the
asserted bijection.

Source: Stacks Project, Properties, Lemma 01PQ and its reduction to Lemma 01PM.
(blueprint: lem-weil-pbc-ideal-power-annihilator-system). -/
theorem ideal_power_annihilator_system
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens)
    (hbij : ∀ (n : ℕ) (W : X.Opens), W ≤ U →
      Function.Bijective ((idealSheafPower ι n).2.app W)) :
    ∃ (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F),
          (∀ n : ℕ, Mono (a n)) ∧
          (∀ n : ℕ, (A n).IsQuasicoherent) ∧
          (∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
            s ∈ Set.range ((a n).app W) ↔
              ∀ (W' : X.Opens) (h : W' ≤ W)
                (b : Γ((idealSheafPower ι n).1, W')),
                (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
                  (F.presheaf.map (homOfLE h).op s) = 0) ∧
          (∀ (n m : ℕ), n ≤ m → ∃ t : A n ⟶ A m, t ≫ a m = a n) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U → Subsingleton Γ(A n, W)) ∧
          (∀ n : ℕ,
            IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n)))) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U →
            Function.Bijective ((cokernel.π (a n)).app W)) := by
  classical
  let A : ℕ → X.Modules := fun n ↦ idealAnnihilator (idealSheafPower ι n).2 F
  let a : ∀ n : ℕ, A n ⟶ F := fun n ↦ idealAnnihilatorι (idealSheafPower ι n).2 F
  have hmono (n : ℕ) : Mono (a n) := by dsimp [a]; infer_instance
  have hqc (n : ℕ) : (A n).IsQuasicoherent :=
    ideal_power_annihilator_quasicoherent ι F n
  have himage (n : ℕ) (W : X.Opens) (s : Γ(F, W)) :
      s ∈ Set.range ((a n).app W) ↔
        ∀ (V : X.Opens) (h : V ≤ W) (b : Γ((idealSheafPower ι n).1, V)),
          (F.smul (U := V) ((idealSheafPower ι n).2.val.app (op V) b)).asHom.hom
            (F.presheaf.map (homOfLE h).op s) = 0 := by
    change (∃ t : idealAnnihilatorSections (idealSheafPower ι n).2 F W, t.val = s) ↔
      s ∈ idealAnnihilatorSections (idealSheafPower ι n).2 F W
    exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ t.property, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩
  have hinc (n m : ℕ) (h : n ≤ m) : ∃ t : A n ⟶ A m, t ≫ a m = a n := by
    have hle : idealAnnihilatorPresheaf (idealSheafPower ι n).2 F ≤
        idealAnnihilatorPresheaf (idealSheafPower ι m).2 F := by
      induction h with
      | refl => exact le_rfl
      | @step m h ih =>
        apply le_trans ih
        intro W s hs V hV b
        cases m with
        | zero => exact hs V hV (ι.app V b)
        | succ m => exact hs V hV ((idealModuleProductι ι _).app V b)
    exact ⟨⟨PresheafOfModules.Submodule.homOfLE hle⟩, rfl⟩
  have hzero (n : ℕ) (W : X.Opens) (hW : W ≤ U) : Subsingleton Γ(A n, W) := by
    have hz (s : Γ(A n, W)) : s = 0 := by
      obtain ⟨b, hb⟩ := (hbij n W hW).2 (1 : Γ(X, W))
      have hh := s.property W le_rfl b
      change (show Γ(X, W) from (idealSheafPower ι n).2.app W b) •
        F.presheaf.map (𝟙 (op W)) s.val = 0 at hh
      rw [hb, F.presheaf.map_id, ConcreteCategory.id_apply, one_smul] at hh
      exact Subtype.ext hh
    exact ⟨fun s t ↦ (hz s).trans (hz t).symm⟩
  have hquot (n : ℕ) (W : X.Opens) (hW : W ≤ U) :
      Function.Bijective ((cokernel.π (a n)).app W) := by
    let S (x : X) := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    have hstalk (x : X) (hx : x ∈ W) :
        Function.Bijective ((S x).map (cokernel.π (a n))).hom := by
      have hAz (t : (S x).obj (A n)) : t = 0 := by
        obtain ⟨V, hxV, t, rfl⟩ := (A n).presheaf.exists_germ_eq t
        have hxVW : x ∈ V ⊓ W := ⟨hxV, hx⟩
        rw [← (A n).presheaf.germ_res_apply (homOfLE inf_le_left) x hxVW t]
        have : Subsingleton Γ(A n, V ⊓ W) := hzero n _ (inf_le_right.trans hW)
        rw [Subsingleton.elim ((A n).presheaf.map (homOfLE inf_le_left).op t) 0,
          map_zero]
      obtain ⟨hepi, hexact⟩ := (RingedSpace.module_stalk_exact X.toRingedSpace (a n)).2.2.1 x
      refine ⟨?_, (ModuleCat.epi_iff_surjective _).mp hepi⟩
      apply (injective_iff_map_eq_zero ((S x).map (cokernel.π (a n))).hom).2
      intro s hs
      have hmem : s ∈ LinearMap.range ((S x).map (a n)).hom := by
        rw [hexact.moduleCat_range_eq_ker]
        exact hs
      obtain ⟨t, rfl⟩ := hmem
      rw [hAz t, map_zero]
    let fs := (SheafOfModules.toSheaf X.ringCatSheaf).map (cokernel.π (a n))
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective fs W hstalk
  have hiso (n : ℕ) :
      IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n))) := by
    let f := (SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n))
    have hb (V : (Over U)ᵒᵖ) : Function.Bijective (f.val.app V) := by
      exact hquot n V.unop.left (leOfHom V.unop.hom)
    have : Mono f.val := PresheafOfModules.mono_of_injective (fun {V} ↦ (hb V).1)
    have : Epi f.val := PresheafOfModules.epi_of_surjective (fun {V} ↦ (hb V).2)
    have : IsIso f.val := isIso_of_mono_of_epi _
    let : IsIso ((SheafOfModules.forget _).map f) := by
      change IsIso f.val
      infer_instance
    exact isIso_of_reflects_iso f (SheafOfModules.forget _)
  exact ⟨A, a, hmono, hqc, himage, hinc, hzero, hiso, hquot⟩

end AlgebraicGeometry.Scheme
