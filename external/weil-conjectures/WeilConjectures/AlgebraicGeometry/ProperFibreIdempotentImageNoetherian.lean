/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FormalFunctionsStalk
import WeilConjectures.AlgebraicGeometry.FormalFibreIdempotentLimit
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # The locally Noetherian part of proper-fibre idempotent lifting

Source: Stacks Project, Tag 0G7X, Noetherian case.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem formalFibreZero_iso {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    ∃ a : formalFibre f s 0 ≅ f.fiber s,
      a.hom ≫ f.fiberι s = formalFibreι f s 0 := by
  let c : CommRingCat.of ((S.presheaf.stalk s) ⧸ formalFibreIdeal S s 0) ≅
      S.residueField s := (Ideal.quotEquivOfEq (by simp [formalFibreIdeal])).toCommRingCatIso
  let k := Limits.pullback.map (formalFibreBaseMap S s 0) f (S.fromSpecResidueField s) f
    (Spec.map c.inv) (𝟙 X) (𝟙 S) (by
      simp only [Category.comp_id, formalFibreBaseMap, Scheme.fromSpecResidueField]
      rw [← Spec.map_comp_assoc]
      congr 1) (by simp)
  have : IsIso k := inferInstance
  let a := asIso k ≪≫ Limits.pullbackSymmetry (S.fromSpecResidueField s) f
  exact ⟨a, by simp [a, k, formalFibreι, Scheme.Hom.fiberι]⟩

private theorem completion_image_mod_one {R : Type u} [CommRing R]
    (I : Ideal R) (hI : I.FG) (M : Type u) [AddCommGroup M] [Module R M]
    (N : Type u) [AddCommGroup N] [Module R N]
    (L : AdicCompletion I M →ₗ[R] N)
    (hN : ∀ (r : R), r ∈ I → ∀ n : N, r • n = 0)
    (z : AdicCompletion I M) :
    ∃ x : M, L (AdicCompletion.of I M x) = L z := by
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I ^ 1 • (⊤ : Submodule R M))
    (AdicCompletion.eval I M 1 z)
  have hk : AdicCompletion.of I M x - z ∈ (AdicCompletion.eval I M 1).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, hx, sub_self]
  have hkill : I ^ 1 • (⊤ : Submodule R (AdicCompletion I M)) ≤ L.ker := by
    rw [pow_one]
    exact Submodule.smul_le.mpr fun r hr m _ ↦ by
      rw [LinearMap.mem_ker, map_smul, hN r hr]
  have hz := hkill ((AdicCompletion.pow_smul_top_eq_ker_eval (M := M) (n := 1) hI).symm ▸ hk)
  exact ⟨x, sub_eq_zero.mp (by simpa only [LinearMap.mem_ker, map_sub] using hz)⟩

/-- Idempotents on a proper fibre over a locally Noetherian base lift to sections
near the base point. Source: Stacks Project, Tag 0G7X, Noetherian part of the proof.

Proof: Let A be the local ring at s, m its maximal ideal, and M the stalk of f_* O_X.
The ring A is Noetherian, hence m is finitely generated. On the infinitesimal fibres
X_n over A/m^(n+1), nilpotent base change lifts e uniquely to idempotents e_n.
Uniqueness implies that the e_n restrict compatibly, and e_0 corresponds to e.
Formal functions for O_X identifies the completion of M with the inverse limit of
these section modules. Let z in the completion correspond to (e_n). The quotient of
the completion by m is M/mM, so choose x in M with the same quotient class as z.
The component on the ordinary fibre is A-linear and m kills its target; consequently
x and z have the same fibre image, namely e. Represent x by a section t over f⁻¹(U)
for a neighbourhood U of s. The formal-functions germ formula identifies its fibre
restriction with e. The first infinitesimal fibre and the usual fibre are identified
by A/m = κ(s) and symmetry of the pullback, preserving their projections to X.
(blueprint: lem-weil-pbc-stein-fibre-idempotent-image-noetherian) -/
theorem proper_fibre_idempotent_image_noetherian
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (U : S.Opens), s ∈ U ∧
      ∃ (h : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (t : Γ(X, f ⁻¹ᵁ U)),
        (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e := by
  classical
  obtain ⟨a, ha⟩ := formalFibreZero_iso f s
  let e₀ : Γ(formalFibre f s 0, ⊤) := a.hom.appTop e
  have he₀ : IsIdempotentElem e₀ := he.map a.hom.appTop.hom
  obtain ⟨v, hv⟩ := formalFibre_idempotent_limit f s e₀ he₀
  obtain ⟨b, hb⟩ := formal_functions_stalk_structureSheaf f s
  let M := (RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
  let R := S.presheaf.stalk s
  let I := IsLocalRing.maximalIdeal R
  let N := (ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).obj
    (formalFibreSections f s 0)
  let L : AdicCompletion I M →ₗ[R] N :=
    ((ModuleCat.restrictScalars (algebraMap R (AdicCompletion I R))).map
      (b.hom ≫ Limits.limit.π (formalFibreSectionsSystem f s) (Opposite.op 0))).hom
  have hN : ∀ r : R, r ∈ I → ∀ n : N, r • n = 0 := by
    intro r hr n
    change Γ(formalFibre f s 0, ⊤) at n
    change formalFibreScalarMap f s 0
      (AdicCompletion.evalₐ I 1 (algebraMap R (AdicCompletion I R) r)) * n = 0
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    have hq : Ideal.Quotient.mk (formalFibreIdeal S s 0) r = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (by simpa only [formalFibreIdeal, zero_add, pow_one] using hr)
    change formalFibreScalarMap f s 0 (Ideal.Quotient.mk (formalFibreIdeal S s 0) r) * n = 0
    rw [hq, map_zero, zero_mul]
  obtain ⟨x, hx⟩ := completion_image_mod_one I I.fg_of_isNoetherianRing M N L hN (b.inv v)
  obtain ⟨U, hs, t, ht⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val.presheaf x
  have h : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro z _
    have hz : f (f.fiberι s z) = s := by
      have hz := Set.mem_range_self (f := f.fiberι s) z
      rw [f.range_fiberι s] at hz
      exact hz
    change f (f.fiberι s z) ∈ U
    rw [hz]
    exact hs
  have h₀ : (⊤ : (formalFibre f s 0).Opens) ≤
      (formalFibreι f s 0) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← ha]
    intro z _
    exact h (by trivial : a.hom z ∈ (⊤ : (f.fiber s).Opens))
  have hx₀ : (formalFibreι f s 0).appLE (f ⁻¹ᵁ U) ⊤ h₀ t = e₀ := by
    rw [← hb 0 U hs h₀ t, ht]
    change L (AdicCompletion.of I M x) = e₀
    rw [hx]
    change (Limits.limit.π (formalFibreSectionsSystem f s) (Opposite.op 0)) (b.hom (b.inv v)) = e₀
    simpa only [← ConcreteCategory.comp_apply, b.inv_hom_id, ConcreteCategory.id_apply]
      using hv
  refine ⟨U, hs, h, t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso a.hom.appTop).1
  change a.hom.appTop ((f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t) = e₀
  have hc := Scheme.Hom.appLE_comp_appLE a.hom (f.fiberι s) (f ⁻¹ᵁ U) ⊤ ⊤ h
    (show (⊤ : (formalFibre f s 0).Opens) ≤ a.hom ⁻¹ᵁ ⊤ from le_top)
  have hc' := congrArg (fun k ↦ k t) hc
  simp only [ha, ConcreteCategory.comp_apply] at hc'
  simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.preimage_top, ConcreteCategory.comp_apply] using hc'.trans hx₀

end AlgebraicGeometry
