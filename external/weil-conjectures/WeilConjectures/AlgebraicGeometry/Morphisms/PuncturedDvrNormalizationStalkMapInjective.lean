/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.RingTheory.RingHom.Injective
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- Injectivity of the normalization stalk map in the punctured DVR situation.
-/
theorem punctured_dvr_normalization_stalkMap_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    Function.Injective ((p ≫ U.ι).fromNormalization.stalkMap x).hom := by
  classical
  by_cases hxU : (p ≫ U.ι).fromNormalization x ∈ U
  · exact (hs hxU).elim
  let f := p ≫ U.ι
  let n := f.fromNormalization
  have : Etale p := hetale
  have : Flat f := inferInstance
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro r hr
  change (n.stalkMap x).hom r = 0 at hr
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨B, hxB, hB, hBV, hinj⟩ := X.exists_le_and_germ_injective (n x) V hxV
  let t := X.presheaf.map (homOfLE hBV).op s
  have ht : X.presheaf.germ B (n x) hxB t =
      X.presheaf.germ V (n x) hxV s := by
    exact X.presheaf.germ_res_apply (homOfLE hBV) (n x) hxB s
  have : IsDomain Γ(X, B) := Function.Injective.isDomain
    (X.presheaf.germ B (n x) hxB).hom hinj
  have hzero : f.normalization.presheaf.germ (n ⁻¹ᵁ B) x hxB (n.app B t) = 0 := by
    rw [← n.germ_stalkMap_apply, ht]
    exact hr
  have he : f.normalization.presheaf.germ (n ⁻¹ᵁ B) x hxB (n.app B t) =
      f.normalization.presheaf.germ (n ⁻¹ᵁ B) x hxB 0 := by simpa using hzero
  obtain ⟨W, hxW, i, j, hij⟩ :=
    f.normalization.presheaf.germ_eq x hxB hxB _ _ he
  obtain ⟨z, hzW⟩ := f.toNormalization.denseRange.exists_mem_open W.isOpen ⟨x, hxW⟩
  have hzB : n (f.toNormalization z) ∈ B := i.le hzW
  have hz : f.normalization.presheaf.germ (n ⁻¹ᵁ B) (f.toNormalization z) hzB
      (n.app B t) = 0 := by
    rw [← f.normalization.presheaf.germ_res_apply i (f.toNormalization z) hzW, hij]
    simp
  have hcomp : f.toNormalization ≫ n = f := f.toNormalization_fromNormalization
  have hzB' : f z ∈ B := by simpa only [← Hom.comp_apply, hcomp] using hzB
  have hz' : P.presheaf.germ (f ⁻¹ᵁ B) z hzB' (f.app B t) = 0 := by
    have H := congrArg (fun a ↦ (f.toNormalization.stalkMap z).hom a) hz
    rw [map_zero, ← n.germ_stalkMap_apply, ← CommRingCat.comp_apply,
      ← Hom.stalkMap_comp] at H
    change (f.toNormalization ≫ n).stalkMap z
      (X.presheaf.germ B ((f.toNormalization ≫ n) z) hzB t) = 0 at H
    have H' : ∀ h : (f.toNormalization ≫ n) z ∈ B,
        (f.toNormalization ≫ n).stalkMap z
          (X.presheaf.germ B ((f.toNormalization ≫ n) z) h t) = 0 := fun _ ↦ H
    rw [hcomp] at H'
    simpa only [Hom.germ_stalkMap_apply] using H' hzB'
  let : Algebra (X.presheaf.stalk (f z)) (P.presheaf.stalk z) :=
    (f.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (f z)) (P.presheaf.stalk z) := Flat.stalkMap f z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f z)) (P.presheaf.stalk z)) := by
    change IsLocalHom (f.stalkMap z).hom
    infer_instance
  have : Module.FaithfullyFlat (X.presheaf.stalk (f z)) (P.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hf : Function.Injective (f.stalkMap z).hom := FaithfulSMul.algebraMap_injective _ _
  have htzero : X.presheaf.germ B (f z) hzB' t = 0 := hf (by
    simpa only [map_zero, Hom.germ_stalkMap_apply] using hz')
  let := X.presheaf.algebra_section_stalk (⟨f z, hzB'⟩ : B)
  have := hB.isLocalization_stalk ⟨f z, hzB'⟩
  have hginj : Function.Injective (X.presheaf.germ B (f z) hzB').hom :=
    IsLocalization.injective (M := (hB.primeIdealOf ⟨f z, hzB'⟩).asIdeal.primeCompl)
      _ (Ideal.primeCompl_le_nonZeroDivisors _)
  have ht0 : t = 0 := hginj (by simpa using htzero)
  change X.presheaf.germ V (n x) hxV s = 0
  rw [← ht, ht0, map_zero]
end AlgebraicGeometry.Scheme
