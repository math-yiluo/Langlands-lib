/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility
import WeilConjectures.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.Kummer

/-!
# Proper Kummer degree-one base change

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case in degree
one (blueprint: lem-sc-proper-kummer-degree-one-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem proper_units_divisible {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    ∀ a : Γ(C, ⊤)ˣ, ∃ v : Γ(C, ⊤)ˣ, v ^ n = a := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (C ↘ Spec (.of k)) := ‹IsProper f›
  let := (Scheme.globalSectionsRingHom k (X := C)).toAlgebra
  have : Module.Finite k Γ(C, ⊤) := Scheme.finite_globalSectionsRingHom_of_isProper
  exact IsAlgClosed.exists_pow_eq_of_finite hn

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case in
degree one (blueprint: lem-sc-proper-kummer-degree-one-base-change).

Proof: Global units of a proper curve over an algebraically closed field are n-divisible.
The Kummer sequence therefore identifies H¹(mu_n) with Picard n-torsion, naturally
under pullback. Torsion has degree zero, so Jacobian representability identifies this
map with pullback on Jacobian n-torsion points. Jacobian base change identifies the
target with the scalar extension of the source Jacobian. Its n-torsion is finite
etale because n is invertible. A finite etale scheme over an algebraically closed
field is a disjoint union of rational points, and extension preserves those points.
Thus the map on n-torsion, and hence the displayed cohomology map, is bijective. -/
theorem IsConnectedCurve.proper_kummer_degree_one_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0)
    (φ : ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).mapShortComplex.obj
        (C.kummerSequence n)) ⟶
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerSequence n)
    (hφ : φ.τ₂ = upperStarGmSheafToGmSheaf
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    Function.Bijective ((Sheaf.H.map φ.τ₁ 1).comp
      (Etale.cohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (C.rootsOfUnitySheaf n) 1)) := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P := pullback f b
  let π := pullback.fst f b
  obtain ⟨hC, hP, ψ, hψ₂, hψ₃, hδ, hι, _, hPic, _, _⟩ :=
    kummer_base_change_compatibility k K C f P π (pullback.snd f b)
      (IsPullback.of_hasPullback f b) n hn
  have : Mono (P.kummerSequence n).f := hP.mono_f
  have hτ : ψ.τ₁ = φ.τ₁ := by
    apply (cancel_mono (P.kummerSequence n).f).1
    rw [ψ.comm₁₂, φ.comm₁₂, hψ₂, hφ]
  let μ : Sheaf.H (C.rootsOfUnitySheaf n) 1 →+ Sheaf.H (P.rootsOfUnitySheaf n) 1 :=
    (Sheaf.H.map ψ.τ₁ 1).comp (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1)
  have hnC : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hnK : (n : K) ≠ 0 := by
    simpa only [map_natCast] using ((map_ne_zero (algebraMap k K)).mpr hn)
  have hnP : IsUnit (n : Γ(P, ⊤)) := by
    simpa using hnK.isUnit.map ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd f b).appTop).hom
  let α := C.kummerδ₀ n hnC
  let αP := P.kummerδ₀ n hnP
  let β : Sheaf.H (C.rootsOfUnitySheaf n) 1 →+ C.CohomologicalPicardGroup :=
    Sheaf.H.map (C.kummerSequence n).f 1
  let βP : Sheaf.H (P.rootsOfUnitySheaf n) 1 →+ P.CohomologicalPicardGroup :=
    Sheaf.H.map (P.kummerSequence n).f 1
  obtain ⟨hα, hex, hβ⟩ := C.exact_sheafH_rootsOfUnitySheaf_one n hnC
  obtain ⟨hαP, hexP, hβP⟩ := P.exact_sheafH_rootsOfUnitySheaf_one n hnP
  let E := Scheme.Pic.toCohomologicalPicardGroupAddEquiv C
  let EP := Scheme.Pic.toCohomologicalPicardGroupAddEquiv P
  let V : C.CohomologicalPicardGroup →+ P.CohomologicalPicardGroup :=
    EP.toAddMonoidHom.comp
      ((Scheme.Pic.mapHom π).toAdditive.comp E.symm.toAddMonoidHom)
  have hβnat (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) : βP (μ x) = V (β x) := by
    have hp := hPic (E.symm (β x)).toMul
    change EP (Additive.ofMul (Scheme.Pic.map π (E.symm (β x)).toMul)) =
      Sheaf.H.map (upperStarGmSheafToGmSheaf π) 1
        (Etale.cohomologyMap π C.gmSheaf 1 (E (E.symm (β x)))) at hp
    rw [AddEquiv.apply_symm_apply] at hp
    have hi := hι 1 x
    rw [hψ₂] at hi
    exact hi.symm.trans hp.symm
  obtain ⟨F, hF, hFmap⟩ := proper_pic_torsion_baseChange_bijective (K := K) f n hn
  have hVinj (x : C.CohomologicalPicardGroup) (hx : n • x = 0) (hv : V x = 0) : x = 0 := by
    have hx' : (E.symm x).toMul ^ n = 1 := by
      have h := congrArg E.symm hx
      simp only [map_nsmul, map_zero] at h
      simpa only [toMul_nsmul, toMul_zero] using congrArg Additive.toMul h
    let t : {L : C.Pic // L ^ n = 1} := ⟨(E.symm x).toMul, hx'⟩
    have hp : Additive.ofMul (Scheme.Pic.map π t.val) = 0 := by
      apply EP.injective
      change EP (Additive.ofMul (Scheme.Pic.map π (E.symm x).toMul)) = EP 0
      rw [map_zero]
      exact hv
    have hFt : F t = F ⟨1, by simp⟩ := by
      apply Subtype.ext
      rw [hFmap, hFmap]
      change Scheme.Pic.map π t.val = Scheme.Pic.map π 1
      change Scheme.Pic.map π t.val = 1 at hp
      simpa only [← Scheme.Pic.mapHom_apply, map_one] using hp
    have ht := congrArg Subtype.val (hF.1 hFt)
    have ht' : E.symm x = 0 := ht
    simpa only [AddEquiv.apply_symm_apply, map_zero] using congrArg E ht'
  have hVsurj (y : P.CohomologicalPicardGroup) (hy : n • y = 0) :
      ∃ x : C.CohomologicalPicardGroup, n • x = 0 ∧ V x = y := by
    have hy' : (EP.symm y).toMul ^ n = 1 := by
      have h := congrArg EP.symm hy
      simp only [map_nsmul, map_zero] at h
      simpa only [toMul_nsmul, toMul_zero] using congrArg Additive.toMul h
    obtain ⟨t, ht⟩ := hF.2 ⟨(EP.symm y).toMul, hy'⟩
    refine ⟨E (Additive.ofMul t.val), ?_, ?_⟩
    · have h : n • (Additive.ofMul t.val : Additive C.Pic) = 0 := by
        simpa only [ofMul_pow, ofMul_one] using congrArg Additive.ofMul t.property
      rw [← map_nsmul, h, map_zero]
    · have hp := hFmap t
      rw [ht] at hp
      change (EP.symm y).toMul = Scheme.Pic.map π t.val at hp
      change EP (Additive.ofMul (Scheme.Pic.map π
        (E.symm (E (Additive.ofMul t.val))).toMul)) = y
      rw [AddEquiv.symm_apply_apply]
      change EP (Additive.ofMul (Scheme.Pic.map π t.val)) = y
      rw [← hp]
      exact EP.apply_symm_apply y
  have hβtor (x : Sheaf.H (C.rootsOfUnitySheaf n) 1) : n • β x = 0 := by
    have hm : β x ∈ (Sheaf.H.map (kernel.ι (n • 𝟙 C.gmSheaf)) 1).range := ⟨x, rfl⟩
    rw [hβ] at hm
    exact AddSubgroup.torsionBy.nsmul_iff.mp hm
  have hβPtor (y : Sheaf.H (P.rootsOfUnitySheaf n) 1) : n • βP y = 0 := by
    have hm : βP y ∈ (Sheaf.H.map (kernel.ι (n • 𝟙 P.gmSheaf)) 1).range := ⟨y, rfl⟩
    rw [hβP] at hm
    exact AddSubgroup.torsionBy.nsmul_iff.mp hm
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha⟩ := (hex x).mp hx
    obtain ⟨v, hv⟩ := proper_units_divisible f n hn a.toMul
    have hm : a ∈ α.ker := by
      rw [hα]
      exact ⟨Additive.ofMul v, by simpa [← ofMul_pow] using congrArg Additive.ofMul hv⟩
    change α a = 0 at hm
    exact ha.symm.trans hm
  have : IsProper (pullback.snd f b) := (baseChange_curve (k' := K) f).2.2.2.1 inferInstance
  have hdivP : ∀ a : Γ(P, ⊤)ˣ, ∃ v : Γ(P, ⊤)ˣ, v ^ n = a :=
    proper_units_divisible (pullback.snd f b) n hnK
  have hβPinj : Function.Injective βP := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, ha⟩ := (hexP y).mp hy
    obtain ⟨v, hv⟩ := hdivP a.toMul
    have hm : a ∈ αP.ker := by
      rw [hαP]
      exact ⟨Additive.ofMul v, by simpa [← ofMul_pow] using congrArg Additive.ofMul hv⟩
    change αP a = 0 at hm
    exact ha.symm.trans hm
  have hμ : Function.Bijective μ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      apply hβinj
      rw [map_zero]
      exact hVinj (β x) (hβtor x) (by rw [← hβnat, hx, map_zero])
    · intro y
      obtain ⟨d, hd, hdy⟩ := hVsurj (βP y) (hβPtor y)
      have hβ' : β.range = AddSubgroup.torsionBy C.CohomologicalPicardGroup n := hβ
      have hmem : d ∈ β.range := by
        rw [hβ']
        exact AddSubgroup.torsionBy.nsmul_iff.mpr hd
      obtain ⟨x, hx⟩ := hmem
      refine ⟨x, hβPinj ?_⟩
      rw [hβnat, hx, hdy]
  change Function.Bijective ((Sheaf.H.map φ.τ₁ 1).comp
    (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1))
  rw [← hτ]
  exact hμ


end AlgebraicGeometry
