/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility
import WeilConjectures.AlgebraicGeometry.Curve.UnitsQuotientBaseChange
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Affine Kummer degree-one base change

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, affine case in degree
one (blueprint: lem-sc-affine-kummer-degree-one-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

private theorem boundary_eq_of_quotient_eq {A B : Type*} [CommGroup A] [AddCommGroup B]
    (n : ℕ) (α : Additive A →+ B)
    (hker : α.ker = (zsmulAddGroupHom (α := Additive A) (n : ℤ)).range)
    {a b : A} (hab : (QuotientGroup.mk a : A ⧸ (powMonoidHom n : A →* A).range) =
      QuotientGroup.mk b) : α (Additive.ofMul a) = α (Additive.ofMul b) := by
  obtain ⟨v, hv⟩ := QuotientGroup.eq_iff_div_mem.mp hab
  have hz : Additive.ofMul (a / b) ∈ α.ker := by
    rw [hker]
    exact ⟨Additive.ofMul v, by simpa using congrArg Additive.ofMul hv⟩
  change α (Additive.ofMul (a / b)) = 0 at hz
  simpa only [ofMul_div, map_sub, sub_eq_zero] using hz

private theorem quotient_eq_one_of_boundary_zero {A B : Type*}
    [CommGroup A] [AddCommGroup B] (n : ℕ) (α : Additive A →+ B)
    (hker : α.ker = (zsmulAddGroupHom (α := Additive A) (n : ℤ)).range)
    {a : A} (ha : α (Additive.ofMul a) = 0) :
    (QuotientGroup.mk a : A ⧸ (powMonoidHom n : A →* A).range) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  have hm : Additive.ofMul a ∈ α.ker := ha
  rw [hker] at hm
  obtain ⟨v, hv⟩ := hm
  refine ⟨v.toMul, ?_⟩
  change v.toMul ^ n = a
  have hv' : n • v = Additive.ofMul a := by simpa using hv
  simpa only [toMul_nsmul, toMul_ofMul] using congrArg Additive.toMul hv'

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, affine case in
degree one (blueprint: lem-sc-affine-kummer-degree-one-base-change).

Proof: The Kummer sequence gives short exact sequences with outer terms units modulo
n-th powers and Picard n-torsion. Kummer naturality makes pullback a commuting
ladder. The units quotient comparison is bijective by units_quotient_base_change.
The affine clause of kummer_base_change_compatibility gives bijectivity on Picard
n-torsion. The short five lemma gives bijectivity on the middle H¹(mu_n) term.
The condition on the second component fixes the first component uniquely, since
the roots-of-unity inclusion into Gm is monic, so the assertion holds for every φ
with the displayed condition. This also covers n = 1, when all three terms vanish. -/
theorem IsConnectedCurve.affine_kummer_degree_one_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
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
        (C.rootsOfUnitySheaf n) 1))  := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let P := pullback f b
  let π := pullback.fst f b
  obtain ⟨hC, hP, ψ, hψ₂, hψ₃, hδ, hι, _, hPic, hUnits, hAff⟩ :=
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
  let U : Γ(C, ⊤)ˣ →* Γ(P, ⊤)ˣ := Units.map π.appTop.hom.toMonoidHom
  have hαnat (a : Additive Γ(C, ⊤)ˣ) : μ (α a) = αP (Additive.ofMul (U a.toMul)) := by
    let z := (Sheaf.H.equiv₀ C.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale C)).symm (ULift.up a)
    have hz : α a = Sheaf.H.δSucc hC 0 z := by
      have he := (Sheaf.H.equiv₀ C.gmSheaf
        (MorphismProperty.Over.mkIdTerminal @Etale C)).apply_symm_apply (ULift.up a)
      have hd := Sheaf.H.δSucc_zero hC
        (MorphismProperty.Over.mkIdTerminal @Etale C) z
      change Sheaf.H.δSections (C.kummerSequence_shortExact n hnC)
        (MorphismProperty.Over.mkIdTerminal @Etale C) (ULift.up a) = _
      change Sheaf.H.δSucc hC 0 z =
        Sheaf.H.δSections hC (MorphismProperty.Over.mkIdTerminal @Etale C)
          (Sheaf.H.equiv₀ C.gmSheaf
            (MorphismProperty.Over.mkIdTerminal @Etale C) z) at hd
      exact (hd.trans (congrArg
        (Sheaf.H.δSections hC (MorphismProperty.Over.mkIdTerminal @Etale C)) he)).symm
    change Sheaf.H.map ψ.τ₁ 1
      (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1 (α a)) = _
    rw [hz, hδ 0, hψ₃]
    have hu := hUnits a.toMul
    have hd := Sheaf.H.δSucc_zero hP (MorphismProperty.Over.mkIdTerminal @Etale P)
      (Sheaf.H.map (upperStarGmSheafToGmSheaf π) 0 (Etale.cohomologyMap π C.gmSheaf 0 z))
    exact hd.trans (congrArg
      (Sheaf.H.δSections hP (MorphismProperty.Over.mkIdTerminal @Etale P)) hu)
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
  obtain ⟨e, he⟩ := units_quotient_base_change k K C f n (NeZero.one_le)
  obtain ⟨F, hF, hFmap⟩ := hAff inferInstance
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
  have hαinj (a : Additive Γ(C, ⊤)ˣ) (ha : αP (Additive.ofMul (U a.toMul)) = 0) :
      α a = 0 := by
    have hz := quotient_eq_one_of_boundary_zero n αP hαP ha
    have hq : e (QuotientGroup.mk a.toMul) = e 1 := by
      rw [he, map_one]
      exact hz
    have hqa := e.injective hq
    have h := boundary_eq_of_quotient_eq n α hα hqa
    simpa using h
  have hαsurj (aP : Additive Γ(P, ⊤)ˣ) : ∃ a : Additive Γ(C, ⊤)ˣ,
      μ (α a) = αP aP := by
    obtain ⟨q, hq⟩ := e.surjective (QuotientGroup.mk aP.toMul)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rw [he] at hq
    refine ⟨Additive.ofMul a, ?_⟩
    rw [hαnat]
    exact boundary_eq_of_quotient_eq n αP hαP hq
  have hμ : Function.Bijective μ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hbx : β x = 0 := hVinj (β x) (hβtor x) (by
        rw [← hβnat, hx, map_zero])
      obtain ⟨a, ha⟩ := (hex x).mp hbx
      change α a = x at ha
      rw [← ha] at hx ⊢
      apply hαinj
      rw [← hαnat]
      exact hx
    · intro y
      obtain ⟨d, hd, hdy⟩ := hVsurj (βP y) (hβPtor y)
      have hβ' : β.range = AddSubgroup.torsionBy C.CohomologicalPicardGroup n := hβ
      have hmem : d ∈ β.range := by
        rw [hβ']
        exact AddSubgroup.torsionBy.nsmul_iff.mpr hd
      obtain ⟨x, hx⟩ := hmem
      change β x = d at hx
      have hz : βP (y - μ x) = 0 := by
        rw [map_sub, hβnat, hx, hdy, sub_self]
      obtain ⟨aP, haP⟩ := (hexP (y - μ x)).mp hz
      change αP aP = y - μ x at haP
      obtain ⟨a, ha⟩ := hαsurj aP
      refine ⟨x + α a, ?_⟩
      rw [map_add, ha, haP]
      abel
  change Function.Bijective ((Sheaf.H.map φ.τ₁ 1).comp
    (Etale.cohomologyMap π (C.rootsOfUnitySheaf n) 1))
  rw [← hτ]
  exact hμ

end AlgebraicGeometry
