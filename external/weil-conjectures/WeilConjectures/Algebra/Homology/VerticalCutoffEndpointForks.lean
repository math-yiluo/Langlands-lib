/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps

import all WeilConjectures.Algebra.Homology.VerticalCutoffComparisonEpi

/-!
# Boundary universal properties of nested vertical cutoffs

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations (3) and (4).
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma upper_boundary_kernel (K : CochainComplex C ℤ) (a : ℤ) :
    ∃ h : (K.ιTruncLE (a - 1)).f (a - 1) ≫ K.d (a - 1) a = 0,
      Nonempty (IsLimit (KernelFork.ofι ((K.ιTruncLE (a - 1)).f (a - 1)) h)) := by
  have hz : (K.ιTruncLE (a - 1)).f (a - 1) ≫ K.d (a - 1) a = 0 := by
    rw [← CochainComplex.truncLEXIsoCycles_comp_iCycles]
    simp
  refine ⟨hz, ⟨?_⟩⟩
  exact IsKernel.isoKernel _ _ (K.cyclesIsKernel (a - 1) a (by simp))
    (K.truncLEXIsoCycles (a - 1))
    (CochainComplex.truncLEXIsoCycles_comp_iCycles K (a - 1))

private lemma nested_upper_kernel (K : CochainComplex C ℤ) (a b : ℤ) (hab : a < b)
    {A : C} (f : A ⟶ (K.truncLE (b - 1)).X (a - 1))
    (e : A ≅ (K.truncLE (a - 1)).X (a - 1))
    (hf : f ≫ (K.ιTruncLE (b - 1)).f (a - 1) =
      e.hom ≫ (K.ιTruncLE (a - 1)).f (a - 1)) :
    ∃ h : f ≫ (K.truncLE (b - 1)).d (a - 1) a = 0,
      Nonempty (IsLimit (KernelFork.ofι f h)) := by
  let B := K.truncLE (b - 1)
  have : IsIso ((K.ιTruncLE (b - 1)).f (a - 1)) :=
    inclusion_f_isIso K (b - 1) (a - 1) (by omega)
  have : Mono ((K.ιTruncLE (b - 1)).f a) :=
    inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE K
      (ComplexShape.embeddingUpIntLE (b - 1))).f a))
  obtain ⟨hz, ⟨hk⟩⟩ := upper_boundary_kernel K a
  have hz' : f ≫ B.d (a - 1) a = 0 := by
    rw [← cancel_mono ((K.ιTruncLE (b - 1)).f a), Category.assoc,
      ← (K.ιTruncLE (b - 1)).comm, ← Category.assoc, hf, Category.assoc, hz,
      comp_zero, zero_comp]
  let h' := KernelFork.isLimitOfIsLimitOfIff hk (B.d (a - 1) a)
    (asIso ((K.ιTruncLE (b - 1)).f (a - 1))).symm (fun W φ ↦ by
      rw [← cancel_mono ((K.ιTruncLE (b - 1)).f a)]
      dsimp only [B, Iso.symm_hom, asIso_inv]
      simp only [Category.assoc]
      rw [← (K.ιTruncLE (b - 1)).comm]
      simp only [IsIso.inv_hom_id_assoc, zero_comp])
  refine ⟨hz', ⟨?_⟩⟩
  apply IsKernel.isoKernel _ _ h' e
  dsimp
  rw [← Category.assoc, ← hf]
  simp

private noncomputable def cokernel_post_iso {X Y Z Z' : C} {d : X ⟶ Y} (p : Y ⟶ Z)
    (hp : d ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hp)) (e : Z ≅ Z') :
    IsColimit (CokernelCofork.ofπ (f := d) (p ≫ e.hom) (by simp [← Category.assoc, hp])) := by
  exact IsColimit.ofIsoColimit hc (Cofork.ext e (by simp))

private lemma lower_boundary_cokernel (K : CochainComplex C ℤ) (a : ℤ) :
    ∃ h : K.d (a - 1) a ≫ (K.πTruncGE a).f a = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((K.πTruncGE a).f a) h)) := by
  rw [CochainComplex.pi_f_self]
  exact ⟨by simp, ⟨cokernel_post_iso _ _
    (K.opcyclesIsCokernel (a - 1) a (by simp)) (K.truncGEXIsoOpcycles a).symm⟩⟩

private lemma cycles_lower_boundary_cokernel (K : CochainComplex C ℤ) (a : ℤ) :
    ∃ h : K.toCycles (a - 1) a ≫ HomologicalComplex.cyclesMap (K.πTruncGE a) a = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        (HomologicalComplex.cyclesMap (K.πTruncGE a) a) h)) := by
  have hprev : (ComplexShape.up ℤ).prev a = a - 1 :=
    ComplexShape.prev_eq' _ (by simp)
  have hd : (K.truncGE a).d (a - 1) a = 0 :=
    ((K.truncGE a).isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _
  have : IsIso ((K.truncGE a).homologyπ a) :=
    (K.truncGE a).isIso_homologyπ (a - 1) a hprev hd
  have : QuasiIsoAt (K.πTruncGE a) a := K.quasiIsoAt_πTruncGE a a (by omega)
  have : IsIso (HomologicalComplex.homologyMap (K.πTruncGE a) a) := inferInstance
  let e := asIso (HomologicalComplex.homologyMap (K.πTruncGE a) a) ≪≫
    (asIso ((K.truncGE a).homologyπ a)).symm
  have he : K.homologyπ a ≫ e.hom = HomologicalComplex.cyclesMap (K.πTruncGE a) a := by
    dsimp [e]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    simp
  have hz : K.toCycles (a - 1) a ≫ HomologicalComplex.cyclesMap (K.πTruncGE a) a = 0 := by
    rw [← he, ← Category.assoc]
    simp
  refine ⟨hz, ⟨?_⟩⟩
  simpa only [he] using
    cokernel_post_iso _ _ (K.homologyIsCokernel (a - 1) a hprev) e

private lemma upper_projection_cokernel (K : CochainComplex C ℤ) (a t : ℤ)
    (hat : a ≤ t) :
    ∃ h : (K.truncLE t).d (a - 1) a ≫
        (CochainComplex.truncLEMap (K.πTruncGE a) t).f a = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((CochainComplex.truncLEMap (K.πTruncGE a) t).f a) h)) := by
  let B := K.truncLE t
  let Q := CochainComplex.truncLEMap (K.πTruncGE a) t
  have : IsIso ((K.ιTruncLE t).f (a - 1)) :=
    inclusion_f_isIso K t (a - 1) (by omega)
  by_cases h : a < t
  · have : IsIso ((K.ιTruncLE t).f a) := inclusion_f_isIso K t a h
    have : IsIso (((K.truncGE a).ιTruncLE t).f a) :=
      inclusion_f_isIso (K.truncGE a) t a h
    obtain ⟨hz, ⟨hc⟩⟩ := lower_boundary_cokernel K a
    have hc' := CokernelCofork.isColimitOfIsColimitOfIff hc (B.d (a - 1) a)
      (asIso ((K.ιTruncLE t).f a)) (fun W φ ↦ by
        dsimp only [B, asIso_hom]
        rw [← (K.ιTruncLE t).comm_assoc]
        rw [← cancel_epi ((K.ιTruncLE t).f (a - 1))]
        simp only [comp_zero])
    have hq : (K.ιTruncLE t).f a ≫ (K.πTruncGE a).f a =
        Q.f a ≫ ((K.truncGE a).ιTruncLE t).f a := by
      simpa only [HomologicalComplex.comp_f] using congrArg (fun f ↦ f.f a)
        (CochainComplex.ιTruncLE_naturality (K.πTruncGE a) t).symm
    have hc'' := cokernel_post_iso _ _ hc'
      (asIso (((K.truncGE a).ιTruncLE t).f a)).symm
    have he : ((K.ιTruncLE t).f a ≫ (K.πTruncGE a).f a) ≫
        inv (((K.truncGE a).ιTruncLE t).f a) = Q.f a := by
      rw [hq]
      simp
    refine ⟨?_, ⟨?_⟩⟩
    · rw [← cancel_mono (((K.truncGE a).ιTruncLE t).f a)]
      simp only [Category.assoc, zero_comp]
      rw [← hq, ← Category.assoc, ← (K.ιTruncLE t).comm, Category.assoc,
        hz, comp_zero]
    · simpa only [asIso_hom, Iso.symm_hom, asIso_inv, CokernelCofork.π_ofπ, he] using hc''
  · have hat' : t = a := by omega
    subst t
    obtain ⟨hz, ⟨hc⟩⟩ := cycles_lower_boundary_cokernel K a
    have hd : (K.truncLE a).d (a - 1) a ≫ (K.truncLEXIsoCycles a).hom =
        (K.ιTruncLE a).f (a - 1) ≫ K.toCycles (a - 1) a := by
      rw [← cancel_mono (K.iCycles a)]
      simp only [Category.assoc, CochainComplex.truncLEXIsoCycles_comp_iCycles,
        HomologicalComplex.toCycles_i]
      exact ((K.ιTruncLE a).comm (a - 1) a).symm
    have hc' := CokernelCofork.isColimitOfIsColimitOfIff hc
      ((K.truncLE a).d (a - 1) a) (K.truncLEXIsoCycles a) (fun W φ ↦ by
        rw [← Category.assoc, hd]
        rw [← cancel_epi ((K.ιTruncLE a).f (a - 1))]
        simp only [Category.assoc, comp_zero])
    have hc'' := cokernel_post_iso _ _ hc' ((K.truncGE a).truncLEXIsoCycles a).symm
    have he : (K.truncLEXIsoCycles a).hom ≫
        HomologicalComplex.cyclesMap (K.πTruncGE a) a ≫
        ((K.truncGE a).truncLEXIsoCycles a).inv =
        (CochainComplex.truncLEMap (K.πTruncGE a) a).f a := by
      rw [← Category.assoc, ← CochainComplex.truncLEXIsoCycles_naturality]
      simp
    refine ⟨?_, ⟨?_⟩⟩
    · rw [← he, ← Category.assoc, ← Category.assoc, hd]
      simp only [Category.assoc]
      rw [← Category.assoc (K.toCycles (a - 1) a), hz, zero_comp, comp_zero]
    · simpa only [Category.assoc, Iso.symm_hom, CokernelCofork.π_ofπ, he] using hc''

/-- The boundary inclusion is a kernel, and the boundary comparison is a cokernel.
Source: Stacks Project, Tag 0118 (homology-section-truncations), canonical
truncations (3) and (4); the specialization to the upper cutoff is explicit.
(blueprint: lem-sp-vertical-cutoff-endpoint-forks)

Proof: put E = L extended by zero, B = tau-le-(b-1) E, and m = a-1.
The inclusion of tau-le-m E into B in degree m is the kernel of B.d m a:
B agrees with E in degree m, and its inclusion into E is mono in degree a.
The cycles object of E at m is the kernel of E.d m a. Naturality and the
factorization equation for g give precisely this kernel inclusion, so transport
that kernel fork through the invertible degree-m inclusion of B. Restriction
preserves the coordinates because a>0.
For the cokernel fork, if a<b-1 then B agrees with E in degree a. The comparison
at a is the opcycles projection, the cokernel of E.d m a, conjugated by the
canonical truncation isomorphisms. If a=b-1, B.X a is cycles of E at a and the
window component is homology of E at a. Its comparison is cycles to homology,
the cokernel of the differential into cycles. The chain condition puts the
image of E.d m a in cycles. Transport these cokernel forks through the
truncation isomorphisms. The equations of both forks follow from chain-map
compatibility and the zero terms of the lower cutoff and window, respectively.
For a=1 the surviving indices are 0 and 1. For zero differential both forks
are the usual kernel of zero and cokernel of zero, so no nonzero-object
hypothesis is needed. -/
theorem verticalCutoff_endpoint_forks
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L) :
    (∃ h : g.f (a.toNat - 1) ≫
        ((verticalCutoff b).obj L).d (a.toNat - 1) a.toNat = 0,
      Nonempty (IsLimit (KernelFork.ofι (g.f (a.toNat - 1)) h))) ∧
    (∃ h : ((verticalCutoff b).obj L).d (a.toNat - 1) a.toNat ≫
        (HomologicalComplex.restrictionMap
          (CochainComplex.truncLEMap
            (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
          ComplexShape.embeddingUpNat).f a.toNat = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((HomologicalComplex.restrictionMap
          (CochainComplex.truncLEMap
            (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
          ComplexShape.embeddingUpNat).f a.toNat) h))) := by
  let E : CochainComplex C ℤ := L.extend ComplexShape.embeddingUpNat
  let A : CochainComplex C ℤ := E.truncLE (a - 1)
  let B : CochainComplex C ℤ := E.truncLE (b - 1)
  let W : CochainComplex C ℤ := (E.truncGE a).truncLE (b - 1)
  let r := CochainComplex.truncLEMap (E.πTruncGE a) (b - 1)
  let m := a.toNat - 1
  let n := a.toNat
  have hm : ComplexShape.embeddingUpNat.f m = a - 1 := by
    change (m : ℤ) = a - 1
    dsimp [m]
    omega
  have hn : ComplexShape.embeddingUpNat.f n = a := by
    change (n : ℤ) = a
    dsimp [n]
    omega
  let eA := A.restrictionXIso ComplexShape.embeddingUpNat hm
  let eB := B.restrictionXIso ComplexShape.embeddingUpNat hm
  let eN := B.restrictionXIso ComplexShape.embeddingUpNat hn
  let eW := W.restrictionXIso ComplexShape.embeddingUpNat hn
  have hgf : g.f m ≫ eB.hom ≫ (E.ιTruncLE (b - 1)).f (a - 1) =
      eA.hom ≫ (E.ιTruncLE (a - 1)).f (a - 1) := by
    have h := congrArg (fun f ↦ f.f m) hg
    change g.f m ≫ (HomologicalComplex.restrictionMap
      (E.ιTruncLE (b - 1)) ComplexShape.embeddingUpNat).f m =
      (HomologicalComplex.restrictionMap
        (E.ιTruncLE (a - 1)) ComplexShape.embeddingUpNat).f m at h
    rw [HomologicalComplex.restrictionMap_f' _ _ hm,
      HomologicalComplex.restrictionMap_f' _ _ hm] at h
    exact (cancel_mono (E.restrictionXIso ComplexShape.embeddingUpNat hm).inv).mp
      (by simpa only [Category.assoc] using h)
  obtain ⟨hk₀, ⟨hk⟩⟩ := nested_upper_kernel E a b hab (g.f m ≫ eB.hom) eA
    (by simpa only [Category.assoc] using hgf)
  have hd : ((verticalCutoff b).obj L).d m n =
      eB.hom ≫ B.d (a - 1) a ≫ eN.inv :=
    B.restriction_d_eq ComplexShape.embeddingUpNat hm hn
  have hk₀' : g.f m ≫ ((verticalCutoff b).obj L).d m n = 0 := by
    rw [hd, ← Category.assoc, ← Category.assoc, hk₀, zero_comp]
  have hk' := KernelFork.isLimitOfIsLimitOfIff hk
    (((verticalCutoff b).obj L).d m n) eB.symm (fun T φ ↦ by
      rw [hd]
      simp only [Iso.symm_hom, Iso.inv_hom_id_assoc]
      rw [← cancel_mono eN.inv]
      simp only [Category.assoc, zero_comp]
      rfl)
  have hki : (g.f m ≫ eB.hom) ≫ eB.symm.hom = g.f m := by simp
  have hkernel : Nonempty (IsLimit (KernelFork.ofι (g.f m) hk₀')) := by
    exact ⟨by simpa only [KernelFork.ι_ofι, hki] using hk'⟩
  obtain ⟨hr₀, ⟨hr⟩⟩ := upper_projection_cokernel E a (b - 1) (by omega)
  have hdr : (HomologicalComplex.restrictionMap r ComplexShape.embeddingUpNat).f n =
      eN.hom ≫ r.f a ≫ eW.inv :=
    HomologicalComplex.restrictionMap_f' r ComplexShape.embeddingUpNat hn
  have hr₀' : ((verticalCutoff b).obj L).d m n ≫
      (HomologicalComplex.restrictionMap r ComplexShape.embeddingUpNat).f n = 0 := by
    rw [hd, hdr]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (B.d (a - 1) a), hr₀, zero_comp, comp_zero]
  have hr' := CokernelCofork.isColimitOfIsColimitOfIff hr
    (((verticalCutoff b).obj L).d m n) eN (fun T φ ↦ by
      rw [hd]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← cancel_epi eB.hom]
      simp only [comp_zero]
      rfl)
  have hr'' := cokernel_post_iso _ _ hr' eW.symm
  change IsColimit (CokernelCofork.ofπ (f := ((verticalCutoff b).obj L).d m n)
    ((eN.hom ≫ r.f a) ≫ eW.inv) _) at hr''
  have hcokernel : Nonempty (IsColimit (CokernelCofork.ofπ
      ((HomologicalComplex.restrictionMap r ComplexShape.embeddingUpNat).f n) hr₀')) := by
    exact ⟨by simpa only [Category.assoc, ← hdr] using hr''⟩
  exact ⟨⟨hk₀', hkernel⟩, ⟨hr₀', hcokernel⟩⟩

end HomologicalComplex₂
