/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffEndpointForks
import all WeilConjectures.Algebra.Homology.VerticalCutoffComparisonEpi
import all WeilConjectures.Algebra.Homology.LowerTruncationTransitionKernel
import all WeilConjectures.Algebra.Homology.UpperTruncationStepSES

/-!
# Endpoint calculation for the strict vertical cutoff comparison

Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations and the two-term kernel argument.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma cutoff_projection_iso_above (K : CochainComplex C ℤ) (a t n : ℤ)
    (han : a < n) :
    IsIso ((CochainComplex.truncLEMap (K.πTruncGE a) t).f n) := by
  by_cases hn : t < n
  · have hsrc := (K.truncLE t).isZero_of_isStrictlyLE t n hn
    have htgt := ((K.truncGE a).truncLE t).isZero_of_isStrictlyLE t n hn
    exact IsZero.isIso hsrc htgt _
  · by_cases hn' : n < t
    · have : IsIso ((K.ιTruncLE t).f n) := inclusion_f_isIso K t n hn'
      have : IsIso (((K.truncGE a).ιTruncLE t).f n) :=
        inclusion_f_isIso (K.truncGE a) t n hn'
      have : IsIso ((K.πTruncGE a).f n) := by
        rw [CochainComplex.pi_f_above K a n han]
        infer_instance
      have h := congrArg (fun f ↦ f.f n)
        (CochainComplex.ιTruncLE_naturality (K.πTruncGE a) t)
      simp only [HomologicalComplex.comp_f] at h
      have : IsIso ((CochainComplex.truncLEMap (K.πTruncGE a) t).f n ≫
          ((K.truncGE a).ιTruncLE t).f n) := by
        rw [h]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (((K.truncGE a).ιTruncLE t).f n)
    · have hnt : n = t := by omega
      subst n
      have hnext : (ComplexShape.up ℤ).next t = t + 1 :=
        ComplexShape.next_eq' _ (by simp)
      let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) t).map
        (K.πTruncGE a)
      have : IsIso φ.τ₂ := by
        change IsIso ((K.πTruncGE a).f t)
        rw [CochainComplex.pi_f_above K a t han]
        infer_instance
      have : Mono φ.τ₃ := by
        change Mono ((K.πTruncGE a).f ((ComplexShape.up ℤ).next t))
        rw [hnext, CochainComplex.pi_f_above K a (t + 1) (by omega)]
        infer_instance
      have : IsIso (HomologicalComplex.cyclesMap (K.πTruncGE a) t) :=
        inferInstanceAs (IsIso (ShortComplex.cyclesMap φ))
      have : IsIso ((CochainComplex.truncLEMap (K.πTruncGE a) t).f t ≫
          ((K.truncGE a).truncLEXIsoCycles t).hom) := by
        rw [CochainComplex.truncLEXIsoCycles_naturality]
        infer_instance
      exact IsIso.of_isIso_comp_right _ ((K.truncGE a).truncLEXIsoCycles t).hom

set_option backward.isDefEq.respectTransparency false in
private lemma kernel_d_isIso_of_endpoint_forks
    {A B W : CochainComplex C ℕ} (g : A ⟶ B) (q : cokernel g ⟶ W)
    (m n : ℕ) (hA : IsZero (A.X n)) (hW : IsZero (W.X m))
    (hk₀ : g.f m ≫ B.d m n = 0)
    (hk : IsLimit (KernelFork.ofι (g.f m) hk₀))
    (hr₀ : B.d m n ≫ ((cokernel.π g).f n ≫ q.f n) = 0)
    (hr : IsColimit (CokernelCofork.ofπ ((cokernel.π g).f n ≫ q.f n) hr₀)) :
    IsIso ((kernel q).d m n) := by
  let f := B.d m n
  let p := cokernel.π g
  let i := kernel.ι q
  have hc (r : ℕ) : IsColimit (CokernelCofork.ofπ (p.f r)
      (show g.f r ≫ p.f r = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun t ↦ t.f r) (cokernel.condition g))) :=
    isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval C (ComplexShape.up ℕ) r)
      (cokernel.condition g) (cokernelIsCokernel g)
  have hi (r : ℕ) : IsLimit (KernelFork.ofι (i.f r)
      (show i.f r ≫ q.f r = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun t ↦ t.f r) (kernel.condition q))) :=
    isLimitForkMapOfIsLimit' (HomologicalComplex.eval C (ComplexShape.up ℕ) r)
      (kernel.condition q) (kernelIsKernel q)
  have : IsIso (p.f n) :=
    CokernelCofork.IsColimit.isIso_π _ (hc n) (hA.eq_of_src _ _)
  have : IsIso (i.f m) :=
    KernelFork.IsLimit.isIso_ι _ (hi m) (hW.eq_of_tgt _ _)
  let ek := IsLimit.conePointUniqueUpToIso hk (kernelIsKernel f)
  have hek : ek.hom ≫ kernel.ι f = g.f m :=
    IsLimit.conePointUniqueUpToIso_hom_comp hk (kernelIsKernel f)
      WalkingParallelPair.zero
  have hc' : IsColimit (CokernelCofork.ofπ (p.f m)
      (show kernel.ι f ≫ p.f m = 0 by
        rw [← cancel_epi ek.hom, ← Category.assoc, hek, comp_zero]
        exact (CokernelCofork.ofπ (p.f m) (by
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
            congrArg (fun t ↦ t.f m) (cokernel.condition g))).condition)) := by
    apply CokernelCofork.isColimitOfIsColimitOfIff' (hc m) (kernel.ι f)
    intro V v
    rw [← cancel_epi ek.hom, ← Category.assoc, hek, comp_zero]
  let ec := IsColimit.coconePointUniqueUpToIso hc' (cokernelIsCokernel (kernel.ι f))
  have hec : p.f m ≫ ec.hom = Abelian.coimage.π f :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc'
      (cokernelIsCokernel (kernel.ι f)) WalkingParallelPair.one
  let er := IsColimit.coconePointUniqueUpToIso hr (cokernelIsCokernel f)
  have her : p.f n ≫ q.f n ≫ er.hom = cokernel.π f := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hr (cokernelIsCokernel f)
      WalkingParallelPair.one
    change (p.f n ≫ q.f n) ≫ er.hom = cokernel.π f at h
    simpa only [Category.assoc] using h
  have him : IsLimit (KernelFork.ofι (i.f n ≫ inv (p.f n))
      (show (i.f n ≫ inv (p.f n)) ≫ cokernel.π f = 0 by
        rw [← her]
        simp only [Category.assoc, IsIso.inv_hom_id_assoc]
        have h : i.f n ≫ q.f n = 0 := by
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
            congrArg (fun t ↦ t.f n) (kernel.condition q)
        rw [← Category.assoc, h, zero_comp])) := by
    apply KernelFork.isLimitOfIsLimitOfIff (hi n) (cokernel.π f) (asIso (p.f n)).symm
    intro V v
    simp only [Iso.symm_hom, asIso_inv, ← her, IsIso.inv_hom_id_assoc]
    constructor
    · intro h
      simp only [← Category.assoc, h, zero_comp]
    · intro h
      apply (cancel_mono er.hom).mp
      simpa only [Category.assoc, zero_comp] using h
  let ei :=
    IsLimit.conePointUniqueUpToIso him (kernelIsKernel (cokernel.π f))
  have hei : ei.hom ≫ Abelian.image.ι f = i.f n ≫ inv (p.f n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp him (kernelIsKernel (cokernel.π f))
      WalkingParallelPair.zero
  let e₀ : (kernel q).X m ≅ Abelian.coimage f := asIso (i.f m) ≪≫ ec
  have hd : e₀.inv ≫ (kernel q).d m n ≫ ei.hom ≫ Abelian.image.ι f =
      Abelian.factorThruCoimage f := by
    apply (cancel_epi (Abelian.coimage.π f)).mp
    rw [Abelian.coimage.fac, ← hec]
    simp only [e₀, Iso.trans_inv, asIso_inv, Category.assoc, Iso.hom_inv_id_assoc]
    rw [hei, ← i.comm_assoc m n]
    simp only [IsIso.inv_hom_id_assoc]
    rw [p.comm_assoc m n]
    simp only [IsIso.hom_inv_id, Category.comp_id]
    rfl
  have hd' : e₀.inv ≫ (kernel q).d m n ≫ ei.hom =
      Abelian.coimageImageComparison f := by
    apply (cancel_mono (Abelian.image.ι f)).mp
    simp only [Category.assoc]
    rw [hd]
    apply (cancel_epi (Abelian.coimage.π f)).mp
    rw [Abelian.coimage.fac, Abelian.coimage_image_factorisation]
  have : IsIso (e₀.inv ≫ (kernel q).d m n ≫ ei.hom) := by
    rw [hd']
    infer_instance
  have : IsIso ((kernel q).d m n ≫ ei.hom) :=
    IsIso.of_isIso_comp_left e₀.inv _
  exact IsIso.of_isIso_comp_right _ ei.hom

private lemma cutoff_kernel_isZero_away
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat)
    (n : ℕ) (h₀ : n ≠ a.toNat - 1) (h₁ : n ≠ a.toNat) :
    IsZero ((kernel q).X n) := by
  let E : CochainComplex C ℤ := L.extend ComplexShape.embeddingUpNat
  have hker : IsLimit (KernelFork.ofι ((kernel.ι q).f n)
      (show (kernel.ι q).f n ≫ q.f n = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun f ↦ f.f n) (kernel.condition q))) :=
    isLimitForkMapOfIsLimit' (HomologicalComplex.eval C (ComplexShape.up ℕ) n)
      (kernel.condition q) (kernelIsKernel q)
  have hcoker : IsColimit (CokernelCofork.ofπ ((cokernel.π g).f n)
      (show g.f n ≫ (cokernel.π g).f n = 0 by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun f ↦ f.f n) (cokernel.condition g))) :=
    isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval C (ComplexShape.up ℕ) n)
      (cokernel.condition g) (cokernelIsCokernel g)
  by_cases hn : (n : ℤ) < a - 1
  · have hi (c : ℤ) (hc : (n : ℤ) < c - 1) :
        IsIso (((verticalCutoffι c).app L).f n) := by
      change IsIso ((E.ιTruncLE (c - 1)).f (n : ℤ))
      exact inclusion_f_isIso E (c - 1) n hc
    have := hi a hn
    have := hi b (by omega)
    have heq := congrArg (fun f ↦ f.f n) hg
    simp only [HomologicalComplex.comp_f] at heq
    have : IsIso (g.f n ≫ ((verticalCutoffι b).app L).f n) := by
      rw [heq]
      infer_instance
    have : IsIso (g.f n) :=
      IsIso.of_isIso_comp_right (g.f n) (((verticalCutoffι b).app L).f n)
    have hz := CokernelCofork.IsColimit.isZero_of_epi hcoker
    exact IsZero.of_mono ((kernel.ι q).f n) hz
  · have han : a < (n : ℤ) := by omega
    have hzero : IsZero (((verticalCutoff a).obj L).X n) := by
      change IsZero ((E.truncLE (a - 1)).X (n : ℤ))
      exact E.truncLE (a - 1) |>.isZero_of_isStrictlyLE (a - 1) n (by omega)
    have hgzero : g.f n = 0 := hzero.eq_of_src _ _
    have : IsIso ((cokernel.π g).f n) :=
      CokernelCofork.IsColimit.isIso_π _ hcoker hgzero
    have h := congrArg (fun f ↦ f.f n) hq
    simp only [HomologicalComplex.comp_f] at h
    have hmap : IsIso ((HomologicalComplex.restrictionMap
        (CochainComplex.truncLEMap (E.πTruncGE a) (b - 1))
        ComplexShape.embeddingUpNat).f n) :=
      cutoff_projection_iso_above E a (b - 1) n han
    have : IsIso ((cokernel.π g).f n ≫ q.f n) := by
      rw [h]
      exact hmap
    have : IsIso (q.f n) := IsIso.of_isIso_comp_left ((cokernel.π g).f n) (q.f n)
    exact KernelFork.IsLimit.isZero_of_mono hker

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the strict cutoff comparison is a two-term complex
with invertible differential.
Source: Stacks Project, Homology Tag 0118 (homology-section-truncations),
canonical truncations; the kernel identification is explicit.
(blueprint: lem-sp-vertical-cutoff-comparison-kernel-two-term)

Proof: write E for L extended by zero and I for image of E.d (a - 1) a.
Monicity of the upper cutoff inclusion identifies g with the nested inclusion.
Evaluation preserves cokernels. Thus cokernel g is zero below a - 1, is I
in degree a - 1, and agrees with the upper cutoff from degree a onward.
By hq, the comparison is zero in degree a - 1. At degree a it is the
opcycles quotient when a < b - 1, and the cycles-to-homology quotient when
a = b - 1. Both have kernel I. Above a, q is invertible on the nonzero
components; beyond the upper cutoff both sides are zero. Evaluation preserves
kernels, so the kernel has I in degrees a - 1 and a and zero elsewhere.
The chain map equation for the kernel inclusion identifies its differential
with the identity on I, using the image factorization of E.d (a - 1) a.
It is therefore invertible. Since 0 < a, both indices are nonnegative and
restriction preserves them: they are a.toNat - 1 and a.toNat. For a = 1
these are 0 and 1; for b = a + 1 the image lies in cycles because d squared
is zero. Zero I gives the invertible zero-to-zero differential as required. -/
theorem verticalCutoff_comparison_kernel_twoTerm
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b) (ha : 0 < a)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) :
    (∀ n, n ≠ a.toNat - 1 → n ≠ a.toNat → IsZero ((kernel q).X n)) ∧
      IsIso ((kernel q).d (a.toNat - 1) a.toNat) := by
  refine ⟨cutoff_kernel_isZero_away L a b hab ha g hg q hq, ?_⟩
  obtain ⟨⟨hk₀, ⟨hk⟩⟩, ⟨hr₀, ⟨hr⟩⟩⟩ := verticalCutoff_endpoint_forks L a b hab ha g hg
  have hA : IsZero (((verticalCutoff a).obj L).X a.toNat) := by
    change IsZero ((CochainComplex.truncLE (L.extend ComplexShape.embeddingUpNat)
      (a - 1)).X (a.toNat : ℤ))
    exact CochainComplex.isZero_of_isStrictlyLE _ (a - 1) _ (by omega)
  have hW : IsZero (((verticalWindow a b).obj L).X (a.toNat - 1)) := by
    change IsZero ((CochainComplex.truncLE
      (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1)).X
      ((a.toNat - 1 : ℕ) : ℤ))
    have hz : IsZero ((CochainComplex.truncGE
        (L.extend ComplexShape.embeddingUpNat) a).X ((a.toNat - 1 : ℕ) : ℤ)) :=
      CochainComplex.isZero_of_isStrictlyGE _ a _ (by omega)
    have : Mono ((CochainComplex.ιTruncLE
        (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a)
        (b - 1)).f ((a.toNat - 1 : ℕ) : ℤ)) :=
      inferInstanceAs (Mono ((HomologicalComplex.ιTruncLE
        (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a)
        (ComplexShape.embeddingUpIntLE (b - 1))).f ((a.toNat - 1 : ℕ) : ℤ)))
    exact IsZero.of_mono
      ((CochainComplex.ιTruncLE
        (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) a)
        (b - 1)).f ((a.toNat - 1 : ℕ) : ℤ)) hz
  have h := congrArg (fun f ↦ f.f a.toNat) hq
  simp only [HomologicalComplex.comp_f] at h
  have hr₀' : ((verticalCutoff b).obj L).d (a.toNat - 1) a.toNat ≫
      ((cokernel.π g).f a.toNat ≫ q.f a.toNat) = 0 := by
    simpa only [← h] using hr₀
  have hr' : IsColimit (CokernelCofork.ofπ
      ((cokernel.π g).f a.toNat ≫ q.f a.toNat) hr₀') := by
    simpa only [← h] using hr
  exact kernel_d_isIso_of_endpoint_forks g q (a.toNat - 1) a.toNat hA hW
    hk₀ hk hr₀' hr'

end HomologicalComplex₂
