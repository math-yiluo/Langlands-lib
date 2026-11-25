/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.FormalCompletionExact
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Detection of formal maps by a torsion comparison and one quotient

Source: Stacks Project, Tags 0889 and 088A, uniqueness argument;
Tag 0881, exactness of coherent completion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

private theorem kernel_quotient_projection_isIso
    {X : Scheme.{u}} (J : X.IdealSheafData)
    {Q R : X.Modules} (b : Q ⟶ R) (n : ℕ)
    (hsep : Mono (kernel.ι b ≫ formalModuleQuotientπ J (n + 1) Q))
    (m : ℕ) (hm : n ≤ m) :
    IsIso (formalModuleQuotientπ J (m + 1) (kernel b)) := by
  let := hsep
  let r := formalModuleQuotientMap J (kernel.ι b) (Nat.add_le_add_right hm 1)
  have hr : formalModuleQuotientπ J (m + 1) (kernel b) ≫ r =
      kernel.ι b ≫ formalModuleQuotientπ J (n + 1) Q := by
    simp [r, formalModuleQuotientπ, formalModuleQuotientMap]
  have : Mono (formalModuleQuotientπ J (m + 1) (kernel b)) := mono_of_mono_fac hr
  have : Epi (formalModuleQuotientπ J (m + 1) (kernel b)) :=
    inferInstanceAs (Epi (cokernel.π _))
  exact isIso_of_mono_of_epi _

/-- One separating quotient detects the difference of two formal maps into Q
whose composites with b agree.
Source: Stacks Project, Tags 0889 and 088A, uniqueness argument.
Proof: let T be the coherent kernel of b. The map T → Q/J^(n+1)Q factors
through T/J^(m+1)T for every m ≥ n. Since it is monomorphic, the quotient
projection of T is monomorphic as well as epimorphic, hence invertible. Thus
the completion of T has invertible transitions at and above n. Exactness of
coherent completion (Stacks, Tag 0881) transports the kernel fork T → Q → R
to a kernel fork in the formal category. The difference f - g therefore factors
through the completion of T. At level n, precompose the separating map with
this factor followed by the inverse quotient projection. The resulting composite
is f_n - g_n = 0, so the factor at n is zero. Naturality and invertible kernel
transitions give zero at all higher levels. At lower levels cancel the epimorphic
transition of M from n to that level. All components of the factor vanish, hence
f - g = 0. The bound hker is unnecessary once hsep is given, but its original
binder is retained. For J=0 the quotients are the original modules; for the unit
ideal hsep forces T=0. No termwise preservation of kernels is asserted.
(blueprint: lem-weil-pbc-formal-map-torsion-finite-detection). -/
theorem formalMap_torsion_finite_detection
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (Q R : CoherentModules X) (b : Q ⟶ R)
    (hker : ∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel b.hom)))
    (n : ℕ) (hsep : Mono (kernel.ι b.hom ≫ formalModuleQuotientπ J (n + 1) Q.obj))
    (M : CoherentFormalModule X J) (f g : M ⟶ (completion X J).obj Q)
    (hcomp : f ≫ (completion X J).map b = g ≫ (completion X J).map b)
    (hlevel : f.hom.app (op n) = g.hom.app (op n)) : f = g := by
  classical
  have _ := hker
  let zC : HasZeroMorphisms (CoherentModules X) := inferInstance
  let zD : HasZeroMorphisms (CoherentFormalModule X J) := inferInstance
  obtain ⟨hC, hD, hAdd, hExact⟩ := formalCompletion_exact X J
  let _ : Abelian (CoherentModules X) := hC.some
  let _ : Abelian (CoherentFormalModule X J) := hD.some
  let _ : Subsingleton (Preadditive (CoherentModules X)) :=
    @CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts _ _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ hC.some.toPreadditive)
      (@Abelian.hasBinaryBiproducts _ _ hC.some)
  let _ : Subsingleton (Preadditive (CoherentFormalModule X J)) :=
    @CategoryTheory.subsingleton_preadditive_of_hasBinaryBiproducts _ _
      (@Preadditive.preadditiveHasZeroMorphisms _ _ hD.some.toPreadditive)
      (@Abelian.hasBinaryBiproducts _ _ hD.some)
  let hAdd' : @Functor.Additive _ _ _ _ hC.some.toPreadditive hD.some.toPreadditive
      (completion X J) := by
    convert hAdd using 1
  let _ := hAdd'
  have hPres : PreservesFiniteLimits (completion X J) ∧
      PreservesFiniteColimits (completion X J) := by
    apply ((Functor.exact_tfae (completion X J)).out 1 4).mp
    let P (z₁ : HasZeroMorphisms (CoherentModules X))
        (z₂ : HasZeroMorphisms (CoherentFormalModule X J)) : Prop :=
      ∀ hz : @Functor.PreservesZeroMorphisms _ _ _ _ z₁ z₂ (completion X J),
        ∀ S : @ShortComplex (CoherentModules X) _ z₁,
          @ShortComplex.ShortExact _ _ z₁ S →
            @ShortComplex.ShortExact _ _ z₂
              (@ShortComplex.map _ _ _ _ z₁ z₂ S (completion X J) hz)
    have hP : P zC zD := fun _ ↦ hExact
    have hP' : P
        (@Preadditive.preadditiveHasZeroMorphisms _ _ hC.some.toPreadditive)
        (@Preadditive.preadditiveHasZeroMorphisms _ _ hD.some.toPreadditive) :=
      (congrArg₂ P (Subsingleton.elim _ _) (Subsingleton.elim _ _)) ▸ hP
    exact hP' inferInstance
  have : PreservesFiniteLimits (completion X J) := hPres.1
  let K : CoherentModules X := ⟨kernel b.hom,
    ((RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1
      Q.obj R.obj b.hom Q.property R.property).1⟩
  let i : K ⟶ Q := ObjectProperty.homMk (kernel.ι b.hom)
  have hi : i ≫ b = 0 := by
    apply ObjectProperty.hom_ext
    exact kernel.condition b.hom
  let c := KernelFork.ofι i hi
  have hc : IsLimit c := by
    apply Fork.IsLimit.mk'
    intro s
    let k : s.pt ⟶ K := ObjectProperty.homMk
      (kernel.lift b.hom s.ι.hom (congrArg (fun v ↦ v.hom) s.condition))
    refine ⟨k, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact kernel.lift_ι _ _ _
    · intro l hl
      apply ObjectProperty.hom_ext
      apply (cancel_mono (kernel.ι b.hom)).mp
      exact (congrArg (fun v ↦ v.hom) hl).trans (kernel.lift_ι b.hom s.ι.hom
        (congrArg (fun v ↦ v.hom) s.condition)).symm
  have hc' := KernelFork.mapIsLimit c hc (completion X J)
  have hd : (f - g) ≫ (completion X J).map b = 0 := by
    rw [Preadditive.sub_comp, hcomp, sub_self]
  obtain ⟨k, hk⟩ := KernelFork.IsLimit.lift' hc' (f - g) hd
  have hkn : k.hom.app (op n) = 0 := by
    have hn := congrArg (fun v ↦ v.hom.app (op n)) hk
    change k.hom.app (op n) ≫
      formalModuleQuotientMap J (kernel.ι b.hom) (Nat.le_refl (n + 1)) =
      f.hom.app (op n) - g.hom.app (op n) at hn
    rw [hlevel, sub_self] at hn
    have := kernel_quotient_projection_isIso J b.hom n hsep n le_rfl
    let q := formalModuleQuotientπ J (n + 1) (kernel b.hom)
    have hq : q ≫ formalModuleQuotientMap J (kernel.ι b.hom)
        (Nat.le_refl (n + 1)) =
        kernel.ι b.hom ≫ formalModuleQuotientπ J (n + 1) Q.obj := by
      simp [q, formalModuleQuotientπ, formalModuleQuotientMap]
    let := hsep
    have hz : k.hom.app (op n) ≫ inv q = 0 := by
      apply (cancel_mono (kernel.ι b.hom ≫
        formalModuleQuotientπ J (n + 1) Q.obj)).mp
      rw [Category.assoc, ← hq, IsIso.inv_hom_id_assoc]
      simpa using hn
    apply (cancel_mono (inv q)).mp
    simpa using hz
  have hhigh (m : ℕ) (hm : n ≤ m) : k.hom.app (op m) = 0 := by
    have := kernel_quotient_projection_isIso J b.hom n hsep n le_rfl
    have := kernel_quotient_projection_isIso J b.hom n hsep m hm
    let t := ((completion X J).obj K).obj.map (homOfLE hm).op
    have ht : formalModuleQuotientπ J (m + 1) K.obj ≫ t =
        formalModuleQuotientπ J (n + 1) K.obj := by
      change cokernel.π _ ≫ cokernel.desc _ _ _ = _
      simp
    have ht' : t = inv (formalModuleQuotientπ J (m + 1) K.obj) ≫
        formalModuleQuotientπ J (n + 1) K.obj := by
      rw [← ht, IsIso.inv_hom_id_assoc]
    have : IsIso t := by rw [ht']; infer_instance
    apply (cancel_mono t).mp
    have hn := k.hom.naturality (homOfLE hm).op
    change M.obj.map (homOfLE hm).op ≫ k.hom.app (op n) =
      k.hom.app (op m) ≫ t at hn
    rw [hkn, comp_zero] at hn
    simpa only [zero_comp] using hn.symm
  have hkzero : k = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext a
    obtain ⟨m⟩ := a
    change k.hom.app (op m) = 0
    by_cases hm : n ≤ m
    · exact hhigh m hm
    · have hmn : m ≤ n := by omega
      have := formalTransition_epi M hmn
      apply (cancel_epi (M.obj.map (homOfLE hmn).op)).mp
      have hn := k.hom.naturality (homOfLE hmn).op
      rw [hkn, zero_comp] at hn
      simpa only [comp_zero] using hn
  have hd0 : f - g = 0 := by
    rw [← hk, hkzero, zero_comp]
  exact sub_eq_zero.mp hd0

end

end AlgebraicGeometry
