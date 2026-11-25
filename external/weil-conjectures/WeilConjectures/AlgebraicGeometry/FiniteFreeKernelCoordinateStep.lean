/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSubmoduleIdeal

/-!
# Removing one coordinate from a finite free kernel

Source: Stacks Project, Tag 01XF, coordinate-filtration paragraph
(blueprint: lem-pqf-finite-free-kernel-coordinate-step).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separate the distinguished summand of a coproduct indexed by `Option I`. -/
private theorem free_option_coordinate_split
    {C : Type*} [Category C] [Preadditive C] {T : C} {I : Type*}
    (F : Cofan (fun _ : I ↦ T)) (hF : IsColimit F)
    (G : Cofan (fun _ : Option I ↦ T)) (hG : IsColimit G)
    (inc : F.pt ⟶ G.pt) (hi : ∀ i, F.inj i ≫ inc = G.inj (some i)) :
    ∃ (r : G.pt ⟶ F.pt) (t : G.pt ⟶ T) (s : T ⟶ G.pt),
      inc ≫ r = 𝟙 _ ∧ inc ≫ t = 0 ∧ r ≫ inc + t ≫ s = 𝟙 _ := by
  let r := Cofan.IsColimit.desc hG (fun i ↦ match i with
    | none => 0
    | some j => F.inj j)
  let t := Cofan.IsColimit.desc hG (fun i ↦ match i with
    | none => 𝟙 T
    | some _ => 0)
  refine ⟨r, t, G.inj none, ?_, ?_, ?_⟩
  · apply Cofan.IsColimit.hom_ext hF
    intro i
    rw [← Category.assoc, hi]
    simp only [r, Cofan.IsColimit.fac, Category.comp_id]
  · apply Cofan.IsColimit.hom_ext hF
    intro i
    rw [← Category.assoc, hi]
    simp only [t, Cofan.IsColimit.fac, comp_zero]
  · apply Cofan.IsColimit.hom_ext hG
    intro i
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    cases i with
    | none => simp [r, t]
    | some i => simp [r, t, hi]

/-- A split coordinate decomposition gives the kernel an image quotient. -/
private theorem exists_shortExact_kernel_split
    {C : Type*} [Category C] [Abelian C] {Q P T L T' : C}
    (inc : Q ⟶ P) (r : P ⟶ Q) (t : P ⟶ T) (s : T ⟶ P) (p : P ⟶ L)
    (hir : inc ≫ r = 𝟙 Q) (hit : inc ≫ t = 0) (hsplit : r ≫ inc + t ≫ s = 𝟙 P)
    (e : Abelian.image (kernel.ι p ≫ t) ≅ T') :
    ∃ (a : kernel (inc ≫ p) ⟶ kernel p) (b : kernel p ⟶ T') (w : a ≫ b = 0),
      (ShortComplex.mk a b w).ShortExact := by
  let q := inc ≫ p
  have : Mono inc := mono_of_mono_fac hir
  let a : kernel q ⟶ kernel p := kernel.map q p inc (𝟙 _) (by simp [q])
  let v := kernel.ι p ≫ t
  have ha : a ≫ kernel.ι p = kernel.ι q ≫ inc := by simp [a]
  have hav : a ≫ v = 0 := by
    dsimp only [v]
    rw [← Category.assoc, ha, Category.assoc, hit, comp_zero]
  have : Mono a := by
    have : Mono (a ≫ kernel.ι p) := by rw [ha]; infer_instance
    exact mono_of_mono a (kernel.ι p)
  have hkernel : IsLimit (KernelFork.ofι a hav) := by
    apply KernelFork.IsLimit.ofι'
    intro T k hk
    have hrec : (k ≫ kernel.ι p ≫ r) ≫ inc = k ≫ kernel.ι p := by
      have h := congrArg (fun f ↦ (k ≫ kernel.ι p) ≫ f) hsplit
      have hkts : (k ≫ kernel.ι p) ≫ (t ≫ s) = 0 := by
        calc
          (k ≫ kernel.ι p) ≫ (t ≫ s) = (k ≫ v) ≫ s := by
            simp only [v, Category.assoc]
          _ = 0 := by rw [hk, zero_comp]
      simp only [Preadditive.comp_add, Category.comp_id, hkts, add_zero] at h
      simpa only [Category.assoc] using h
    have hkq : (k ≫ kernel.ι p ≫ r) ≫ q = 0 := by
      change (k ≫ kernel.ι p ≫ r) ≫ (inc ≫ p) = 0
      rw [← Category.assoc, hrec]
      simp
    refine ⟨kernel.lift q (k ≫ kernel.ι p ≫ r) hkq, ?_⟩
    apply (cancel_mono (kernel.ι p)).mp
    simp only [Category.assoc, ha, kernel.lift_ι_assoc]
    simpa only [Category.assoc] using hrec
  let b₀ := Abelian.factorThruImage v
  have hw₀ : a ≫ b₀ = 0 := by
    apply (cancel_mono (Abelian.image.ι v)).mp
    simp [b₀, Category.assoc, hav]
  have hbkernel : IsLimit (KernelFork.ofι a hw₀) :=
    isKernelOfComp (Abelian.image.ι v) v hkernel hw₀ (Abelian.image.fac v)
  have : Epi b₀ := inferInstanceAs (Epi (Abelian.factorThruImage v))
  have hs₀ : (ShortComplex.mk a b₀ hw₀).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ hbkernel }
  have hw : a ≫ (b₀ ≫ e.hom) = 0 := by simp [← Category.assoc, hw₀]
  refine ⟨a, b₀ ≫ e.hom, hw, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk a b₀ hw₀)
      (S₂ := ShortComplex.mk a (b₀ ≫ e.hom) hw) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp)) hs₀

/-- The image of a map from a quasi-coherent module to the unit is an ideal sheaf. -/
private theorem quasiCoherent_image_ideal (X : Scheme.{u}) {M : X.Modules}
    [M.IsQuasicoherent] (v : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ∃ J : X.IdealSheafData, J.toModules.IsQuasicoherent ∧
      Nonempty (Abelian.image v ≅ J.toModules) := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := Scheme.Modules.isQuasicoherent_cokernel v
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π v)
  exact quasiCoherent_submodule_ideal X (Abelian.image.ι v)

set_option backward.isDefEq.respectTransparency false in
/-- Removing the distinguished coordinate gives a short exact sequence of kernels
with a quasi-coherent ideal quotient.

Source: Stacks Project, Tag 01XF, coordinate-filtration paragraph
(blueprint: lem-pqf-finite-free-kernel-coordinate-step).

Proof: Let q be the restriction of p to the coordinates indexed by I. The inclusion
of these coordinates induces a monomorphism kernel q → kernel p. Project kernel p
onto the coordinate indexed by none. Its kernel is exactly kernel q: a vector whose
none coordinate vanishes comes uniquely from the coordinates indexed by I, and the
condition that p kills it is the condition that q kills that vector. Both kernels
are quasi-coherent by quasi-coherent kernel closure, since the finite free source
and the structure sheaf are quasi-coherent. The image of the projection is therefore
quasi-coherent by quasi-coherent image closure. On every affine open its sections,
viewed inside the section ring, form an ideal. Quasi-coherence says these ideals
localize on principal opens, so they define ideal sheaf data J. The image and
J.toModules have identical section ranges inside the structure sheaf on the affine
basis, by range_toModulesι_app. Injectivity gives inverse linear maps on that basis;
uniqueness makes them compatible with restriction and sheaf gluing extends them.
Transport the epimorphism onto the image along this isomorphism. Its kernel is the
coordinate inclusion of kernel q, giving the short exact sequence. No surjectivity
of p is needed. For I empty, q has zero source and the sequence identifies kernel p
with its ideal image; for p zero the quotient is the unit ideal.
-/
theorem finite_free_kernel_coordinate_step (X : Scheme.{u})
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := X.ringCatSheaf) (Option I) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    ∃ J : X.IdealSheafData, J.toModules.IsQuasicoherent ∧
      ∃ (a : kernel (SheafOfModules.freeMap (R := X.ringCatSheaf) some ≫ p) ⟶ kernel p)
        (b : kernel p ⟶ J.toModules) (w : a ≫ b = 0),
        (ShortComplex.mk a b w).ShortExact := by
  classical
  let inc := SheafOfModules.freeMap (R := X.ringCatSheaf) (some : I → Option I)
  obtain ⟨r, t, s, hir, hit, hsplit⟩ := free_option_coordinate_split
    (SheafOfModules.freeCofan I) (SheafOfModules.isColimitFreeCofan I)
    (SheafOfModules.freeCofan (Option I)) (SheafOfModules.isColimitFreeCofan (Option I))
    inc (SheafOfModules.ιFree_freeMap some)
  let v := kernel.ι p ≫ t
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_free (R := X.ringCatSheaf) (Option I)
  have hqc := Scheme.Modules.isQuasicoherent_kernel p
  have himage := quasiCoherent_image_ideal X v
  let J := himage.choose
  have hJ := himage.choose_spec
  have hstep := exists_shortExact_kernel_split inc r t s p hir hit hsplit
    (Classical.choice hJ.2)
  exact ⟨J, hJ.1, hstep⟩

end AlgebraicGeometry
