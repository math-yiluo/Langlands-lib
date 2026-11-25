/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable

/-!
# Tor as the kernel of a tensor image inclusion

Source: Stacks Project, Tag 0653, the Tor argument in `lemma-last-one-flat`.
(blueprint: lem-pc-module-opcycles-tor-kernel-iso).
-/

@[expose] public section

universe u

namespace CategoryTheory

open MonoidalCategory

private theorem isZero_tor_one_flat
    {A : Type u} [CommRing A] (M N : ModuleCat.{u} A) (hflat : Module.Flat A M) :
    Limits.IsZero (((Tor' (ModuleCat.{u} A) 1).obj M).obj N) := by
  have : Module.Flat A M := hflat
  obtain ⟨e⟩ := nonempty_tor'_flip_iso A 1
  let Q := projectiveResolution N
  let F := tensorRight M
  apply Limits.IsZero.of_iso _ ((e.app M).app N)
  apply Limits.IsZero.of_iso _ (Q.isoLeftDerivedObj F 1)
  apply HomologicalComplex.ExactAt.isZero_homology
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
  simpa [F, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    ShortComplex.map] using
    Module.Flat.rTensor_shortComplex_exact M _ (Q.exact_succ 0)

/-- The first Tor of the opcycles is the kernel of the image inclusion after tensoring.
Source: Stacks Project, Tag 0653, Tor argument; Algebra, Tags 00M0 and 00M3.
(blueprint: lem-pc-module-opcycles-tor-kernel-iso)

Proof: Put K = im(P.d (a-1) a). The image inclusion and the opcycles projection form
an exact sequence 0 -> K -> P.X a -> P.opcycles a -> 0. Apply the first-variable
low-degree Tor sequence. Flatness of P.X a makes Tor_1(P.X a,N) zero: Tor symmetry
identifies it with Tor_1(N,P.X a), computed from a projective resolution of N
whose tensor with the flat module P.X a remains exact in positive degrees.
Exactness of the Tor sequence then makes the boundary injective with image exactly
ker(K tensor N -> P.X a tensor N). Factor the boundary through that kernel; the
factor is both injective and surjective, hence an isomorphism. The boundary is
natural in N by the long exact sequence theorem. Kernel inclusions are monic, so
this naturality passes to the factors. Finally, evaluation of a functor-category
kernel is canonically the kernel of its evaluated map, giving the stated natural
isomorphism. No flatness of any other term of P is required. -/
theorem nonempty_tor_opcycles_tensor_image_kernel_iso
    (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ℤ) (hflat : Module.Flat A (P.X a)) :
    Nonempty ((Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a) ≅
      Limits.kernel ((curriedTensor (ModuleCat.{u} A)).map
        (Abelian.image.ι (P.d (a - 1) a)))) := by
  classical
  let d := P.d (a - 1) a
  let K := Abelian.image d
  let i : K ⟶ P.X a := Abelian.image.ι d
  let p := P.pOpcycles a
  let S := ShortComplex.mk d p (P.d_pOpcycles (a - 1) a)
  have hS : S.Exact :=
    ShortComplex.exact_of_g_is_cokernel S (P.opcyclesIsCokernel (a - 1) a (by simp))
  have hex : Function.Exact i.hom p.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (S.exact_iff_exact_image_ι.mp hS)
  obtain ⟨δ, hδ, hn⟩ := tor_long_exact_first_variable i.hom p.hom
    ((ModuleCat.mono_iff_injective i).mp inferInstance)
    ((ModuleCat.epi_iff_surjective p).mp inferInstance) hex
  let T := (Tor' (ModuleCat.{u} A) 1).obj (P.opcycles a)
  let α : tensorLeft K ⟶ tensorLeft (P.X a) := (curriedTensor (ModuleCat A)).map i
  let β : T ⟶ tensorLeft K := {
    app := fun N ↦ δ N
    naturality := fun N N' f ↦ by
      apply ModuleCat.hom_ext
      exact (hn N N' f.hom).symm }
  have w : β ≫ α = 0 := by
    ext N x
    exact (hδ N).2.1.apply_apply_eq_zero x
  let γ : T ⟶ Limits.kernel α := Limits.kernel.lift α β w
  have fac (N : ModuleCat.{u} A) :
      γ.app N ≫ (Limits.kernel.ι α).app N = β.app N := by
    exact congrArg (fun t ↦ t.app N) (Limits.kernel.lift_ι α β w)
  have hγ (N : ModuleCat.{u} A) : IsIso (γ.app N) := by
    have hzero := isZero_tor_one_flat (P.X a) N hflat
    have hinj : Function.Injective (β.app N).hom := by
      intro x y hxy
      have hz : (δ N).hom (x - y) = 0 := by
        change (β.app N).hom (x - y) = 0
        rw [map_sub, hxy, sub_self]
      obtain ⟨z, hz⟩ := ((hδ N).1 (x - y)).mp hz
      have : Subsingleton (((Tor' (ModuleCat A) 1).obj (P.X a)).obj N) :=
        ModuleCat.isZero_iff_subsingleton.mp hzero
      have hz0 : z = 0 := Subsingleton.elim _ _
      rw [hz0, map_zero] at hz
      exact sub_eq_zero.mp hz.symm
    have : Mono (β.app N) := (ModuleCat.mono_iff_injective _).mpr hinj
    have : Mono (γ.app N) := mono_of_mono_fac (fac N)
    have : Epi (γ.app N) := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro y
      let z := (Limits.kernel.ι α).app N y
      have hz : (i.hom.rTensor N) z = 0 := by
        have hc := congrArg (fun t ↦ (t.app N).hom y) (Limits.kernel.condition α)
        exact hc
      obtain ⟨x, hx⟩ := ((hδ N).2.1 z).mp hz
      refine ⟨x, ?_⟩
      apply (ModuleCat.mono_iff_injective ((Limits.kernel.ι α).app N)).mp inferInstance
      have hf := congrArg (fun t : T.obj N ⟶ (tensorLeft K).obj N ↦ t.hom x) (fac N)
      exact hf.trans hx
    exact isIso_of_mono_of_epi (γ.app N)
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact ⟨asIso γ⟩

end CategoryTheory
