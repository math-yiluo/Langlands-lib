/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Detecting invertibility on the rank-one free module

Source: the free-module presentation argument, as in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator`.
-/

@[expose] public section

universe u v w
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] {D : Type v} [Category.{w} D]
  {F G : ModuleCat.{u} R ⥤ D}
  [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G]

/-- A natural transformation of cocontinuous functors on modules is invertible
if it is invertible on the free rank-one module.
Source: the free-module presentation argument in
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator,
`PresheafOfModules.isIso_app_of_freeYoneda`, specialized to a point.
(blueprint: lem-sc-modulecat-cocontinuous-generator)
Proof: each free module is a coproduct of copies of R, so preservation of coproducts
and naturality extend invertibility from R to every free module. Present any module
M by the surjection R^(M) → M sending the basis vector [m] to m. Map the free module
on the kernel into R^(M); its image is precisely that kernel, hence M is the
coequalizer of this map and zero. Both functors preserve this coequalizer, and the
transformation is invertible on its two free vertices, so it is invertible on M.
This also applies to the zero ring, zero module and empty free basis. -/
theorem isIso_app_of_rankOne (α : F ⟶ G)
    (h : IsIso (α.app (ModuleCat.of R R))) (M : ModuleCat.{u} R) :
    IsIso (α.app M) := by
  have hF : PreservesColimitsOfSize.{0, 0} F :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} F
  have hG : PreservesColimitsOfSize.{0, 0} G :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} G
  have hfree (I : Type u) : IsIso (α.app ((free R).obj I)) := by
    let c : Cofan (fun _ : I ↦ ModuleCat.of R R) :=
      Cofan.mk ((free R).obj I) (fun i ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf R ℤ ((free R).obj I)).symm (freeMk i)))
    have hc : IsColimit c := by
      refine Cofan.IsColimit.mk _
        (fun s ↦ freeDesc (↾fun i ↦ s.inj i 1)) ?_ ?_
      · intro s i
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        simp [c]
      · intro s m hm
        apply free_hom_ext
        intro i
        have hi := congrArg (fun f : ModuleCat.of R R ⟶ s.pt ↦ f 1) (hm i)
        simpa [c, ModuleCat.comp_apply] using hi
    let K := Discrete.functor (fun _ : I ↦ ModuleCat.of R R)
    have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := fun _ ↦ h
    have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K α c hc
  let g : (free R).obj M ⟶ M := freeDesc (↾fun m ↦ m)
  let f : (free R).obj g.hom.ker ⟶ (free R).obj M := freeDesc (↾fun x ↦ x.val)
  have hg : Function.Surjective g.hom := by
    intro m
    exact ⟨freeMk m, freeDesc_apply _ _⟩
  have hfg : Function.Exact f.hom g.hom := by
    intro x
    constructor
    · intro hx
      exact ⟨freeMk (⟨x, hx⟩ : g.hom.ker), freeDesc_apply _ _⟩
    · rintro ⟨y, rfl⟩
      have heq : g.hom.comp f.hom = 0 := by
        apply Finsupp.lhom_ext'
        intro y
        apply LinearMap.ext_ring
        change g (f (freeMk y)) = 0
        rw [show f (freeMk y) = y.val from freeDesc_apply _ _]
        exact y.property
      exact LinearMap.congr_fun heq y
  let K := parallelPair f 0
  have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := by
    intro j
    cases j <;> apply hfree
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _
    (ModuleCat.isColimitCokernelCofork f g hfg hg)

end ModuleCat
