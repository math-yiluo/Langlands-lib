/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.SquareZeroGluedLinearOperators
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # The quotient action on a square-zero ideal

Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem equality_on_lifting_cover (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (hp : Epi ((commAlgebraSheafModuleFunctor X.sheaf).map p))
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (U : X.Opens) (f : C.right.obj.obj (op U)) (s t : I.val.obj (op U))
    (h : ∀ (V : X.Opens) (j : V ⟶ U) (b : B.right.obj.obj (op V)),
      p.right.hom.app (op V) b = C.right.obj.map j.op f →
        I.val.map j.op s = I.val.map j.op t) : s = t := by
  obtain ⟨A, V, hV, b, hc, hb⟩ :=
    ((RingedSpace.module_exactness_local_lifting X.toRingedSpace).2.1
      (commAlgebraSheafModule X.sheaf B) (commAlgebraSheafModule X.sheaf C)
      ((commAlgebraSheafModuleFunctor X.sheaf).map p)).2.mpr hp U f
  let F := (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj I
  apply TopCat.Sheaf.eq_of_locally_eq' F V U (fun a ↦ homOfLE (hV a)) (by rw [hc]) s t
  intro a
  exact h (V a) (homOfLE (hV a)) (b a) (hb a)

set_option backward.isDefEq.respectTransparency false in
/-- A square-zero kernel has a local action by the quotient algebra, compatible with
restriction. No resolutions or cohomology occur in this assertion.
Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
(blueprint: lem-sc-square-zero-quotient-local-action)

Proof: Short exactness identifies I with the kernel sheaf of p. For a section f of C
on U, choose local lifts b on an open cover of U, using that p is an epimorphism of
sheaves. For x in I(U), the product b * i(x) lies in the kernel, hence has a unique
preimage in I on that open. Two lifts differ by a kernel section, so their products
with i(x) agree by square-zero. These preimages therefore glue uniquely. Define
sigma_U(f)(x) to be this glued section. Multiplication is linear over O_X(U), and
its additive, unit, and composition identities follow after restricting to a cover
with lifts and applying the monomorphism i. The same uniqueness proves compatibility
with restriction. For f = p(b), one may use b itself as the lift, giving the displayed
formula. Empty opens and the zero kernel cause no exception: uniqueness gives the
unique action on the zero module. -/
theorem square_zero_quotient_local_action (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U))),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) := by
  obtain ⟨α, hα, hres⟩ := square_zero_glued_linear_operators X B C p I i hw hS hsq
  dsimp only [id] at hα
  have hinj (U : X.Opens) : Function.Injective (i.val.app (op U)) := by
    have : Mono i := hS.mono_f
    exact (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op U)).map i)).mp
      inferInstance
  have hzero (U : X.Opens) : α U 0 = 0 := by
    ext x
    apply hinj U
    simpa using hα U 0 x
  have hone (U : X.Opens) : α U 1 = 1 := by
    ext x
    apply hinj U
    simpa using hα U 1 x
  have hadd (U : X.Opens) (f g : C.right.obj.obj (op U)) :
      α U (f + g) = α U f + α U g := by
    ext x
    change α U (f + g) x = α U f x + α U g x
    apply equality_on_lifting_cover X B C p hS.epi_g I U f
    intro V j b hb
    simp only [hres, map_add]
    apply equality_on_lifting_cover X B C p hS.epi_g I V (C.right.obj.map j.op g)
    intro W k c hc
    simp only [hres, map_add]
    have hb' : p.right.hom.app (op W) (B.right.obj.map k.op b) =
        C.right.obj.map k.op (C.right.obj.map j.op f) := by
      rw [← hb]
      exact congrArg (fun m ↦ m b) (p.right.hom.naturality k.op)
    apply hinj W
    rw [← hb', ← hc, ← map_add, hα, map_add, hα, hα, add_mul]
  have hmul (U : X.Opens) (f g : C.right.obj.obj (op U)) :
      α U (f * g) = α U f * α U g := by
    ext x
    apply equality_on_lifting_cover X B C p hS.epi_g I U f
    intro V j b hb
    change I.val.map j.op (α U (f * g) x) =
      I.val.map j.op (α U f (α U g x))
    simp only [hres, map_mul]
    apply equality_on_lifting_cover X B C p hS.epi_g I V (C.right.obj.map j.op g)
    intro W k c hc
    simp only [hres, map_mul]
    have hb' : p.right.hom.app (op W) (B.right.obj.map k.op b) =
        C.right.obj.map k.op (C.right.obj.map j.op f) := by
      rw [← hb]
      exact congrArg (fun m ↦ m b) (p.right.hom.naturality k.op)
    apply hinj W
    rw [← hb', ← hc, ← map_mul, hα, hα, hα, mul_assoc]
  let σ (U : X.Opens) : C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)) :=
    { toFun := α U
      map_zero' := hzero U
      map_one' := hone U
      map_add' := hadd U
      map_mul' := hmul U }
  exact ⟨σ, hα, hres⟩

end AlgebraicGeometry
