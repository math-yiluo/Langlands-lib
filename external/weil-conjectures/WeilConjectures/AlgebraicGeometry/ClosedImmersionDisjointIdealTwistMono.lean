/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Injectivity of restriction on a disjoint ideal twist

Source: Stacks Project, Remark 09NW, the kernel calculation, and Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-mono).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private theorem ideal_inclusions_disjoint {Y : Scheme.{u}}
    (I J : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ J.idealOfOpens U = ⊥)
    {T : Y.Modules} (a : T ⟶ I.toModules) (b : T ⟶ J.toModules)
    (h : a ≫ I.toModulesι = b ≫ J.toModulesι) : a = 0 := by
  apply (cancel_mono I.toModulesι).mp
  rw [zero_comp]
  apply Scheme.Modules.hom_ext
  intro U
  ext t
  have hi : I.toModulesι.app U (a.app U t) ∈ I.idealOfOpens U :=
    (I.range_toModulesι_app_eq_idealOfOpens U).subset ⟨a.app U t, rfl⟩
  have hj : I.toModulesι.app U (a.app U t) ∈ J.idealOfOpens U := by
    rw [show I.toModulesι.app U (a.app U t) = J.toModulesι.app U (b.app U t) from
      congrArg (fun f ↦ f.app U t) h]
    exact (J.range_toModulesι_app_eq_idealOfOpens U).subset ⟨b.app U t, rfl⟩
  have hz : I.toModulesι.app U (a.app U t) ∈
      I.idealOfOpens U ⊓ J.idealOfOpens U := ⟨hi, hj⟩
  rw [hzero U] at hz
  exact hz

private theorem tensor_ideal_inclusions_disjoint {Y : Scheme.{u}}
    (I J : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ J.idealOfOpens U = ⊥)
    (N : Y.Modules) [N.IsInvertible] {T : Y.Modules}
    (a : T ⟶ I.toModules ⊗ N) (b : T ⟶ J.toModules ⊗ N)
    (h : a ≫ I.toModulesι ▷ N = b ≫ J.toModulesι ▷ N) : a = 0 := by
  let e := BraidedCategory.tensorRightEquivalence N N.dual
    (nonempty_tensorObj_dual_iso_unit N).some
  let a' := e.functor.preimage ((e.counitIso.app T).hom ≫ a)
  let b' := e.functor.preimage ((e.counitIso.app T).hom ≫ b)
  change a ≫ e.functor.map I.toModulesι = b ≫ e.functor.map J.toModulesι at h
  have hab : a' ≫ I.toModulesι = b' ≫ J.toModulesι := by
    apply e.functor.map_injective
    simpa [a', b', Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ (e.counitIso.app T).hom ≫ f) h
  have ha' : a' = 0 := ideal_inclusions_disjoint I J hzero a' b' hab
  have ha : (e.counitIso.app T).hom ≫ a = 0 := by
    rw [← e.functor.map_preimage ((e.counitIso.app T).hom ≫ a)]
    change e.functor.map a' = 0
    rw [ha', Functor.map_zero]
  exact (cancel_epi (e.counitIso.app T).hom).mp (ha.trans (comp_zero.symm))

/-- Restriction of an ideal times an invertible module is monic when the ideal has
zero intersection with the closed-immersion ideal.

Source: Stacks Project, Remark 09NW, the calculation I/(I intersection J), and the
local trivialization argument in Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-mono).

Proof: put N = M.tensorPow m, which is invertible. First, maps into I and J with
identical composites into the structure module have zero common composite: on each
open its values belong to I(U) intersection J(U), which is zero by hzero. The ideal
inclusion is monic, so the map into I is zero. Tensoring with N is an equivalence,
with inverse tensoring by its dual. Fullness, faithfulness and the counit isomorphism
transport this zero-intersection property to the two tensor ideal inclusions.
Both multiplication maps are monic, so their images identify with their sources.
The closed-immersion unit kernel theorem identifies the image of J multiplication
with the kernel of the chosen unit on N. Any map into the image of I multiplication
killed by the unit therefore factors through the image of J multiplication. Cancel
the common unitor and apply the tensor zero-intersection property to show this map
is zero. The additive cancellation criterion proves monicity. No local choice of
trivialization or comparison of adjunctions is needed: the kernel theorem uses the
same chosen adjunction. The argument also covers empty schemes, m = 0 and I = 0. -/
theorem closedImmersion_disjointIdeal_twist_mono {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (hzero : ∀ U : Y.Opens, I.idealOfOpens U ⊓ i.ker.idealOfOpens U = ⊥)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    Mono (image.ι μ ≫ adj.unit.app (M.tensorPow m)) := by
  classical
  dsimp only
  let N := M.tensorPow m
  let μI := I.toModulesι ▷ N ≫ (λ_ N).hom
  let μJ := i.ker.toModulesι ▷ N ≫ (λ_ N).hom
  have : Mono μI := inferInstance
  have : Mono μJ := inferInstance
  obtain ⟨_, w, ⟨hk⟩⟩ := closedImmersion_unit_kernel i N
  rw [Preadditive.mono_iff_cancel_zero]
  intro T g hg
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk (g ≫ image.ι μI) (by
    simpa only [Category.assoc] using hg)
  let a := g ≫ (imageMonoIsoSource μI).hom
  let b := l ≫ (imageMonoIsoSource μJ).hom
  have hab : a ≫ I.toModulesι ▷ N = b ≫ i.ker.toModulesι ▷ N := by
    apply (cancel_mono (λ_ N).hom).mp
    change a ≫ μI = b ≫ μJ
    simpa [a, b, Category.assoc, imageMonoIsoSource_hom_self] using hl.symm
  have ha : a = 0 := tensor_ideal_inclusions_disjoint I i.ker hzero N a b hab
  apply (cancel_mono (imageMonoIsoSource μI).hom).mp
  exact ha.trans zero_comp.symm

end AlgebraicGeometry.Scheme.Modules
