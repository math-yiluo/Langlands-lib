/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement

/-! # Local divisibility under restriction to an equivalent site
Source: Stacks 03A0, 03CH, 03DA, 03DG and 0999.
(blueprint: lem-pur-native-ringed-restriction-divisibility). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsEquivalence] [F.IsDenseSubsite K J]
  (R : Sheaf J CommRingCat.{max c d vc vd r})
attribute [local instance] sliceDense

/-- Local principal divisibility is preserved and reflected by restriction. Pull back a covering
sieve along the dense equivalence for one direction. For the converse push it forward; a
resulting arrow factors through an image arrow, and naturality transports its chosen quotient
along that factor. This works also for the zero generator and empty covers.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 0999.
(blueprint: lem-pur-native-ringed-restriction-divisibility). -/
theorem localDivisibilityRestriction
    (a : (R.obj ⋙ forget CommRingCat).sections) (U : C)
    (s : ((R.over (F.obj U)).obj ⋙ forget CommRingCat).sections) :
    principalLocallyDivisible.{d, vd, max c vc r} R a (F.obj U) s ↔
      principalLocallyDivisible.{c, vc, max d vd r}
        (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R)
        (restrictedSection.{c, d, vc, vd, r} (K := K) F R a) U
        (restrictedSection.{max c vc, max d vd, vc, vd, r}
          (K := K.over U) (Over.post F) (R.over (F.obj U)) s) := by
  constructor
  · rintro ⟨S, hS, hs⟩
    let : F.IsCoverDense J := Functor.IsDenseSubsite.isCoverDense K J F
    let : F.IsLocallyFull J := Functor.IsDenseSubsite.isLocallyFull K J F
    have hcov : S.functorPullback F ∈ K U :=
      (F.functorPushforward_mem_iff K J).mp
        (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨S, hS⟩)
    exact ⟨S.functorPullback F, hcov, fun V f hf ↦ hs (F.obj V) (F.map f) hf⟩
  · rintro ⟨S, hS, hs⟩
    refine ⟨S.functorPushforward F, (F.functorPushforward_mem_iff K J).mpr hS, ?_⟩
    rintro V f ⟨W, g, h, hg, rfl⟩
    have hb0 := hs W g hg
    change ∃ b : R.obj.obj (op (F.obj W)),
      s.val (op (Over.mk (F.map g))) =
        (show R.obj.obj (op (F.obj W)) from a.val (op (F.obj W))) * b at hb0
    obtain ⟨b, hb⟩ := hb0
    refine ⟨R.obj.map h.op b, ?_⟩
    have hn := s.property (show op (Over.mk (F.map g)) ⟶
        op (Over.mk (h ≫ F.map g)) from (Over.homMk h rfl).op)
    change R.obj.map h.op (s.val (op (Over.mk (F.map g)))) =
      s.val (op (Over.mk (h ≫ F.map g))) at hn
    rw [← hn, hb, map_mul]
    rw [show R.obj.map h.op (a.val (op (F.obj W))) = a.val (op V) from a.property h.op]
end CategoryTheory.NativeRestriction
