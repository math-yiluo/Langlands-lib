/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.IsFlatOver
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties

/-! # Base change preserves flat finitely presented modules with proper support

Source: Stacks Project, Tags 01U8 (relative flatness), 056J (support), and 0CYS.
(blueprint: lem-pc-tensor-pullback-flat-proper-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem flatOver_restrict
    {X Y S : Scheme.{u}} (a : X ⟶ Y) [IsOpenImmersion a] (f : Y ⟶ S)
    (F : Y.Modules) (hflat : F.IsFlatOver f) : (F.restrict a).IsFlatOver (a ≫ f) := by
  intro V U e
  let U' : Y.affineOpens := ⟨a ''ᵁ U.1, U.2.image_of_isOpenImmersion a⟩
  have e' : U'.1 ≤ f ⁻¹ᵁ V.1 := by
    apply (a.image_mono e).trans
    exact (a.image_preimage_le (f ⁻¹ᵁ V.1))
  have hh := hflat V U' e'
  have heq : (a ≫ f).appLE V.1 U.1 e ≫ (a.appIso U.1).inv =
      f.appLE V.1 U'.1 e' := by
    rw [Scheme.Hom.comp_appLE, Category.assoc, Scheme.Hom.appLE_appIso_inv]
    rfl
  convert hh using 1 <;> try rfl
  ext r m
  change (F.smul (((a.appIso U.1).inv.hom)
    (((a ≫ f).appLE V.1 U.1 e).hom r))).asHom.hom m =
      (F.smul ((f.appLE V.1 U'.1 e').hom r)).asHom.hom m
  exact congrArg (fun t ↦ (F.smul t).asHom.hom m) (congrArg (fun t ↦ t.hom r) heq)

/-- Base change preserves finite presentation, base-flatness and proper support
for one module. The square must be cartesian; an arbitrary commutative square would
not preserve flatness over the new base.

Proof:
1. Pull back a local finite presentation of M. Tensor is right exact and sends
   finite free modules to finite free modules, giving finite presentation of p* M.
2. At a point of Xj, the cartesian square identifies p* M with the base change
   of a module flat over the old base (Tag 01U8). On affine cartesian charts,
   if A is the old base ring, B its scheme algebra, A' the new base ring,
   and N the module, then (B ⊗[A] A') ⊗[B] N ≅ A' ⊗[A] N.
   The right side is flat over A'. Localization preserves this flatness.
   These charts cover Xj, giving relative stalk flatness. For any affine test
   open U over an affine base open V, quasi-coherence identifies localizations
   of its section module with stalks. Each is flat over the corresponding
   localized base ring. The localization criterion of Tag 00HT(6) gives
   flatness of the section module over the base ring, precisely IsFlatOver.
3. M is finitely presented, hence quasi-coherent of finite type. Tag 056J identifies
   the support of p* M with the inverse image of the support of M. By Tag 0CYS,
   represent M on a closed subscheme proper over Si; base change that closed
   subscheme to Sj. Its morphism remains proper and the pulled-back module is
   supported there. Its support is closed by finite type and is proper over Sj,
   again by Tag 0CYS. This is precisely HasSupportProperOver fj.

Edge cases: the zero module has empty support and remains zero; an empty source
causes no exception. No flatness of k or p is required: only the square is cartesian.
Source: Stacks Project, Tags 01U8 (relative flatness), 056J (support), and 0CYS.
(blueprint: lem-pc-tensor-pullback-flat-proper-support).
-/
theorem tensorPullback_flat_proper_support
    {Xi Xj Si Sj : Scheme.{u}}
    (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj) [LocallyOfFiniteType fi] [LocallyOfFiniteType fj]
    (p : Xj ⟶ Xi) (k : Sj ⟶ Si) (hcart : IsPullback p fj fi k)
    (M : Xi.Modules) [M.IsFinitePresentation]
    (hflat : M.IsFlatOver fi) (hproper : Scheme.Modules.HasSupportProperOver fi M) :
    (Scheme.Modules.tensorPullbackObj p M).IsFinitePresentation ∧
      (Scheme.Modules.tensorPullbackObj p M).IsFlatOver fj ∧
      Scheme.Modules.HasSupportProperOver fj (Scheme.Modules.tensorPullbackObj p M) := by
  classical
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction p
  let ep := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction p)
  -- Compare the tensor formula with the native left adjoint.
  have hfp : (Scheme.Modules.tensorPullbackObj p M).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_of_iso (ep.app M).symm
  refine ⟨hfp, ?_, ?_⟩
  · -- Reduce the arbitrary cartesian square to the canonical fibre product.
    let a := hcart.isoPullback.hom
    let N := Scheme.Modules.tensorPullbackObj (pullback.fst fi k) M
    have hn : N.IsFlatOver (pullback.snd fi k) :=
      relativelyFlat_module_pullback fi k M hflat
    obtain ⟨adja⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
    let ec := (Scheme.Modules.nonempty_tensorPullbackComp a (pullback.fst fi k)).some
    let ea := adja.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction a)
    let ei := (Scheme.Modules.restrictFunctorIsoPullback a).symm
    let eg : Scheme.Modules.tensorPullbackObj p M ≅ N.restrict a :=
      (eqToIso (congrArg (fun q ↦ Scheme.Modules.tensorPullbackObj q M)
        hcart.isoPullback_hom_fst)).symm ≪≫ ec.app M ≪≫ ea.app N ≪≫ ei.app N
    refine Scheme.Modules.IsFlatOver.of_iso (f := fj) eg.symm ?_
    simpa only [a, hcart.isoPullback_hom_snd] using
      flatOver_restrict a (pullback.snd fi k) N hn
  · -- Base change a closed subscheme structure on the support.
    obtain ⟨Z, hZ, hpZ⟩ := hproper
    let Zj : TopologicalSpace.Closeds Xj :=
      ⟨p.base ⁻¹' (Z : Set Xi), Z.isClosed.preimage p.base.hom.continuous⟩
    refine ⟨Zj, ?_, ?_⟩
    · exact (congrArg (fun A : Set Xi ↦ p.base ⁻¹' A) hZ).trans
        ((Scheme.Modules.finiteType_module_support_pullback M).2.2 Xj p).2.symm
    · obtain ⟨T, i, hci, hi, hpi⟩ :=
        (Scheme.closed_subset_proper_over_base_properties fi Z).1.mp hpZ
      have : IsProper (i ≫ fi) := hpi
      let j := pullback.snd i p
      have hj : Set.range j.base = (Zj : Set Xj) := by
        change Set.range (pullback.snd i p) = p ⁻¹' (Z : Set Xi)
        rw [Scheme.Pullback.range_snd]
        exact congrArg (fun A : Set Xi ↦ p ⁻¹' A) hi
      apply (Scheme.closed_subset_proper_over_base_properties fj Zj).1.mpr
      refine ⟨pullback i p, j, inferInstance, hj, ?_⟩
      exact MorphismProperty.of_isPullback (P := @IsProper)
        ((IsPullback.of_hasPullback i p).paste_vert hcart) hpi

end AlgebraicGeometry
