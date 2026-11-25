/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Underlying quasi-coherence of algebra-module kernels

Source: EGA I, Proposition 9.6.1; Stacks Project, Schemes, Lemma 01IC.
(blueprint: lem-weil-pbc-affine-algebra-module-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem scalarRestriction_preservesLimitsAndColimits
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) ∧
      PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) := by
  have h (B : Sheaf J RingCat.{u}) :
      PreservesLimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) ∧
        PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
    refine ⟨⟨?_⟩, ⟨?_⟩⟩
    · intro K _
      exact ((moduleSheaves_colimits_forgetful B).2.2.2.2.2 K).1
    · intro K _
      exact ((moduleSheaves_colimits_forgetful B).2.2.2.2.2 K).2.1
  have := (h R).1
  have := (h R).2
  have := (h R').1
  have := (h R').2
  have : ReflectsLimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    reflectsLimits_of_reflectsIsomorphisms
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesLimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R'))
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R'))
  exact ⟨preservesLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R),
    preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quasiCoherent_slice_iff_open {S : Scheme.{u}} (U : S.Opens)
    (M : SheafOfModules.{u} (S.ringCatSheaf.over U)) :
    M.IsQuasicoherent ↔ ((overEquiv U).functor.obj M).IsQuasicoherent := by
  have := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  constructor
  · intro hM
    have := hM
    have (V : U.toScheme.Opens) :
        (Over.post U.overEquivalence.inverse).IsContinuous
          ((Opens.grothendieckTopology U.carrier).over V)
          (((Opens.grothendieckTopology S).over U).over
            (U.overEquivalence.inverse.obj V)) := by
      exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
        ((CoverPreserving.of_isContinuous U.overEquivalence.inverse _ _).overPost V)
    apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.inverse _ (U.sheafOfModulesEquivOverUnit S.ringCatSheaf)
  · intro hM
    have := hM
    have (V : Over U) :
        (Over.post U.overEquivalence.functor).IsContinuous
          (((Opens.grothendieckTopology S).over U).over V)
          ((Opens.grothendieckTopology U.carrier).over
            (U.overEquivalence.functor.obj V)) := by
      exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
        ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost V)
    have hback : ((overEquiv U).inverse.obj ((overEquiv U).functor.obj M)).IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
        U.overEquivalence.functor _ (U.sheafOfModulesEquivOverInverseUnit S.ringCatSheaf)
    exact (SheafOfModules.isQuasicoherent (S.ringCatSheaf.over U)).prop_of_iso
      ((overEquiv U).unitIso.app M).symm hback

/-- The underlying kernel of a map from a free algebra-module sheaf is quasi-coherent.
Source: EGA I, Proposition 9.6.1; Stacks Project, Schemes, Lemma 01IC and Section 01LA(5).
(blueprint: lem-weil-pbc-affine-algebra-module-kernel)

Proof: restriction of scalars leaves the underlying abelian sheaf unchanged, so it
preserves kernels and coproducts (both can be checked after forgetting to abelian
sheaves). The underlying free A-module sheaf is therefore the coproduct of copies of
A as an O-module, restricted to U. Quasi-coherence of A implies quasi-coherence of
this coproduct. The underlying M is quasi-coherent by hypothesis. After identifying
the slice with modules on the open subscheme, apply closure of quasi-coherent modules
under kernels to the restricted-scalar morphism. Transport back and use preservation
of kernels to obtain the assertion. No epimorphism or relation generators are asserted. -/
theorem affine_algebraModule_kernel_isQuasicoherent
    (S : Scheme.{u}) (A : S.CommAlgebraSheaf) (U : S.Opens)
    (M : SheafOfModules.{u}
      (((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).obj
        A.right).over U))
    (hA : A.toModule.IsQuasicoherent)
    (hM : ((SheafOfModules.restrictScalars
      (((Opens.grothendieckTopology S).overPullback RingCat U).map
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom))).obj M).IsQuasicoherent) (ι : Type u) (g : SheafOfModules.free ι ⟶ M) :
    ((SheafOfModules.restrictScalars
      (((Opens.grothendieckTopology S).overPullback RingCat U).map
        ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map
          A.hom))).obj (Limits.kernel g)).IsQuasicoherent := by
  let α := ((Opens.grothendieckTopology S).overPullback RingCat U).map
    ((sheafCompose (Opens.grothendieckTopology S) (forget₂ CommRingCat RingCat)).map A.hom)
  let ρ := SheafOfModules.restrictScalars α
  have := (scalarRestriction_preservesLimitsAndColimits α).1
  have := (scalarRestriction_preservesLimitsAndColimits α).2
  let F := ρ ⋙ (overEquiv U).functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have hunit : (F.obj (SheafOfModules.unit _)).IsQuasicoherent := by
    have := hA
    change ((overEquiv U).functor.obj (A.toModule.over U)).IsQuasicoherent
    exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((overFunctorEquiv U).app A.toModule).symm inferInstance
  have hfree : (F.obj (SheafOfModules.free (R := _) ι)).IsQuasicoherent := by
    have : ∀ i : ι, (F.obj (SheafOfModules.unit _)).IsQuasicoherent := fun _ ↦ hunit
    have := isQuasicoherent_sigma (fun _ : ι ↦ F.obj (SheafOfModules.unit _))
    exact (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (PreservesCoproduct.iso F (fun _ : ι ↦ SheafOfModules.unit _)).symm inferInstance
  have := hM
  have hFM : (F.obj M).IsQuasicoherent := (quasiCoherent_slice_iff_open U (ρ.obj M)).mp hM
  have := isQuasicoherent_kernel (F.map g)
  have hFK : (F.obj (kernel g)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (PreservesKernel.iso F g).symm inferInstance
  exact (quasiCoherent_slice_iff_open U (ρ.obj (kernel g))).mpr hFK

end AlgebraicGeometry.Scheme.Modules
