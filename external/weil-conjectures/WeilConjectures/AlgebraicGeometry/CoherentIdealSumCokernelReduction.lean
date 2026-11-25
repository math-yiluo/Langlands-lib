/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.CategoryTheory.NatIso

/-! # The smaller-support cokernel of an ideal-sum inclusion

Source: Stacks Project, Tag 01YF, final paragraph, using Tag 01YE.
(blueprint: lem-weil-pbc-coherent-ideal-sum-cokernel-reduction)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- An ideal-sum inclusion which is invertible near a nonzero stalk has a nonzero
ideal, coherent source and cokernel, and strictly smaller cokernel support.
Source: Stacks Project, Tag 01YF (`lemma-coherent-filter`), final paragraph,
using the coherent inclusion of Tag 01YE (`lemma-prepare-filter-irreducible`).
(blueprint: lem-weil-pbc-coherent-ideal-sum-cokernel-reduction)

Proof: the closed subscheme is locally Noetherian, since a closed immersion is
locally of finite type. Finite sums of its coherent ideal are coherent, as is their
finite pushforward. Coherent cokernel closure proves coherence of the cokernel.
If I were zero, all its summands and their pushforward would be zero. The local
isomorphism would force the target stalk at x to be zero, contradicting hx.
The cokernel projection is an epimorphism, hence is surjective on stalks: its
support is contained in the support of F. Restriction to W preserves cokernels;
the cokernel of the restricted isomorphism is zero. In particular its stalk at x
is zero. Thus x belongs to the support of F but not to that of the cokernel,
proving strict containment. This reasoning allows r = 0 syntactically, but the
nonzero target stalk excludes that case as well. -/
theorem coherent_ideal_sum_cokernel_reduction
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (r : ℕ) (I : Z.IdealSheafData)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (α : (pushforward i).obj (∐ fun _ : Fin r => I.toModules) ⟶ F)
    (x : X) (hx : ¬ Subsingleton (F.presheaf.stalk x))
    (W : X.Opens) (hxW : x ∈ W)
    (hαW : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α)) :
    I ≠ ⊥ ∧
      RingedSpace.IsCoherent X.toRingedSpace
        ((pushforward i).obj (∐ fun _ : Fin r => I.toModules)) ∧
      RingedSpace.IsCoherent X.toRingedSpace (cokernel α) ∧
      {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} ⊂
        {y : X | ¬ Subsingleton (F.presheaf.stalk y)}   := by
  classical
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum Z.toRingedSpace
  have hsum : RingedSpace.IsCoherent Z.toRingedSpace
      (∐ fun _ : Fin r => I.toModules) := by
    exact hclosure.2.2.2.2 _ _ (biproduct.isoCoproduct _) (hclosure.2.2.1 r _ (fun _ => hI))
  have hA := (isCoherent_pushforward_of_isFinite i _ hsum).1
  have hQ := (RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace).1 _ _ α hA hF |>.2
  have : IsIso ((SheafOfModules.overFunctor X.ringCatSheaf W).map α) := hαW
  have : IsIso ((restrictFunctor W.ι).map α) := by
    apply (NatIso.isIso_map_iff (overFunctorEquiv W) α).mp
    change IsIso ((overEquiv W).functor.map
      ((SheafOfModules.overFunctor X.ringCatSheaf W).map α))
    infer_instance
  have hbij : Function.Bijective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map α) :=
    bijective_stalk_of_isIso_restrict α x hxW
  have qsurj (y : X) : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).map (cokernel.π α)) := by
    have : Epi ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).map
      (cokernel.π α)) :=
      ((RingedSpace.module_stalk_exact X.toRingedSpace α).2.2.1 y).1
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hQx : Subsingleton ((cokernel α).presheaf.stalk x) := by
    refine ⟨fun a b => ?_⟩
    have hz (a : (cokernel α).presheaf.stalk x) : a = 0 := by
      obtain ⟨a', rfl⟩ := qsurj x a
      obtain ⟨a'', rfl⟩ := hbij.2 a'
      have hcomp := congrArg
        (fun f => f a'')
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_comp α (cokernel.π α))
      rw [cokernel.condition, Functor.map_zero] at hcomp
      exact hcomp.symm
    exact (hz a).trans (hz b).symm
  have hsub : {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} ⊆
      {y : X | ¬ Subsingleton (F.presheaf.stalk y)} := by
    intro y hy hFy
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace y).obj F) := hFy
    exact hy ((qsurj y).subsingleton)
  refine ⟨?_, hA, hQ, ?_⟩
  · intro hbot
    have hzI : IsZero I.toModules := by
      apply isZero_of_forall_affineOpens
      intro V
      refine ⟨fun a b => ?_⟩
      apply I.injective_toModulesι_app V.1
      have zero (a : Γ(I.toModules, V.1)) : I.toModulesι.app V.1 a = 0 := by
        have ha : I.toModulesι.app V.1 a ∈ (I.ideal V : Set Γ(Z, V.1)) := by
          rw [← I.range_toModulesι_app V]
          exact Set.mem_range_self a
        simpa [hbot] using ha
      exact (zero a).trans (zero b).symm
    have hzsum : IsZero (∐ fun _ : Fin r => I.toModules) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Sigma.hom_ext
      intro j
      exact hzI.eq_of_src _ _
    have hzA := (pushforward i).map_isZero hzsum
    have hAx : Subsingleton
        (((pushforward i).obj (∐ fun _ : Fin r => I.toModules)).presheaf.stalk x) := by
      exact ModuleCat.subsingleton_of_isZero
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero hzA)
    have : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((pushforward i).obj (∐ fun _ : Fin r => I.toModules))) := hAx
    exact hx (hbij.2.subsingleton)
  · apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hxQ : x ∈ {y : X | ¬ Subsingleton ((cokernel α).presheaf.stalk y)} := by
      rw [heq]
      exact hx
    exact hxQ hQx


end AlgebraicGeometry.Scheme.Modules
