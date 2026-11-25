/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineLimitModel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionLimits
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-! # Annihilators of affine limits of formal kernels and cokernels -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The affine-limit description of a formal kernel and cokernel preserves their
annihilator ideals over the ring of sections. This statement has no auxiliary ideal,
exponent, or covering hypothesis.

Source: Stacks Project, Lemma 087W and the affine calculation in Lemma 087X
(blueprint: lem-weil-pbc-formal-kernel-cokernel-limit-annihilators).

Proof: Restrict the limiting fork and colimiting cofork to V. Exact restriction
(Lemma 087X (2)) preserves their universal properties. Identify V with the spectrum
of its section ring A and apply Lemma 087W: the restricted category is equivalent
to finite modules over the I(V)-adic completion of A, with underlying A-module the
inverse limit of affine sections, naturally on morphisms. Equivalences preserve
kernels and cokernels. Finite modules over this Noetherian completed ring are closed
under both operations, and restriction of scalars preserves kernels and cokernels.
The resulting A-linear isomorphisms identify the limit of k with the linear kernel
of the limit map and the limit of c with the quotient by its range. Annihilator
ideals are invariant under linear equivalence (LinearEquiv.annihilator_eq), giving
the two equalities. This uses the formal kernel, not a termwise kernel. For an empty
V all section modules are zero and both annihilators are the unit ideal. -/
theorem coherentFormalModule_limit_annihilators
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (k : KernelFork α) (c : CokernelCofork α) (hk : IsLimit k) (hc : IsColimit c)
    (V : X.affineOpens) :
    Module.annihilator Γ(X, V.1)
      (limit (k.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
        ModuleCat Γ(X, V.1)) =
      Module.annihilator Γ(X, V.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom) ∧
    Module.annihilator Γ(X, V.1)
      (limit (c.pt.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
        ModuleCat Γ(X, V.1)) =
      Module.annihilator Γ(X, V.1)
        (↥(limit (G.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)) :
          ModuleCat Γ(X, V.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op V.1)))).hom) := by
  let L : CoherentFormalModule X I ⥤ ModuleCat Γ(X, V.1) :=
    (IsCoherentFormalModule I).ι ⋙
      (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat Γ(X, V.1))).obj
        (SheafOfModules.evaluation X.ringCatSheaf (op V.1)) ⋙ lim
  have : TopologicalSpace.NoetherianSpace V.1.toScheme :=
    (Scheme.Hom.isOpenEmbedding V.1.ι).isInducing.noetherianSpace
  have : IsNoetherian V.1.toScheme := {
    toIsLocallyNoetherian := inferInstance
    isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have : IsNoetherianRing (AdicCompletion (I.ideal V) Γ(X, V.1)) :=
    AdicCompletion.isNoetherianRing (I.ideal V)
  let P : ObjectProperty (ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1))) :=
    fun N ↦ Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N
  have : P.IsClosedUnderSubobjects := by
    constructor
    intro M N f hf hN
    have : Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N := hN
    have := isNoetherian_of_injective f.hom ((ModuleCat.mono_iff_injective f).mp hf)
    exact inferInstanceAs (Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) M)
  have : P.IsClosedUnderQuotients := by
    constructor
    intro M N f hf hM
    have : Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) M := hM
    exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)
  obtain ⟨E, ⟨e⟩⟩ := coherentFormalModule_affine_limit_model X I V
  let R := coherentFormalModulesRestriction I V.1
  let S := ModuleCat.restrictScalars
    (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))
  let T := R ⋙ E.functor ⋙ P.ι ⋙ S
  have : PreservesFiniteLimits R := (coherentFormalModules_restriction_limits I V.1).1
  have : PreservesFiniteColimits R := (coherentFormalModules_restriction_limits I V.1).2
  have : PreservesLimit (parallelPair α 0) T := by
    have hR := k.mapIsLimit hk R
    have hE := (k.map R).mapIsLimit hR E.functor
    have : PreservesLimit (parallelPair (E.functor.map (R.map α)) 0) P.ι :=
      P.preservesKernels_ι _
    have hP := ((k.map R).map E.functor).mapIsLimit hE P.ι
    have hS := (((k.map R).map E.functor).map P.ι).mapIsLimit hP S
    apply preservesLimit_of_preserves_limit_cone hk
    exact (k.isLimitMapConeEquiv T).symm hS
  have : PreservesColimit (parallelPair α 0) T := by
    have hR := c.mapIsColimit hc R
    have hE := (c.map R).mapIsColimit hR E.functor
    have : PreservesColimit (parallelPair (E.functor.map (R.map α)) 0) P.ι :=
      P.preservesCokernels_ι _
    have hP := ((c.map R).map E.functor).mapIsColimit hE P.ι
    have hS := (((c.map R).map E.functor).map P.ι).mapIsColimit hP S
    apply preservesColimit_of_preserves_colimit_cocone hc
    exact (c.isColimitMapCoconeEquiv T).symm hS
  have : PreservesLimit (parallelPair α 0) L :=
    preservesLimit_of_natIso _ e.symm
  have : PreservesColimit (parallelPair α 0) L :=
    preservesColimit_of_natIso _ e.symm
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_iso e.symm
  let ek := IsLimit.conePointUniqueUpToIso (k.mapIsLimit hk L) (kernelIsKernel (L.map α))
  let ec := IsColimit.coconePointUniqueUpToIso
    (c.mapIsColimit hc L) (cokernelIsCokernel (L.map α))
  constructor
  · exact (ek ≪≫ ModuleCat.kernelIsoKer (L.map α)).toLinearEquiv.annihilator_eq
  · exact (ec ≪≫ ModuleCat.cokernelIsoRangeQuotient (L.map α)).toLinearEquiv.annihilator_eq

end AlgebraicGeometry
