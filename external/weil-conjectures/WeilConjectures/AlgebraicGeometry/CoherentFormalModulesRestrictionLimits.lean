/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCokernelClosure
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionKernelFactorization
import all WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelConstruction
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelFactorization
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Restriction preserves finite limits and colimits of formal modules

Source: Stacks Project, Lemma 087X (2), final sentence of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem restricted_construction_mono {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) [IsNoetherian U.toScheme]
    {K F : CoherentFormalModule X I} (ι : K ⟶ F) (c : ℕ)
    (hz : ∀ n : ℕ, kernel.ι (ι.hom.app (op (n + c))) ≫
      K.obj.map (homOfLE (Nat.le_add_right n c)).op = 0) :
    Mono ((coherentFormalModulesRestriction I U).map ι) := by
  apply formalMono_of_kernel_transition_zero _ c
  intro n
  change kernel.ι ((Scheme.Modules.restrictFunctor U.ι).map
    (ι.hom.app (op (n + c)))) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        (K.obj.map (homOfLE (Nat.le_add_right n c)).op) = 0
  rw [← PreservesKernel.iso_inv_ι (Scheme.Modules.restrictFunctor U.ι)
    (ι.hom.app (op (n + c))), Category.assoc, ← Functor.map_comp, hz n,
    Functor.map_zero, comp_zero]

private theorem restricted_kernel_mono {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) [IsNoetherian U.toScheme]
    {F H : CoherentFormalModule X I} (α : F ⟶ H)
    (t : KernelFork α) (ht : IsLimit t) :
    Mono ((coherentFormalModulesRestriction I U).map t.ι) := by
  classical
  obtain ⟨c, _, S, j, hS, K, ι, e, htrans, hcomp, hzero⟩ :=
    coherentFormalModule_kernel_construction I F H α
  have hjzero (m : ℕ) : j.app (op m) ≫ α.hom.app (op m) = 0 := by
    obtain ⟨a, ha⟩ := hS m
    let f := kernel.ι (α.hom.app (op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have hf : f ≫ α.hom.app (op m) = 0 := by
      dsimp only [f]
      rw [Category.assoc, α.hom.naturality, ← Category.assoc, kernel.condition, zero_comp]
    have himage : Abelian.image.ι f ≫ α.hom.app (op m) = 0 := by
      apply (cancel_epi (Abelian.factorThruImage f)).mp
      simpa only [← Category.assoc, Abelian.image.fac, comp_zero] using hf
    rw [← ha, Category.assoc]
    exact (congrArg (a.hom ≫ ·) himage).trans comp_zero
  have hιzero : ι ≫ α = 0 := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext a
    obtain ⟨n⟩ := a
    change ι.hom.app (op n) ≫ α.hom.app (op n) = 0
    have : Epi (formalModuleQuotientπ I (n + 1) (S.obj (op (n + c)))) := by
      dsimp only [formalModuleQuotientπ]
      infer_instance
    apply (cancel_epi (e n).hom).mp
    apply (cancel_epi (formalModuleQuotientπ I (n + 1) (S.obj (op (n + c))))).mp
    simp only [comp_zero]
    rw [← Category.assoc _ _ (α.hom.app (op n)),
      ← Category.assoc _ _ (α.hom.app (op n)), hcomp n, Category.assoc,
      α.hom.naturality, ← Category.assoc, hjzero, zero_comp]
  have : Mono ι := formalMono_of_kernel_transition_zero ι c hzero
  let k := KernelFork.ofι ι hιzero
  have hk : IsLimit k := by
    refine Fork.IsLimit.mk' _ fun s ↦ Classical.choice ?_
    obtain ⟨δ, hδ⟩ := coherentFormalModule_kernel_factorization
      I F H α c S j hS K ι e htrans hcomp s.pt s.ι (by simp)
    exact ⟨⟨δ, hδ, fun {m} hm ↦ (cancel_mono ι).mp (hm.trans hδ.symm)⟩⟩
  let a := IsLimit.conePointUniqueUpToIso hk ht
  have ha : a.inv ≫ ι = t.ι :=
    IsLimit.conePointUniqueUpToIso_inv_comp hk ht WalkingParallelPair.zero
  have := restricted_construction_mono I U ι c hzero
  rw [← ha, Functor.map_comp]
  infer_instance

/-- The explicit termwise restriction functor preserves finite limits and colimits.
Source: Stacks Project, Lemma 087X, construction (a)--(d) and the last sentence
of its proof; step 2 of lem-weil-pbc-coherent-formal-modules-local-exactness.
(blueprint: lem-weil-pbc-coherent-formal-modules-restriction-limits)

Proof: Ambient cokernel closure makes the full-subcategory inclusion preserve
cokernels. Ordinary restriction preserves colimits, and the restricted inclusion
reflects them, so formal restriction preserves cokernels. For kernels, the
stabilized construction has zero transitions on its levelwise arrow kernels.
Epi transitions make the formal arrow monic. Ordinary restriction preserves
kernels and transports those zero-transition equations, so the restricted arrow
is also monic. Compare the constructed limiting fork with an arbitrary limiting
fork to transport this monicity. The restricted factorization-existence lemma
then supplies lifts, and cancellation proves their uniqueness. Finally use the
additive functor criteria for finite limits from kernels and finite colimits from
cokernels, with the finite biproduct instances supplied by abelianness. -/
theorem coherentFormalModules_restriction_limits {X : Scheme.{u}}
    [IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    [IsNoetherian U.toScheme] :
    PreservesFiniteLimits (coherentFormalModulesRestriction I U) ∧
      PreservesFiniteColimits (coherentFormalModulesRestriction I U) := by
  classical
  have : Abelian (CoherentFormalModule X I) :=
    Classical.choice (coherentFormalModule_abelian X I).1
  have : Abelian (CoherentFormalModule U.toScheme (I.comap U.ι)) :=
    Classical.choice (coherentFormalModule_abelian U.toScheme (I.comap U.ι)).1
  have : HasFiniteBiproducts (CoherentFormalModule X I) := by
    convert (Abelian.hasFiniteBiproducts (C := CoherentFormalModule X I)) using 1
    exact Subsingleton.elim _ _
  have : HasBinaryBiproducts (CoherentFormalModule X I) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have := coherentFormalModules_closedUnderCokernels X I
  have hc : ∀ {F G : CoherentFormalModule X I} (α : F ⟶ G),
      PreservesColimit (parallelPair α 0) (coherentFormalModulesRestriction I U) := by
    intro F G α
    have : PreservesColimit (parallelPair α 0) (IsCoherentFormalModule I).ι :=
      (IsCoherentFormalModule I).preservesCokernels_ι α
    have : PreservesColimit (parallelPair α 0)
        (coherentFormalModulesRestriction I U ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι) := by
      change PreservesColimit (parallelPair α 0)
        ((IsCoherentFormalModule I).ι ⋙
          (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
            (Scheme.Modules.restrictFunctor U.ι))
      infer_instance
    exact preservesColimit_of_reflects_of_preserves
      (coherentFormalModulesRestriction I U) (IsCoherentFormalModule (I.comap U.ι)).ι
  have hk : ∀ {F G : CoherentFormalModule X I} (α : F ⟶ G),
      PreservesLimit (parallelPair α 0) (coherentFormalModulesRestriction I U) := by
    intro F G α
    constructor
    intro c hc
    refine ⟨(KernelFork.isLimitMapConeEquiv c (coherentFormalModulesRestriction I U)).symm ?_⟩
    refine Fork.IsLimit.mk' _ fun s ↦ Classical.choice ?_
    have := restricted_kernel_mono I U α c hc
    obtain ⟨δ, hδ⟩ := coherentFormalModules_restriction_kernel_factorization
      I U α c hc s.pt s.ι (by simp)
    exact ⟨⟨δ, hδ, fun {m} hm ↦
      (cancel_mono ((coherentFormalModulesRestriction I U).map (Fork.ι c))).mp
        (hm.trans hδ.symm)⟩⟩
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
    Functor.preservesFiniteColimits_of_preservesCokernels _⟩

end AlgebraicGeometry
