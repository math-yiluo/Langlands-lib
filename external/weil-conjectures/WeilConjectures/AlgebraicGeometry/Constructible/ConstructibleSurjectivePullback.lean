/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleColimitFactorization
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Constructibility descends through surjective pullback

Source: Stacks Project, Tag 095Q, lemma-check-constructible (3), for finite commutative rings
(blueprint: lem-weil-pbc-etale-constructible-surjective-pullback).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Constructibility of a module sheaf over a finite commutative ring can be checked after
surjective pullback between quasi-compact quasi-separated schemes.

Source: Stacks Project, Tag 095Q, lemma-check-constructible (3)
(blueprint: lem-weil-pbc-etale-constructible-surjective-pullback).

Proof:
1. Compare finite constant values with the source library's finite-stalk constructibility
   predicate and use `IsConstructibleSheaf.upperStar` for preservation by arbitrary pullback.
2. Present any sheaf H with constructible pullback as a filtered colimit of constructible
   sheaves. Pullback preserves this colimit since it is a left adjoint. Factor the identity
   of its constructible pullback through a pulled-back colimit leg, making that leg a split
   epimorphism. Surjective module pullback is faithful by the geometric-stalk comparison,
   so it reflects epimorphisms. Thus H is a quotient of a constructible sheaf.
3. Apply this to F, obtaining an epimorphism p : G ⟶ F with G constructible. Exactness of
   pullback and constructibility of kernels show that the pullback of kernel p is
   constructible. Apply step 2 again to obtain an epimorphism r : C ⟶ kernel p with C
   constructible.
4. The cokernel of r followed by the kernel inclusion is the cokernel of the kernel
   inclusion, hence F, since p is epi. Constructibility of cokernels completes the proof. -/
theorem isConstructibleEtaleModuleSheaf_iff_surjective_pullback
    {U V : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace V] [QuasiSeparatedSpace V] (f : V ⟶ U) [Surjective f]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModuleSheaf F ↔
      IsConstructibleEtaleModuleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) := by
  classical
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) f
  have : L.Faithful := Etale.faithful_upperStar_of_surjective Λ f f.surjective
  have pullback_constructible
      (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hG : IsConstructibleEtaleModuleSheaf G) :
      IsConstructibleEtaleModuleSheaf (L.obj G) := by
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mp hG
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.upperStar f G)
  refine ⟨pullback_constructible F, fun hF ↦ ?_⟩
  have quotient_presentation
      (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hH : IsConstructibleEtaleModuleSheaf (L.obj H)) :
      ∃ (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (p : G ⟶ H), IsConstructibleEtaleModuleSheaf G ∧ Epi p := by
    obtain ⟨A, hA, hfiltered, D, hD, ι, ⟨hc⟩⟩ :=
      exists_filtered_colimit_constructible H
    let := hA
    let := hfiltered
    have hLc := Limits.isColimitOfPreserves L hc
    obtain ⟨a, q, hq⟩ := exists_constructible_hom_of_isColimit
      (L.obj H) hH hLc (𝟙 (L.obj H))
    have : Epi (L.map (ι.app a)) := epi_of_epi_fac hq
    exact ⟨D.obj a, ι.app a, hD a, L.epi_of_epi_map inferInstance⟩
  obtain ⟨G, p, hG, hp⟩ := quotient_presentation F hF
  let := hp
  have hGp := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
    (pullback_constructible G hG)
  have hFp := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hF
  have hKp := IsConstructibleSheaf.kernel (L.map p)
  have hK : IsConstructibleEtaleModuleSheaf (L.obj (Limits.kernel p)) := by
    apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
    exact IsConstructibleSheaf.of_iso (Limits.PreservesKernel.iso L p).symm
  obtain ⟨C, r, hC, hr⟩ := quotient_presentation (Limits.kernel p) hK
  let := hr
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hG
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hC
  have := IsConstructibleSheaf.cokernel (r ≫ Limits.kernel.ι p)
  apply (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  apply IsConstructibleSheaf.of_iso (F := Limits.cokernel (r ≫ Limits.kernel.ι p))
  exact Limits.cokernelEpiComp r (Limits.kernel.ι p) ≪≫
    (Limits.cokernelIsCokernel (Limits.kernel.ι p)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel
        (Limits.KernelFork.ofι (Limits.kernel.ι p) (Limits.kernel.condition p))
        (Limits.kernelIsKernel p))

end AlgebraicGeometry.Scheme
