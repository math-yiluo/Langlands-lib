/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory

import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Quasi-coherent cohomology is closed under extensions of complexes

Source: Stacks Project, Tags 0117 and 01IE.
(blueprint: lem-sc-localized-complex-qc-homology-extension)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem qc_overEquiv (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  let := hM
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over W)
      (((Opens.grothendieckTopology X).over U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.functor) _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

private theorem qc_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let := hM
  have : ∀ W, (Over.post (X := W) U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over W)
      ((Opens.grothendieckTopology ↥U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.functor) _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

private theorem mapped_homology_mem_of_shortExact
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (P : ObjectProperty D) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions] (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact)
    (h₁ : ∀ i : ℤ, P (F.obj (S.X₁.homology i)))
    (h₃ : ∀ i : ℤ, P (F.obj (S.X₃.homology i))) (n : ℤ) :
    P (F.obj (S.X₂.homology n)) := by
  exact P.prop_of_exact_of_exact_of_exact
    ((hS.homology_exact₁ (n - 1) n (by simp)).map F)
    ((hS.homology_exact₂ n).map F)
    ((hS.homology_exact₃ n (n + 1) (by simp)).map F)
    (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1))

/-- The middle of a short exact sequence has quasi-coherent cohomology when both ends do.

Source: Stacks Project, Tag 0117, long exact sequence, and Tag 01IE, extension closure.
Proof: in degree n the long exact sequence has the five exact terms
H^(n-1)(C), H^n(A), H^n(B), H^n(C), H^(n+1)(A).
Consequently H^n(B) is an extension of ker(H^n(C) -> H^(n+1)(A)) by
coker(H^(n-1)(C) -> H^n(A)). The hypotheses make the four outer terms
quasi-coherent. Transport to U.toScheme by the exact equivalence of module sheaves
on its open site with those on the localized site over U. Quasi-coherence is
preserved in both directions because local free presentations correspond.
Kernel and cokernel closure make the two end terms quasi-coherent, and extension
closure makes the middle term quasi-coherent. Transport back. This argument works
for every integer n and imposes no boundedness on any of the complexes.
(blueprint: lem-sc-localized-complex-qc-homology-extension). -/
theorem localized_complex_qc_homology_extension
    (X : Scheme.{u}) (U : X.Opens)
    (S : ShortComplex (CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ))
    (hS : S.ShortExact)
    (h₁ : ∀ i : ℤ, (S.X₁.homology i).IsQuasicoherent)
    (h₃ : ∀ i : ℤ, (S.X₃.homology i).IsQuasicoherent) (n : ℤ) :
    (S.X₂.homology n).IsQuasicoherent := by
  -- Share the abelian structure across the localized homology computations.
  let : Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance
  let e := Scheme.Modules.overEquiv U
  let F := e.functor
  let P : ObjectProperty U.toScheme.Modules :=
    fun M ↦ M.IsQuasicoherent
  let : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).IsClosedUnderIsomorphisms
  -- Pass the quasi-coherence proofs explicitly to avoid repeating site instance inference.
  let : P.IsClosedUnderKernels := ⟨by
    rintro _ @⟨M, N, f, k, hk, hM, hN⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (@Scheme.Modules.isQuasicoherent_kernel U.toScheme M N hM hN f)⟩
  let : P.IsClosedUnderCokernels := ⟨by
    rintro _ @⟨M, N, f, k, hk, hM, hN⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (@Scheme.Modules.isQuasicoherent_cokernel U.toScheme M N hM hN f)⟩
  let : P.IsClosedUnderExtensions := ⟨by
    intro T hT h₁ h₃
    exact @Scheme.Modules.isQuasicoherent_of_shortExact U.toScheme T hT h₁ h₃⟩
  have hqc : P (F.obj (S.X₂.homology n)) :=
    mapped_homology_mem_of_shortExact F P S hS
      (fun i ↦ qc_overEquiv X U _ (h₁ i)) (fun i ↦ qc_overEquiv X U _ (h₃ i)) n
  have hinv := qc_overEquiv_inverse X U _ hqc
  exact (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over U)).prop_of_iso
    (e.unitIso.app (S.X₂.homology n)).symm hinv

end AlgebraicGeometry
