/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Homology of a short complex with locally split boundaries
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- The cokernel of a split inclusion between finite locally free modules of fixed ranks
is finite locally free of the difference of the ranks. -/
private theorem isFiniteLocallyFreeOfRank_cokernel_of_splitMono
    {Z : Scheme.{u}} {M N : Z.Modules} (f : M ⟶ N) (k b : ℕ)
    [M.IsFiniteLocallyFreeOfRank b] [N.IsFiniteLocallyFreeOfRank k] [IsSplitMono f] :
    (cokernel f).IsFiniteLocallyFreeOfRank (k - b) := by
  have := IsFiniteLocallyFreeOfRank.isLocallyFree M b
  have := IsFiniteLocallyFreeOfRank.isLocallyFree N k
  have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N k
  have := isQuasicoherent_cokernel f
  let T := ShortComplex.cokernelSequence f
  let t := ShortComplex.Splitting.ofExactOfRetraction T
    (ShortComplex.cokernelSequence_exact f) (retraction f) (IsSplitMono.id f)
    (by dsimp [T, ShortComplex.cokernelSequence]; infer_instance)
  apply isFiniteLocallyFreeOfRank_of_isAffineOpen
  intro U hU
  obtain ⟨hfp, hproj⟩ := finitePresentation_projective_sections N hU
  let F := SheafOfModules.evaluation Z.ringCatSheaf (Opposite.op U)
  have : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  let s := t.map F
  let e : Γ(N, U) ≃ₗ[Γ(Z, U)] Γ(M, U) × Γ(cokernel f, U) :=
    (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  let q : Γ(N, U) →ₗ[Γ(Z, U)] Γ(cokernel f, U) := ((T.map F).g).hom
  let j : Γ(cokernel f, U) →ₗ[Γ(Z, U)] Γ(N, U) := s.s.hom
  have hsplit : q.comp j = LinearMap.id := by
    have h := congrArg ModuleCat.Hom.hom s.s_g
    change q.comp j = LinearMap.id at h
    exact h
  have hQfin : Module.Finite Γ(Z, U) Γ(cokernel f, U) :=
    Module.Finite.of_surjective q (by
      intro y
      exact ⟨j y, DFunLike.congr_fun hsplit y⟩)
  have hQproj : Module.Projective Γ(Z, U) Γ(cokernel f, U) :=
    Module.Projective.of_split j q hsplit
  have hQfp := Module.finitePresentation_of_projective Γ(Z, U) Γ(cokernel f, U)
  have hQflat : Module.Flat Γ(Z, U) Γ(cokernel f, U) := inferInstance
  have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree M b
  obtain ⟨hMfp, hMproj⟩ := finitePresentation_projective_sections M hU
  refine ⟨hQfp, hQflat, ?_⟩
  intro p
  have hr := congrFun (Module.rankAtStalk_eq_of_equiv e) p
  have hsum := congrFun (Module.rankAtStalk_prod (R := Γ(Z, U)) Γ(M, U)
    Γ(cokernel f, U)) p
  have hM := rankAtStalk_sections_eq M (r := b) hU p
  have hN := rankAtStalk_sections_eq N (r := k) hU p
  change Module.rankAtStalk Γ(N, U) p =
    Module.rankAtStalk (Γ(M, U) × Γ(cokernel f, U)) p at hr
  rw [hN, hsum, Pi.add_apply, hM] at hr
  omega


/-- The homology of a short complex is canonically isomorphic to the cokernel of the
induced map from its image to its kernel. This is the standard left-homology
identification in an abelian category.
-/
private theorem homology_iso_cokernel_imageToKernel
    {Z : Scheme.{u}} (S : ShortComplex Z.Modules) :
    Nonempty (S.homology ≅ cokernel S.abelianImageToKernel) := by
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = Abelian.factorThruImage S.f ≫ S.abelianImageToKernel := by
    apply (cancel_mono (kernel.ι S.g)).mp
    simp [f']
  let h : S.LeftHomologyData :=
    { K := kernel S.g
      H := cokernel S.abelianImageToKernel
      i := kernel.ι S.g
      π := cokernel.π S.abelianImageToKernel
      wi := kernel.condition S.g
      hi := kernelIsKernel S.g
      wπ := by
        change f' ≫ cokernel.π S.abelianImageToKernel = 0
        rw [hf', Category.assoc, cokernel.condition, comp_zero]
      hπ := CokernelCofork.IsColimit.ofπ _ _
        (fun a ha ↦ cokernel.desc S.abelianImageToKernel a (by
          change f' ≫ a = 0 at ha
          simpa only [← cancel_epi (Abelian.factorThruImage S.f),
            comp_zero, ← Category.assoc, ← hf'] using ha))
        (fun a ha ↦ cokernel.π_desc _ _ _)
        (fun a ha c hc ↦ coequalizer.hom_ext (by
          simpa only [cokernel.π_desc] using hc)) }
  exact ⟨h.homologyIso⟩

/-- If the image inclusion is locally split, the homology has the expected finite
locally free rank.
-/
private theorem isFiniteLocallyFreeOfRank_cokernel_imageToKernel_of_locally_split
    {Z : Scheme.{u}} (S : ShortComplex Z.Modules) (k b : ℕ)
    (hkernel : (kernel S.g).IsFiniteLocallyFreeOfRank k)
    (himage : (Abelian.image S.f).IsFiniteLocallyFreeOfRank b)
    (hsplit : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (Abelian.image.ι S.f))) :
    (cokernel S.abelianImageToKernel).IsFiniteLocallyFreeOfRank (k - b) := by
  classical
  choose U hz hU using hsplit
  apply isFiniteLocallyFreeOfRank_of_iSup_eq_top _ U
  · apply eq_top_iff.mpr
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hz z⟩
  · intro z
    let F := restrictFunctor (U z).ι
    have : IsSplitMono (F.map (Abelian.image.ι S.f)) := hU z
    have hs : IsSplitMono (F.map S.abelianImageToKernel) :=
      IsSplitMono.mk'
        { retraction := F.map (kernel.ι S.g) ≫ retraction (F.map (Abelian.image.ι S.f))
          id := by
            rw [← Category.assoc, ← F.map_comp,
              S.abelianImageToKernel_comp_kernel_ι, IsSplitMono.id] }
    have hK : (F.obj (kernel S.g)).IsFiniteLocallyFreeOfRank k := inferInstance
    have hI : (F.obj (Abelian.image S.f)).IsFiniteLocallyFreeOfRank b := inferInstance
    have hQ := isFiniteLocallyFreeOfRank_cokernel_of_splitMono
      (F.map S.abelianImageToKernel) k b
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (PreservesCokernel.iso F S.abelianImageToKernel).symm

/-- If the outgoing kernel and the incoming image are finite locally free, and the
incoming image is locally a direct summand of the middle term, homology is finite
locally free of the difference of their ranks. -/
theorem isFiniteLocallyFreeOfRank_homology_of_locally_split_image
    {Z : Scheme.{u}} (S : ShortComplex Z.Modules) (k b : ℕ)
    (hkernel : (kernel S.g).IsFiniteLocallyFreeOfRank k)
    (himage : (Abelian.image S.f).IsFiniteLocallyFreeOfRank b)
    (hsplit : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (Abelian.image.ι S.f))) :
    S.homology.IsFiniteLocallyFreeOfRank (k - b) := by
  obtain ⟨e⟩ := homology_iso_cokernel_imageToKernel S
  have hq := isFiniteLocallyFreeOfRank_cokernel_imageToKernel_of_locally_split
    S k b hkernel himage hsplit
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm

end AlgebraicGeometry.Scheme.Modules
