/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.Modules.ConstantRankMapNormalForm
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Kernel and image of a constant rank map on a reduced scheme
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem kernel_image_of_block_form
    {C : Type*} [Category C] [Abelian C] {S T A B D : C}
    (f : S ⟶ T) (eS : S ≅ A ⊞ B) (eT : T ≅ B ⊞ D)
    (h : f = eS.hom ≫ biprod.snd ≫ biprod.inl ≫ eT.inv) :
    Nonempty (kernel f ≅ A) ∧ Nonempty (Abelian.image f ≅ B) ∧
      IsSplitMono (Abelian.image.ι f) := by
  let p : S ⟶ B := eS.hom ≫ biprod.snd
  let i : B ⟶ T := biprod.inl ≫ eT.inv
  have hi : p ≫ i = f := by simpa [p, i, Category.assoc] using h.symm
  let e : B ≅ Abelian.image f :=
    image.isoStrongEpiMono p i hi ≪≫ (Abelian.imageIsoImage f).symm
  have he' : (Abelian.imageIsoImage f).inv ≫ Abelian.image.ι f = image.ι f := by
    change (Abelian.imageIsoImage f).inv ≫ kernel.ι (cokernel.π f) = image.ι f
    rw [← Abelian.imageIsoImage_hom_comp_image_ι]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he : e.hom ≫ Abelian.image.ι f = i := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, he',
      image.isoStrongEpiMono_hom_comp_ι]
  refine ⟨⟨kernelIsoOfEq h ≪≫ kernelIsIsoComp eS.hom _ ≪≫
    kernelCompMono biprod.snd i ≪≫ kernelBiprodSndIso⟩, ⟨e.symm⟩, ?_⟩
  refine ⟨⟨{ retraction := eT.hom ≫ biprod.fst ≫ e.hom, id := ?_ }⟩⟩
  rw [← cancel_epi e.hom, ← Category.assoc e.hom (Abelian.image.ι f), he]
  simp [i]

/-- A constant rank map between finite free sheaves has a finite locally free kernel
and image, and its image inclusion admits retractions locally on the open subscheme. -/
theorem kernel_image_pullback_of_constantRank
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ)
    (hrank : ∀ z : Z, ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
      Set.range g.base = {j.base z} ∧
      ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank = a) :
    (kernel ((Modules.pullback j).map φ)).IsFiniteLocallyFreeOfRank (m - a) ∧
    (Abelian.image ((Modules.pullback j).map φ)).IsFiniteLocallyFreeOfRank a ∧
    ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map
        (Abelian.image.ι ((Modules.pullback j).map φ))) := by
  classical
  let ψ := (Modules.pullback j).map φ
  choose U hU eS eT hφ using
    exists_local_normal_form_of_constantRank eM eN φ j a hrank
  have hlocal (z : Z) := kernel_image_of_block_form
    ((restrictFunctor (U z).ι).map ψ) (eS z) (eT z) (hφ z)
  have hcover : ⨆ z, U z = ⊤ := by
    exact eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hU z⟩
  have hk (z : Z) : Nonempty
      ((kernel ψ).restrict (U z).ι ≅ free (ULift.{u} (Fin (m - a)))) :=
    ⟨PreservesKernel.iso (restrictFunctor (U z).ι) ψ ≪≫ (hlocal z).1.some⟩
  have hi (z : Z) : Nonempty
      ((Abelian.image ψ).restrict (U z).ι ≅ free (ULift.{u} (Fin a))) :=
    ⟨Abelian.PreservesImage.iso (restrictFunctor (U z).ι) ψ ≪≫ (hlocal z).2.1.some⟩
  refine ⟨isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun z ↦ (U z).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hcover) hk,
    isFiniteLocallyFreeOfRank_of_restrict_iso_free _ (fun z ↦ (U z).ι)
      (by simpa only [Scheme.Opens.opensRange_ι] using hcover) hi, ?_⟩
  intro z
  refine ⟨U z, hU z, ?_⟩
  have := (hlocal z).2.2
  let e := Abelian.PreservesImage.iso (restrictFunctor (U z).ι) ψ
  refine ⟨⟨{ retraction := retraction (Abelian.image.ι
      ((restrictFunctor (U z).ι).map ψ)) ≫ e.inv, id := ?_ }⟩⟩
  rw [← Abelian.PreservesImage.iso_hom_ι, Category.assoc,
    IsSplitMono.id_assoc, Iso.hom_inv_id]

end AlgebraicGeometry.Scheme.Modules
