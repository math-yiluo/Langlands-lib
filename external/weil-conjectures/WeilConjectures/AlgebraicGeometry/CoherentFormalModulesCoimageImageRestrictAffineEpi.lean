/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCokernelClosure
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesRestrictionKernels
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer

/-! # Epimorphic affine restriction of the formal coimage-image comparison

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem affine_formal_equivalence (X : Scheme.{u}) [IsNoetherian X]
    [IsAffine X] (I : X.IdealSheafData) :
    ∃ (A : CommRingCat.{u}) (K : Ideal A), IsNoetherianRing (AdicCompletion K A) ∧
      Nonempty (CoherentFormalModule X I ≌ FGModuleCat.{u} (AdicCompletion K A)) := by
  classical
  let A := Γ(X, ⊤)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian
    ⟨⊤, isAffineOpen_top X⟩
  let J := I.comap X.isoSpec.inv
  let K : Ideal A := (J.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso A).hom.hom
  have hJ : J = Scheme.IdealSheafData.ofIdealTop
      (K.map (Scheme.ΓSpecIso A).inv.hom) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [K, Ideal.map_map, ← CommRingCat.hom_comp]
  obtain ⟨E, _⟩ := coherentFormalModules_affine A K J hJ
  obtain ⟨T⟩ := coherentFormalModules_iso_equivalence I X.isoSpec
  exact ⟨A, K, AdicCompletion.isNoetherianRing K, ⟨T.trans E⟩⟩

private theorem restriction_preserves_cokernel {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) [IsNoetherian U.toScheme]
    {F G : CoherentFormalModule X I} (f : F ⟶ G) :
    PreservesColimit (parallelPair f 0) (coherentFormalModulesRestriction I U) := by
  have := coherentFormalModules_closedUnderCokernels X I
  have : PreservesColimit (parallelPair f 0) (IsCoherentFormalModule I).ι :=
    (IsCoherentFormalModule I).preservesCokernels_ι f
  let R := coherentFormalModulesRestriction I U
  let V := (IsCoherentFormalModule (I.comap U.ι)).ι
  have : PreservesColimit (parallelPair f 0) (R ⋙ V) := by
    change PreservesColimit (parallelPair f 0)
      ((IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι))
    infer_instance
  exact preservesColimit_of_reflects_of_preserves R V

/-- The affine restriction of the coimage-image comparison is epic.
Source: Stacks Project, Lemma 087X, affine calculation of Coim=Im.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image-affine-epi).

Proof: On an affine open, the coherent formal module equivalence identifies the
comparison with the map from a module modulo its kernel onto its image. The first
isomorphism theorem makes this map surjective; restriction and associated sheaf
preserve that surjectivity. The conclusion is invariant under the unique
isomorphisms between supplied kernel and cokernel structures. -/
theorem coherentFormalModules_coimageImage_isEpi_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    Epi ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  classical
  have : IsNoetherian (U : X.Opens).toScheme := {}
  obtain ⟨A, K, hK, ⟨e⟩⟩ :=
    affine_formal_equivalence (U : X.Opens).toScheme (I.comap (U : X.Opens).ι)
  have : IsNoetherianRing (AdicCompletion K A) := hK
  have : HasFiniteProducts (CoherentFormalModule (U : X.Opens).toScheme
      (I.comap (U : X.Opens).ι)) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let : Abelian (CoherentFormalModule (U : X.Opens).toScheme
      (I.comap (U : X.Opens).ι)) := abelianOfEquivalence e.functor
  let R := coherentFormalModulesRestriction I (U : X.Opens)
  have : PreservesLimit (parallelPair α 0) R :=
    coherentFormalModules_restriction_preservesKernel I (U : X.Opens) α
  have : PreservesLimit (parallelPair (cokernel.π α) 0) R :=
    coherentFormalModules_restriction_preservesKernel I (U : X.Opens) (cokernel.π α)
  have : PreservesColimit (parallelPair α 0) R :=
    restriction_preserves_cokernel I (U : X.Opens) α
  have : PreservesColimit (parallelPair (kernel.ι α) 0) R :=
    restriction_preserves_cokernel I (U : X.Opens) (kernel.ι α)
  have : IsIso (R.map (Abelian.coimageImageComparison α)) := by
    rw [Arrow.isIso_iff_isIso_of_isIso
      (Abelian.PreservesCoimageImageComparison.iso R α).hom]
    infer_instance
  let V := (IsCoherentFormalModule (I.comap (U : X.Opens).ι)).ι ⋙
    (evaluation ℕᵒᵖ (U : X.Opens).toScheme.Modules).obj (op n)
  change Epi (V.map (R.map (Abelian.coimageImageComparison α)))
  infer_instance

end AlgebraicGeometry
