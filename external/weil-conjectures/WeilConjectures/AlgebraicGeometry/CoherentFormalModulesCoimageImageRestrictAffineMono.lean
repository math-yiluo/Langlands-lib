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
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem affine_formal_equivalence (Y : Scheme.{u}) [IsNoetherian Y]
    [IsAffine Y] (J : Y.IdealSheafData) :
    ∃ L : Ideal Γ(Y, ⊤), Nonempty (CoherentFormalModule Y J ≌
      FGModuleCat.{u} (AdicCompletion L Γ(Y, ⊤))) := by
  classical
  let A := Γ(Y, ⊤)
  have : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : IsNoetherian (Spec A) := {}
  let e := Y.isoSpec
  let K := J.comap e.inv
  let L : Ideal A := (K.ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso A).hom.hom
  have hK : K = Scheme.IdealSheafData.ofIdealTop
      (L.map (Scheme.ΓSpecIso A).inv.hom) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, L, Ideal.map_map]
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
    simp
  obtain ⟨E₁⟩ := coherentFormalModules_iso_equivalence J e
  obtain ⟨E₂, _⟩ := coherentFormalModules_affine A L K hK
  exact ⟨L, ⟨E₁.trans E₂⟩⟩

private theorem restriction_preservesCokernel {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens) [IsNoetherian U.toScheme]
    {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    PreservesColimit (parallelPair α 0) (coherentFormalModulesRestriction I U) := by
  let R := coherentFormalModulesRestriction I U
  let j := (IsCoherentFormalModule (I.comap U.ι)).ι
  let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
    (Scheme.Modules.restrictFunctor U.ι)
  have := coherentFormalModules_closedUnderCokernels X I
  have : PreservesColimit (parallelPair α 0) (IsCoherentFormalModule I).ι :=
    (IsCoherentFormalModule I).preservesCokernels_ι α
  have : PreservesColimit (parallelPair α 0) (R ⋙ j) := by
    change PreservesColimit (parallelPair α 0) ((IsCoherentFormalModule I).ι ⋙ W)
    infer_instance
  exact preservesColimit_of_reflects_of_preserves R j

set_option backward.isDefEq.respectTransparency false in
/-- The affine restriction of the coimage-image comparison is monic.
Source: Stacks Project, Lemma 087X, affine calculation of Coim=Im.
(blueprint: lem-weil-pbc-coherent-formal-coimage-image-affine-mono).

Proof: On an affine open, the coherent formal module equivalence identifies the
comparison with the map from a module modulo its kernel to its image. The first
isomorphism theorem makes this map injective; restriction and associated sheaf
preserve that injectivity. The argument is independent of the chosen kernel and
cokernel structures because their universal comparison isomorphisms conjugate
the map. -/
theorem coherentFormalModules_coimageImage_isMono_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    Mono ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  classical
  have : IsNoetherian (U : X.Opens).toScheme := {}
  let R := coherentFormalModulesRestriction I (U : X.Opens)
  obtain ⟨L, ⟨E⟩⟩ :=
    affine_formal_equivalence (U : X.Opens).toScheme (I.comap (U : X.Opens).ι)
  have : IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let := AdicCompletion.isNoetherianRing L
  let : HasFiniteProducts (CoherentFormalModule (U : X.Opens).toScheme
      (I.comap (U : X.Opens).ι)) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  let : Abelian (CoherentFormalModule (U : X.Opens).toScheme (I.comap (U : X.Opens).ι)) :=
    abelianOfEquivalence E.functor
  have := coherentFormalModules_restriction_preservesKernel I (U : X.Opens) α
  have := coherentFormalModules_restriction_preservesKernel I (U : X.Opens) (cokernel.π α)
  have := restriction_preservesCokernel I (U : X.Opens) α
  have := restriction_preservesCokernel I (U : X.Opens) (kernel.ι α)
  have : IsIso (Abelian.coimageImageComparison (R.map α)) := by
    exact Abelian.instIsIsoCoimageImageComparison (R.map α)
  have h := Abelian.PreservesCoimage.hom_coimageImageComparison R α
  have : IsIso (R.map (Abelian.coimageImageComparison α)) :=
    IsIso.of_isIso_fac_right h.symm
  let T := (IsCoherentFormalModule (I.comap (U : X.Opens).ι)).ι ⋙
    (evaluation ℕᵒᵖ (U : X.Opens).toScheme.Modules).obj (op n)
  have := T.map_isIso (R.map (Abelian.coimageImageComparison α))
  change Mono (T.map (R.map (Abelian.coimageImageComparison α)))
  infer_instance

end AlgebraicGeometry
