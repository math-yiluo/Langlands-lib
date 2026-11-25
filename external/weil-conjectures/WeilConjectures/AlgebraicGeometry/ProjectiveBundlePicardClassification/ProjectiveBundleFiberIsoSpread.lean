/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberHomLift
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeMapIsoLocusPullback
import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocusPullback
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Spreading an isomorphism of lines on a projective-bundle fibre

## References

* EGA II, Remark 4.2.7 (classification announcement)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules

/-- Two lines that are isomorphic on one projective-bundle fibre become isomorphic
above a neighbourhood of that base point. No degree or tautological quotient is used.
The isomorphism on the neighbourhood need not extend a prescribed fibre isomorphism. -/
theorem projective_bundle_fiber_iso_spread (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (M N : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (hM : M.IsInvertible) (hN : N.IsInvertible) (s : S)
    (e : Nonempty
      ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj M ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj N)) :
    ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj M ≅
        (tensorPullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj N) := by
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  have hfinite :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} E r
  obtain ⟨q, hq, hqfin⟩ := hfinite.exists_localGeneratorsData
  have : SheafOfModules.IsFiniteType.{u, u, u} E := by
    constructor
    exact ⟨q, hqfin⟩
  have : IsProper p := projectiveBundle_proper p
    ⟨E, inferInstance, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨U, hs, φ, hφ⟩ := projective_bundle_fiber_hom_lift S E r hr M N hM hN s e
  let XU := p ⁻¹ᵁ U
  let f := p ∣_ U
  let sU : U.toScheme := ⟨s, hs⟩
  let c : tensorPullback XU.ι ≅ pullback XU.ι :=
    (tensorPullbackSectionAdjunction XU.ι).leftAdjointUniq
      (pullbackPushforwardAdjunction XU.ι)
  have : M.IsInvertible := hM
  have : N.IsInvertible := hN
  have : ((tensorPullback XU.ι).obj M).IsInvertible :=
    IsInvertible.of_iso (c.app M).symm
  have : ((tensorPullback XU.ι).obj N).IsInvertible :=
    IsInvertible.of_iso (c.app N).symm
  have := IsInvertible.sheafOfModules_isInvertible ((tensorPullback XU.ι).obj M)
  have := IsInvertible.sheafOfModules_isInvertible ((tensorPullback XU.ι).obj N)
  have hfib := range_subset_moduleMapIsoLocus_of_isIso_tensorPullback
    ((tensorPullback XU.ι).obj M) ((tensorPullback XU.ι).obj N) φ (f.fiberι sU) hφ
  -- Properness turns the fibrewise isomorphism locus into a base neighbourhood.
  let O := moduleMapIsoLocus φ
  have hclosed : IsClosed (f '' (O : Set XU.toScheme)ᶜ) :=
    f.isClosedMap _ O.isOpen.isClosed_compl
  let W : U.toScheme.Opens := ⟨(f '' (O : Set XU.toScheme)ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hsW : sU ∈ W := by
    rintro ⟨x, hx, he⟩
    apply hx
    apply hfib
    rw [Scheme.Hom.range_fiberι]
    exact he
  let V := U.ι ''ᵁ W
  have hVU : V ≤ U := U.ι_image_le W
  have hVV : p ⁻¹ᵁ V ≤ XU := p.preimage_mono hVU
  let g := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.homOfLE hVV
  have hg : Set.range g ⊆ (O : Set XU.toScheme) := by
    rintro _ ⟨x, rfl⟩
    have hxW : f (g x) ∈ W := by
      apply (Scheme.Opens.mem_ι_image_iff U).mp
      change U.ι ((p ∣_ U) (g x)) ∈ V
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      simpa only [g, Scheme.homOfLE_apply, Scheme.Opens.ι_apply] using
        (show p x.val ∈ V from x.property)
    by_contra hxO
    exact hxW ⟨g x, hxO, rfl⟩
  -- Pull back the map and identify the iterated restriction with direct restriction.
  have := isIso_tensorPullback_of_range_subset_moduleMapIsoLocus φ g hg
  let v := asIso ((tensorPullback g).map φ)
  have hc := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.homOfLE_ι hVV
  let t : tensorPullback (p ⁻¹ᵁ V).ι ≅ tensorPullback XU.ι ⋙ tensorPullback g :=
    eqToIso (congrArg tensorPullback hc.symm) ≪≫ tensorPullbackSectionComp g XU.ι
  exact ⟨V, ⟨sU, hsW, rfl⟩, ⟨t.app M ≪≫ v ≪≫ (t.app N).symm⟩⟩

end AlgebraicGeometry.ProjectiveBundlePicardClassification
