/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientFixedLocalizationKernelComparison

/-! # The classical open part of coefficient-sized localization

Source: Stacks Project, proetale.tex, Tags 09AH, 09AF.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- The closed localization unit is surjective, and its kernel is classical if the
open restriction is classical. Only the open restriction is assumed classical here.
The assertion holds for any adjunction between the specified inverse and direct images.
Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open; Tag 09AF,
lemma-jshriek-comparison; Tag 09AK, lemma-compare-constructible, open endpoint of the sequence
(auxiliary; not a blueprint node).

Proof: on the pro-etale site the canonical open-closed sequence is short exact.
For an affine weakly contractible test object V=Spec B, choose finitely many functions
cutting out the complement of the open. The corresponding principal opens together
with Spec of the localization of B along the closed subset form a pro-etale cover.
On the principal opens the sequence is F -> F -> 0; on that localization it is
0 -> F -> F. Thus the closed unit is epic and the kernel is the open extension by
zero of the open restriction. The open extension commutes with comparison: the two
composite left adjoints have naturally identical right adjoints, given sectionwise
by restriction to etale objects over the open. If G is an etale antecedent of j^*F,
the etale extension by zero of G therefore pulls back to the kernel. These arguments
preserve every constant scalar action and transport through the AsSmall site
models. Quasi-compactness supplies the finite list of functions. No bound on A or
its modules is used. For empty U the kernel is zero; for empty Z the closed unit is
the map to zero and the kernel is F. A full-image closed immersion is treated by
its closed direct image, not by an unjustified scheme isomorphism. An arbitrary
adjunction between the same functors differs from the canonical one by a natural
automorphism of the left adjoint. Its unit is the canonical unit followed by the
corresponding invertible direct-image map. Epimorphy is unchanged, and the kernel
is canonically isomorphic, so essential-image membership is unchanged. -/
theorem coefficientFixed_localization_kernel_origin
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z U : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hj : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} U) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
      (Scheme.coefficientProEtaleModelTopology.{u, v} U)).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} j A).obj F))
    (adj : Scheme.coefficientProEtaleFixedModulePullback.{u, v} i A ⊣
      (Scheme.coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
        (ModuleCat.{max v (u + 1)} A) (Scheme.coefficientProEtaleModelTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} Z))
    [HasKernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) (adj.unit.app F)] :
    Epi (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) (adj.unit.app F) ∧
      (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage
        (kernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          (ModuleCat.{max v (u + 1)} A)) (adj.unit.app F)) := by
  let adj₀ := coefficientFixedCanonicalAdj.{u, v} A i
  have : HasKernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) (adj₀.unit.app F) := by
    exact @HasLimitsOfShape.has_limit WalkingParallelPair inferInstance _ inferInstance
      (HasFiniteLimits.out WalkingParallelPair) (parallelPair (adj₀.unit.app F) 0)
  let R : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} Z)
      (ModuleCat.{max v (u + 1)} A) ⥤
      Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
        (ModuleCat.{max v (u + 1)} A) :=
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
      (ModuleCat.{max v (u + 1)} A)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} Z)
  let e := adj₀.leftAdjointUniq adj
  have he : adj₀.unit.app F ≫ R.map (e.hom.app F) =
      adj.unit.app F := adj₀.unit_leftAdjointUniq_hom_app adj F
  have heiso : IsIso (e.hom.app F) := inferInstance
  have hriso : IsIso (R.map (e.hom.app F)) := by
    dsimp [R]
    infer_instance
  have : IsIso (e.hom.app F) := heiso
  have : IsIso (R.map (e.hom.app F)) := hriso
  have hepi := coefficientFixed_closed_unit_epi.{u, v} A i j hU F
  have hk := coefficientFixed_localization_kernel_comparison.{u, v}
    (A := A) i j hU F hj
  refine ⟨?_, ?_⟩
  · rw [← he]
    infer_instance
  · let kiso := kernel.mapIso (f := adj₀.unit.app F) (f' := adj.unit.app F)
      (Iso.refl _) (asIso (R.map (e.hom.app F))) he
    exact hk.ofIso kiso

end AlgebraicGeometry.ProEtale
