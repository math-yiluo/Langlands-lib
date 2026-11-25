/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel

/-! The open extension-by-zero comparison for the coefficient-sized closed-unit kernel. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- The kernel of the canonical closed unit is classical when the open restriction is.
Source: Stacks Project, Tag 09AH, lemma-ses-associated-to-open, and Tag 09AF,
lemma-jshriek-comparison (auxiliary; not a blueprint node).

Proof: the open-closed localization sequence identifies the kernel of the closed unit
with extension by zero of the restriction to the complementary open. To obtain this
identification, on affine weakly contractible test objects use the principal-open and
closed-localization cover from Tag 09AH: the sequence is respectively F → F → 0 and
0 → F → F. These local identifications preserve the arbitrary A-action, and glue by
the kernel universal property. Choose an etale antecedent G of the open restriction.
The etale extension by zero of G is an antecedent of this kernel: comparison commutes
with open extension by zero by Tag 09AF, since the two composite left adjoints have
identical right adjoints given by restriction to etale objects over the open. Transport
these functors and their adjunctions through the coefficient-sized AsSmall equivalences.
For an empty open the kernel is zero; for an empty closed subscheme the open is all of X
and the hypothesis itself supplies an antecedent. -/
theorem coefficientFixed_localization_kernel_comparison
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
    [HasKernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)) ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)] :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage
        (kernel (C := Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          (ModuleCat.{max v (u + 1)} A))
          ((coefficientFixedCanonicalAdj.{u, v} A i).unit.app F)) := by
  obtain ⟨G, ⟨e⟩⟩ := hj
  obtain ⟨k⟩ := coefficientOpenClosedKernelIso.{u, v} A i j hU F
  refine ⟨(coefficientOpenEtaleExtension.{u, v} A j).obj G, ⟨?_⟩⟩
  exact (coefficientOpenExtensionComparisonIso.{u, v} A j).app G ≪≫
    (coefficientOpenProEtaleExtension.{u, v} A j).mapIso e ≪≫ k

end AlgebraicGeometry.ProEtale
