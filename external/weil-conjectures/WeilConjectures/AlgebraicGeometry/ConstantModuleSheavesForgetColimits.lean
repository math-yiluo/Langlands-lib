/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Forgetting constant module coefficients preserves colimits

Source: Stacks Project, Tags 03DB and 03CO.
(blueprint: lem-weil-pbc-constant-module-sheaves-forget-colimits).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Forgetting constant module coefficients preserves colimits of the size of the
coefficient category, on any small etale site.
Source: Stacks Project, Tag 03DB, proof of lemma-limits-colimits; Tag 03CO,
lemma-limits-colimits-abelian-sheaves.
(blueprint: lem-weil-pbc-constant-module-sheaves-forget-colimits)

Proof: For a diagram of module sheaves, take its sectionwise colimit in module
presheaves and then sheafify. On each object, forgetting a module colimit gives
its abelian-group colimit: the group colimit has the unique scalar action for
which every coprojection is linear, and its universal map to any module is
linear by uniqueness on the coprojections. Sheafification commutes with forgetting
this action. Indeed local module sections and their matching equalities give
exactly the local sections and matching equalities of the underlying abelian
presheaf, and scalar multiplication extends uniquely through sheafification.
Thus forgetting the sheafified module colimit gives the sheafification of the
abelian presheaf colimit. The latter is the abelian-sheaf colimit by Tag 03CO.
All comparisons commute with the original coprojections, proving preservation
of the canonical cocone, and not just an isomorphism of objects.
For the formal proof, restriction of scalars along ℤ → Λ is left adjoint to
coextension. Its composite with the equivalence from ℤ-modules to abelian groups
is definitionally the coefficient forgetful functor, so it too is a left adjoint.
The induced compose-and-sheafify functor is therefore a left adjoint. Since
forgetting preserves sheaves, the sheafification natural isomorphism identifies
this functor with sheafCompose. Transport the adjunction across that isomorphism
and apply preservation of colimits by left adjoints. No compactness or finiteness
hypothesis is used. For an empty diagram the construction gives
the zero sheaf; for an identity diagram it gives the original sheaf. -/
theorem constantModuleSheaves_forget_preservesColimits (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  let f : ℤ →+* Λ := Int.castRingHom Λ
  let U := ModuleCat.restrictScalars.{u + 1} f
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : (U ⋙ V).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let J := X.smallEtaleTopology
  let G := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  infer_instance

end AlgebraicGeometry.Etale
