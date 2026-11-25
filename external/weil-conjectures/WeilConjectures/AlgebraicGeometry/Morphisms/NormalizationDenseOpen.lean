/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Normalization

import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalDenseOpenIntegralSection

/-!
# Relative normalization in a dense open of a normal scheme

## References

* Stacks Project, Tags 0357 (normal components), 035I (relative normalization), and 0AB1 (integral
  birational maps to normal schemes)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A locally Noetherian normal scheme is its own relative normalization in a dense open. -/
theorem isIso_fromNormalization_denseOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hnormal : ∀ z : X, IsDomain (X.presheaf.stalk z) ∧
      IsIntegrallyClosed (X.presheaf.stalk z))
    (V : X.Opens) (hV : Dense (V : Set X)) :
    IsIso V.ι.fromNormalization := by
  have (z : X) : IsDomain (X.presheaf.stalk z) := (hnormal z).1
  have (z : X) : _root_.IsReduced (X.presheaf.stalk z) := inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsDominant V.ι := by
    rw [isDominant_iff, DenseRange, Opens.range_ι]
    exact hV
  have := IsSchemeTheoreticallyDominant.of_isDominant V.ι
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme)
      (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)]
  intro U
  change IsIso (V.ι.fromNormalization ∣_ U.1)
  refine (isIso_morphismRestrict_iff_isIso_app V.ι.fromNormalization U.2).mpr ?_
  let := (V.ι.app U.1).hom.toAlgebra
  rw [Hom.fromNormalization_app V.ι U.2]
  have hbij : Function.Bijective
      (algebraMap Γ(X, U.1) (integralClosure Γ(X, U.1) Γ(V, V.ι ⁻¹ᵁ U.1))) := by
    refine ⟨fun a b hab ↦ V.ι.app_injective U.1 (congrArg Subtype.val hab), ?_⟩
    intro s
    obtain ⟨t, ht⟩ := exists_integral_section_denseOpen hnormal V hV U.1 U.2 s.1 s.2
    exact ⟨t, Subtype.ext ht⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(X, U.1)
      (integralClosure Γ(X, U.1) Γ(V, V.ι ⁻¹ᵁ U.1)))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  infer_instance

end AlgebraicGeometry.Scheme
