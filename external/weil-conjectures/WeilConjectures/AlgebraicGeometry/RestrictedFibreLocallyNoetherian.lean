/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Locally noetherian fibres over a finitely presented restriction

Source: Stacks Project, Tag 054U, fibre topology in the proof.
(blueprint: lem-sbc-restricted-fibre-locally-noetherian)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Fibres over the open where a morphism is locally finitely presented are locally noetherian.
Source: Stacks Project, Tag 054U and the finite-type-over-a-field fibre argument.
Proof: the restriction is locally of finite type. Its fibre over the point of U
corresponding to t is locally of finite type over the residue field, so is locally
noetherian. The residue field of U at t is canonically the residue field of T at t.
Pullback associativity therefore identifies the restricted fibre with f.fiber t.
The isomorphism preserves local noetherianity. No assertion is made outside U.
(blueprint: lem-sbc-restricted-fibre-locally-noetherian) -/
theorem isLocallyNoetherian_fibre_of_finite_presentation_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] (t : T) (ht : t ∈ U) :
    IsLocallyNoetherian (f.fiber t) := by
  let tU : U := ⟨t, ht⟩
  let q := pullback.map (f ∣_ U) (U.toScheme.fromSpecResidueField tU) f
    (T.fromSpecResidueField (U.ι tU)) (f ⁻¹ᵁ U).ι
    (Spec.map (U.ι.residueFieldMap tU)) U.ι (by simp)
    (by exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι tU).symm)
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f U).flip tU
  have : IsIso q := hsq.isIso_fst_of_isIso
  have : LocallyOfFiniteType ((f ∣_ U).fiberToSpecResidueField tU) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian
    ((f ∣_ U).fiberToSpecResidueField tU)
  exact isLocallyNoetherian_of_isOpenImmersion (inv q)

end AlgebraicGeometry
