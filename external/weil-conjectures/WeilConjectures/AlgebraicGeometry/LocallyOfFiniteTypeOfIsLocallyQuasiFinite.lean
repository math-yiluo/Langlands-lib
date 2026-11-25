/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Locally quasi-finite morphisms are locally of finite type

Source: Stacks Project, Morphisms of Schemes, remark after Definition Tag 01TD,
and Lemma Tag 01T2 (blueprint: lem-weil-pbc-lqf-locally-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally quasi-finite morphism in the Stacks sense is locally of finite type.
Source: Stacks Project, remark after Definition Tag 01TD and Lemma Tag 01T2
(blueprint: lem-weil-pbc-lqf-locally-finite-type).

Proof: For each point `x`, unpack `IsLocallyQuasiFinite` and `IsQuasiFiniteAtPoint`
(pqf-def-quasifinite) to obtain affine opens `U` containing `x` and `V` with
`U ≤ f ⁻¹ᵁ V`. The induced map on sections is of finite type
(def-weil-pbc-finite-type-algebra). Discard its quasi-finiteness-at-the-prime clause.
Apply the pointwise criterion for locally finite type
(lem-weil-pbc-lft-pointwise-criterion, Stacks Tags 01T1 and 01T2) to these affine
pairs, obtaining `LocallyOfFiniteType f` (def-weil-finite-type-morphism). -/
theorem locallyOfFiniteType_of_isLocallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : f.IsLocallyQuasiFinite) : LocallyOfFiniteType f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
    (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).left]
  intro x
  obtain ⟨U, hx, hU, V, hV, e, hft, _⟩ := hf x
  exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, hft⟩

end AlgebraicGeometry.Scheme.Hom
