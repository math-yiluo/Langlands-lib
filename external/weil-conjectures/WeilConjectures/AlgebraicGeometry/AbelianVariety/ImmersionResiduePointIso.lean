/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.ResidueField

/-! Residue-point isomorphisms induced by immersions.

(blueprint: new-immersion-residue-point-iso)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An immersion identifies the residue points, with the actual projection equation.
Source: Stacks Project, Tag 01IO; Mathlib's surjectivity of immersion stalk maps.
(blueprint: new-immersion-residue-point-iso)

Proof: After substituting the image point, lift a residue-field element to the target
stalk and then through the surjective stalk map of the immersion. This proves that the
induced field homomorphism is surjective; every field homomorphism is injective.
Apply Spec to this ring isomorphism. Naturality of the canonical residue-point map
is exactly the required projection equation. -/
theorem immersion_residuePointIso
    {S W : Scheme.{v}} (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s) :
    ∃ r : Spec (W.residueField w) ≅ Spec (S.residueField s),
      W.fromSpecResidueField w ≫ k = r.hom ≫ S.fromSpecResidueField s := by
  classical
  subst s
  have hr : Function.Surjective (k.residueFieldMap w) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective (R := W.presheaf.stalk w) y
    obtain ⟨x, rfl⟩ := k.stalkMap_surjective w z
    exact ⟨IsLocalRing.residue _ x, rfl⟩
  have : IsIso (k.residueFieldMap w) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(k.residueFieldMap w).hom.injective, hr⟩
  exact ⟨asIso (Spec.map (k.residueFieldMap w)),
    (k.SpecMap_residueFieldMap_fromSpecResidueField w).symm⟩

end AlgebraicGeometry.Scheme
