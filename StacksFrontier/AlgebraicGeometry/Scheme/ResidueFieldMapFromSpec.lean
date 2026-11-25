module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The canonical morphism from the spectrum of a residue field is an isomorphism on residue fields

For a scheme `X` and a point `x`, the morphism `Spec κ(x) ⟶ X` induces an isomorphism on the
residue field at the unique point of `Spec κ(x)`.

For a local ring `B`, `AlgebraicGeometry.residueFieldAtClosedPointEquiv` identifies the residue
field of the scheme `Spec B` at its closed point with the residue field of `B`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes whose stalk map at `x` is surjective induces an isomorphism on
residue fields at `x`. -/
private theorem isIso_residueFieldMap_of_surjective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (hf : Function.Surjective (f.stalkMap x)) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨z, hz⟩ := X.residue_surjective x y
    obtain ⟨w, hw⟩ := hf z
    refine ⟨Y.residue (f x) w, ?_⟩
    have heq := congrArg (fun φ => φ w)
      (congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x))
    change (f.residueFieldMap x).hom (Y.residue (f x) w) = X.residue x (f.stalkMap x w) at heq
    rw [hw, hz] at heq
    exact heq
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, hs⟩

/-- A morphism of schemes whose stalk map at `x` is surjective induces an isomorphism on
residue fields at `x`. -/
public theorem isIso_residueFieldMap_of_stalkMap_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hf : Function.Surjective (f.stalkMap x)) : IsIso (f.residueFieldMap x) :=
    isIso_residueFieldMap_of_surjective_stalkMap f x hf

end AlgebraicGeometry
