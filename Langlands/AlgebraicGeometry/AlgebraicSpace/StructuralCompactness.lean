import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-! # Absolute and structural quasi-compactness of algebraic spaces

Absolute quasi-compactness requires a surjective etale atlas with quasi-compact
source scheme. Structural quasi-compactness tests every affine scheme over the
base. Structural finite type is local finite type and structural quasi-compactness.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Absolute quasi-compactness: a surjective etale atlas from a quasi-compact scheme. -/
def IsQuasiCompact (X : AlgebraicSpace S) : Prop :=
  ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
    IsEtale a ∧ IsSurjective a ∧ CompactSpace U.left

/-- The structural morphism is quasi-compact, tested by every affine scheme over the base. -/
def QuasiCompactOverBase (X : AlgebraicSpace S) : Prop :=
  ∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S),
    IsQuasiCompact (baseChange g X)

/-- Structural finite type is structural local finite type and quasi-compactness. -/
def FiniteTypeOverBase (X : AlgebraicSpace S) : Prop :=
  LocallyOfFiniteTypeOverBase X ∧ QuasiCompactOverBase X

variable {X Y : AlgebraicSpace S}

/-- A supplied surjective etale atlas with compact source introduces absolute quasi-compactness. -/
theorem IsQuasiCompact.of_atlas {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) (hU : CompactSpace U.left) :
    IsQuasiCompact X :=
  ⟨U, a, ha, hs, hU⟩

/-- Recover an actual surjective etale scheme atlas with compact source. -/
theorem IsQuasiCompact.exists_atlas (hX : IsQuasiCompact X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsEtale a ∧ IsSurjective a ∧ CompactSpace U.left :=
  hX

/-- A quasi-compact scheme gives an absolutely quasi-compact space by its identity atlas. -/
theorem IsQuasiCompact.of_scheme (U : Over S) [CompactSpace U.left] :
    IsQuasiCompact ((schemeToSpace S).obj U) :=
  HasAtlasProperty.of_scheme (P := fun V _ _ => CompactSpace V) U inferInstance

/-- Whole-presheaf isomorphism transport retains the same compact source scheme. -/
theorem IsQuasiCompact.of_iso (hX : IsQuasiCompact X) (e : X.presheaf ≅ Y.presheaf) :
    IsQuasiCompact Y := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX
  exact ⟨U, a ≫ e.hom, ha.comp_iso e, hs.comp_iso e, hU⟩

/-- Absolute quasi-compactness is invariant under a whole-presheaf isomorphism. -/
theorem IsQuasiCompact.iff_of_iso (e : X.presheaf ≅ Y.presheaf) :
    IsQuasiCompact X ↔ IsQuasiCompact Y :=
  ⟨fun hX => hX.of_iso e, fun hY => hY.of_iso e.symm⟩

/-- Specialize structural quasi-compactness to any supplied affine scheme over the base. -/
theorem QuasiCompactOverBase.affine_baseChange (hX : QuasiCompactOverBase X)
    (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S) :
    IsQuasiCompact (baseChange g X) :=
  hX T g

/-- The exact family of affine-base-change assertions introduces structural quasi-compactness. -/
theorem QuasiCompactOverBase.of_affine_tests
    (hX : ∀ (T : Scheme.{u}) [IsAffine T] (g : T ⟶ S),
      IsQuasiCompact (baseChange g X)) :
    QuasiCompactOverBase X :=
  hX

/-- Introduce structural finite type from its two defining conjuncts. -/
theorem FiniteTypeOverBase.of_locallyOfFiniteType_quasiCompact
    (hl : LocallyOfFiniteTypeOverBase X) (hq : QuasiCompactOverBase X) :
    FiniteTypeOverBase X :=
  ⟨hl, hq⟩

/-- Structural finite type implies structural local finite type. -/
theorem FiniteTypeOverBase.locallyOfFiniteType (hX : FiniteTypeOverBase X) :
    LocallyOfFiniteTypeOverBase X :=
  hX.1

/-- Structural finite type implies structural quasi-compactness. -/
theorem FiniteTypeOverBase.quasiCompact (hX : FiniteTypeOverBase X) :
    QuasiCompactOverBase X :=
  hX.2

end Langlands.AlgebraicGeometry.AlgebraicSpace
