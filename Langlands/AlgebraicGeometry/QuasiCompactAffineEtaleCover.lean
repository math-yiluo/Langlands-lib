import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # A surjective étale morphism from an affine scheme onto a quasi-compact scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover

/-- The ring of global sections of the disjoint union of the finite affine subcover
`Y.affineCover.finiteSubcover` of a quasi-compact scheme `Y`. -/
def coverRing (Y : Scheme.{u}) [CompactSpace Y] : CommRingCat.{u} :=
  Γ(∐ (Y.affineCover.finiteSubcover).X, ⊤)

/-- For a quasi-compact scheme `Y`, the morphism `Spec (coverRing Y) ⟶ Y` obtained from the
finite affine subcover `𝒰 := Y.affineCover.finiteSubcover`: the inverse of the isomorphism
`∐ 𝒰.X ≅ Spec Γ(∐ 𝒰.X, ⊤)` (the coproduct is affine) followed by `Sigma.desc 𝒰.f`. -/
def specCover (Y : Scheme.{u}) [CompactSpace Y] : Spec (coverRing Y) ⟶ Y :=
  (∐ (Y.affineCover.finiteSubcover).X).isoSpec.inv ≫ Sigma.desc (Y.affineCover.finiteSubcover).f

/-- `specCover Y` is surjective, flat, geometrically reduced, locally of finite type, étale and
smooth. -/
theorem specCover_properties (Y : Scheme.{u}) [CompactSpace Y] :
    Surjective (specCover Y) ∧ Flat (specCover Y) ∧ GeometricallyReduced (specCover Y) ∧
      LocallyOfFiniteType (specCover Y) ∧ Etale (specCover Y) ∧ Smooth (specCover Y) := by
  let 𝒰 : Y.OpenCover := Y.affineCover.finiteSubcover
  let p : Spec Γ(∐ 𝒰.X, ⊤) ⟶ Y := (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f
  have hsurj : Surjective p := inferInstance
  have : Etale (Sigma.desc 𝒰.f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u}) fun _ => inferInstance
  have het : Etale p := inferInstance
  have hsm : Smooth p := inferInstance
  have hfl : Flat p := inferInstance
  have hft : LocallyOfFiniteType p := inferInstance
  exact ⟨hsurj, hfl,
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth p, hft, het, hsm⟩

/-- A quasi-compact scheme `Y` receives a surjective étale morphism from an affine scheme
`Spec R`; such a morphism is also smooth, flat, locally of finite type and geometrically
reduced. -/
theorem exists_spec_cover (Y : Scheme.{u}) [CompactSpace Y] :
    ∃ (R : CommRingCat.{u}) (p : Spec R ⟶ Y),
      Surjective p ∧ Flat p ∧ GeometricallyReduced p ∧ LocallyOfFiniteType p ∧
        Etale p ∧ Smooth p :=
  ⟨coverRing Y, specCover Y, specCover_properties Y⟩

end Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover
