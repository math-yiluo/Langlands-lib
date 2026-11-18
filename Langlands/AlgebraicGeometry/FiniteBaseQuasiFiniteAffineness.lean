import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen
import Langlands.AlgebraicGeometry.SmoothDvrFibreGenericPoints
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Affineness of quasi-finite schemes over a finite affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A quasi-affine scheme with finitely many points is affine. -/
theorem isAffine_of_finite_of_quasiAffine (X : Scheme.{u})
    [Finite X] [X.IsQuasiAffine] : IsAffine X := by
  obtain ⟨s, hs, ha⟩ :=
    OrbitSaturatedAffineOpen.exists_basicOpen_isAffineOpen_of_finite X
      (Set.toFinite (Set.univ : Set X))
  have htop : X.basicOpen s = ⊤ := by
    apply le_antisymm le_top
    exact hs
  have : IsAffine (⊤ : X.Opens).toScheme := htop ▸ ha
  exact IsAffine.of_isIso X.topIso.inv

/-- A quasi-compact separated locally quasi-finite morphism to an affine
scheme with finitely many points has affine source. -/
theorem isAffine_of_quasiFinite_of_finite_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Finite Y]
    [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] : IsAffine X := by
  have hfinite : (Set.univ : Set X).Finite := by
    simpa using f.finite_preimage (Set.toFinite (Set.univ : Set Y))
  let : Finite X := Finite.of_finite_univ hfinite
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  let : X.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion f.toNormalization
  exact isAffine_of_finite_of_quasiAffine X

/-- The same hypotheses give relative affineness over the finite affine base. -/
theorem isAffineHom_of_quasiFinite_of_finite_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Finite Y]
    [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] : IsAffineHom f := by
  let : IsAffine X := isAffine_of_quasiFinite_of_finite_base f
  infer_instance

/-- An actual affine coordinate presentation of a quasi-finite scheme over
an affine base with finitely many points. -/
def finiteBaseQuasiFiniteAffineIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Finite Y]
    [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] : X ≅ Spec Γ(X, ⊤) := by
  let : IsAffine X := isAffine_of_quasiFinite_of_finite_base f
  exact X.isoSpec

/-- Every quasi-compact separated locally quasi-finite morphism over a DVR
is affine, without any affineness assumption on its source. -/
theorem isAffineHom_quasiFinite_over_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] : IsAffineHom f := by
  let : Finite (Spec (CommRingCat.of R)) := SmoothDvrFibreGenericPoints.finite_base R
  exact isAffineHom_of_quasiFinite_of_finite_base f

/-- In particular, a quasi-compact separated etale scheme over a DVR is affine. -/
theorem isAffineHom_etale_over_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [IsSeparated f] [Etale f] : IsAffineHom f := by
  let : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  exact isAffineHom_quasiFinite_over_dvr R f

end Langlands.AlgebraicGeometry
