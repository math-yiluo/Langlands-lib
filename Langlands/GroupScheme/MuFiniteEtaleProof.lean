import Langlands.GroupScheme.MuFiniteEtaleStatement
import Langlands.GroupScheme.MuAffinePresentationProof
import Langlands.GroupScheme.MuCoordinateAlgebraProof

/-! # Descent assembly for finite étaleness of the actual roots of unity -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Finite étaleness on affine spectra implies the unchanged global target. -/
theorem muFiniteEtale_of_spec
    (hSpec : ∀ (A : CommRingCat.{u}) (n : ℕ), 0 < n → IsUnit (n : A) →
      IsFinite (mu (Spec A) n).X.hom ∧ Etale (mu (Spec A) n).X.hom) :
    MuFiniteEtaleStatement.{u} := by
  intro S n hn hu
  have hLocal (i : S.affineOpenCover.I₀) :
      IsFinite (S.affineOpenCover.openCover.pullbackHom (mu S n).X.hom i) ∧
      Etale (S.affineOpenCover.openCover.pullbackHom (mu S n).X.hom i) := by
    have huSpec : IsUnit (n : Γ(Spec (S.affineOpenCover.X i), ⊤)) := by
      simpa only [map_natCast] using hu.map (S.affineOpenCover.f i).appTop.hom
    have huA : IsUnit (n : S.affineOpenCover.X i) := by
      simpa only [map_natCast] using
        huSpec.map (Scheme.ΓSpecIso (S.affineOpenCover.X i)).hom.hom
    obtain ⟨hf, he⟩ := hSpec (S.affineOpenCover.X i) n hn huA
    let e :
        (Over.pullback (S.affineOpenCover.f i)).obj (mu S n).X ≅
          (mu (Spec (S.affineOpenCover.X i)) n).X :=
      (Grp.forget _).mapIso (mu.baseChangeIso (S.affineOpenCover.f i) n)
    exact ⟨(MorphismProperty.over_iso_iff (@IsFinite) e).mpr hf,
      (MorphismProperty.over_iso_iff (@Etale) e).mpr he⟩
  exact ⟨
    (IsZariskiLocalAtTarget.iff_of_openCover
      (P := @IsFinite) S.affineOpenCover.openCover).mpr (fun i => (hLocal i).1),
    (IsZariskiLocalAtTarget.iff_of_openCover
      (P := @Etale) S.affineOpenCover.openCover).mpr (fun i => (hLocal i).2)⟩

/-- The affine presentation and coordinate algebra calculation suffice for the target. -/
theorem muFiniteEtale_of_affineData
    (hPresentation : MuAffinePresentationStatement.{u})
    (hAlgebra : MuCoordinateAlgebraStatement.{u}) :
    MuFiniteEtaleStatement.{u} := by
  apply muFiniteEtale_of_spec
  intro A n hn hu
  obtain ⟨e⟩ := hPresentation A n hn
  obtain ⟨hf, he⟩ := hAlgebra A n hn hu
  constructor
  · apply (MorphismProperty.over_iso_iff (@IsFinite) e).mpr
    change IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1)))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hf
  · apply (MorphismProperty.over_iso_iff (@Etale) e).mpr
    change Etale (Spec.map (CommRingCat.ofHom
      (algebraMap A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1)))))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he

/-- The actual roots-of-unity group scheme is finite étale when its positive
index is invertible in the base's global sections. -/
theorem muFiniteEtale : MuFiniteEtaleStatement.{u} :=
  muFiniteEtale_of_affineData muAffinePresentation muCoordinateAlgebra

end Langlands.GroupScheme
