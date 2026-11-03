import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Dynamic.Uniqueness

/-! # Scheme-theoretic dominance in the split-torus image factorization -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

open SplitTorusImage Corepresented Diagonalizable in
/-- Over a field `k`, every homomorphism `φ : D ⟶ H` from a split torus to an affine group
scheme factors as `π ≫ i = φ` through a split subtorus `i : D' ⟶ H`, i.e. a closed immersion of
a split torus; if `φ` is central, so is `i`. -/
theorem IsSplitTorus.exists_dominant_factor_isSplitSubtorus {k : Type u} [Field k]
    {D : CommGroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] (φ : D.toGrp ⟶ H) :
    ∃ (D' : CommGroupScheme (Spec (CommRingCat.of k))) (π : D.toGrp ⟶ D'.toGrp)
      (i : D'.toGrp ⟶ H), IsSplitSubtorus i ∧ π ≫ i = φ ∧
        IsSchemeTheoreticallyDominant π.hom.hom.left ∧ (IsCentral φ → IsCentral i) := by
  classical
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  let : Fintype I := Fintype.ofFinite I
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let G₀ := Corepresented.groupScheme (functor (CommRingCat.of k) (I → ℤ))
    (grpCorepresentation (CommRingCat.of k) (I → ℤ))
  let cH := AffineCoordinates.corepresentation H
  let Hc := Corepresented.groupScheme (AffineCoordinates.functor H) cH
  let eT : G₀ ≅ splitTorus (Spec (CommRingCat.of k)) I :=
    splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))
  let eH : Hc ≅ H := AffineCoordinates.groupSchemeIso H
  let φ₀ : G₀ ⟶ Hc := ((eT.hom ≫ eD.inv) ≫ φ) ≫ eH.symm.hom
  let β := pointsTrans (grpCorepresentation (CommRingCat.of k) (I → ℤ)) cH φ₀
  obtain ⟨n, v⟩ := Submodule.basisOfPid (Pi.basisFun ℤ I) (lattice cH β)
  let b : lattice cH β ≃+ (ULift.{u} (Fin n) → ℤ) :=
    (v.equivFun.trans (LinearEquiv.funCongrLeft ℤ ℤ Equiv.ulift)).toAddEquiv
  let Glat := Corepresented.groupScheme (functor (CommRingCat.of k) (lattice cH β))
    (grpCorepresentation (CommRingCat.of k) (lattice cH β))
  let p : G₀ ⟶ Glat := groupSchemeMap (grpCorepresentation (CommRingCat.of k) (I → ℤ))
    (grpCorepresentation (CommRingCat.of k) (lattice cH β))
    (restrict (CommRingCat.of k) (lattice cH β).subtype.toAddMonoidHom)
  let q : Glat ⟶ Hc :=
    groupSchemeMap (grpCorepresentation (CommRingCat.of k) (lattice cH β)) cH (imageTrans cH β)
  have hcomp : p ≫ q = φ₀ := by
    change groupSchemeMap _ _ _ ≫ groupSchemeMap _ _ _ = φ₀
    rw [groupSchemeMap_comp, restrict_imageTrans, groupSchemeMap_pointsTrans]
  refine ⟨groupScheme (CommRingCat.of k) (lattice cH β), (eD.hom ≫ eT.inv ≫ p : D.toGrp ⟶ Glat),
    (q ≫ eH.hom : Glat ⟶ H), ⟨isSplitTorus (CommRingCat.of k) b, ?_⟩, ?_, ?_, ?_⟩
  · have := isClosedImmersion_imageTrans cH β
    have : IsIso eH.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso eH)).hom)
    change IsClosedImmersion (q.hom.hom.left ≫ eH.hom.hom.hom.left)
    infer_instance
  · change (eD.hom ≫ eT.inv ≫ p) ≫ q ≫ eH.hom = φ
    rw [Category.assoc, Category.assoc, ← Category.assoc p, hcomp]
    simp only [φ₀, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.comp_id]
  · have hp : IsSchemeTheoreticallyDominant p.hom.hom.left := by
      change IsSchemeTheoreticallyDominant (groupSchemeMap _ _ _).hom.hom.left
      rw [groupSchemeMap_hom_left]
      have hclass : Corepresented.classify
          (grpCorepresentation (CommRingCat.of k) (I → ℤ))
          (grpCorepresentation (CommRingCat.of k) (lattice cH β))
          (restrict (CommRingCat.of k) (lattice cH β).subtype.toAddMonoidHom) =
          latticeIncl cH β := by
        unfold Corepresented.classify
        rw [restrict_homEquiv, Category.comp_id, Equiv.symm_apply_apply]
      rw [hclass]
      exact isSchemeTheoreticallyDominant_specMap (latticeIncl_injective cH β)
    have : IsSchemeTheoreticallyDominant p.hom.hom.left := hp
    have : IsIso eD.hom.hom.hom.left :=
      (Over.forget _).map_isIso eD.hom.hom.hom
    have : IsIso eT.inv.hom.hom.left :=
      (Over.forget _).map_isIso eT.inv.hom.hom
    change IsSchemeTheoreticallyDominant
      (eD.hom.hom.hom.left ≫ eT.inv.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  · intro hφ
    have hφ₀ : IsCentral φ₀ := (hφ.comp (eT.hom ≫ eD.inv)).comp_iso eH.symm
    exact (isCentral_groupSchemeMap _ cH _ (commute_imageTrans cH β
      (Corepresented.IsCentral.commute_pointsTrans _ cH hφ₀))).comp_iso eH


namespace SplitTorusImage

/-- An actual closed split-torus image with its dominant factor map retained. -/
structure DominantFactorization {k : Type u} [Field k]
    {D : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))} (φ : D.toGrp ⟶ H) where
  image : CommGroupScheme (Spec (CommRingCat.of k))
  factor : D.toGrp ⟶ image.toGrp
  inclusion : image.toGrp ⟶ H
  isSplitSubtorus : IsSplitSubtorus inclusion
  factor_comp : factor ≫ inclusion = φ
  dominant : IsSchemeTheoreticallyDominant factor.hom.hom.left
  central : IsCentral φ → IsCentral inclusion

end SplitTorusImage

/-- Choose the image factorization without discarding schematic dominance. -/
def IsSplitTorus.dominantFactorization {k : Type u} [Field k]
    {D : CommGroupScheme (Spec (CommRingCat.of k))} (hD : IsSplitTorus D.toGrp)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (φ : D.toGrp ⟶ H) : SplitTorusImage.DominantFactorization φ :=
  Classical.choice (by
    obtain ⟨D', π, i, hi, hπ, hd, hc⟩ := hD.exists_dominant_factor_isSplitSubtorus φ
    exact ⟨⟨D', π, i, hi, hπ, hd, hc⟩⟩)

end Langlands.GroupScheme
