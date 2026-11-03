import Langlands.AlgebraicGeometry.ProjectiveSpace.LinearAction
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts

/-! # Projective maps from homogeneous global coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (n : ℕ) {X : Scheme.{u}}

local notation "𝒜" => projectiveSpaceGrading R n

/-- Evaluation of a homogeneous affine chart into the corresponding localized target ring. -/
def chartRingMap {B : Type u} [CommRing B]
    (f : ProjectiveCoordinateRing R n →+* B) (t : ProjectiveCoordinateRing R n) :
    Away 𝒜 t →+* Localization.Away (f t) :=
  (IsLocalization.map (M := .powers t) (T := .powers (f t)) _ f (by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp (algebraMap (Away 𝒜 t) (Localization.Away t))

/-- Chart evaluation commutes with graded coordinate substitution. -/
theorem chartRingMap_comp {B : Type u} [CommRing B]
    (g : 𝒜 →+*ᵍ 𝒜) (f : ProjectiveCoordinateRing R n →+* B)
    (t : ProjectiveCoordinateRing R n) :
    chartRingMap n (f.comp g.toRingHom) t =
      (chartRingMap n f (g t)).comp (Away.map g t) := by
  ext z
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  change (IsLocalization.map (M := .powers t) (T := .powers (f (g t)))
      (Localization.Away (f (g t))) (f.comp g.toRingHom) (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
        exact le_rfl))
      (HomogeneousLocalization.val (.mk c)) =
    (IsLocalization.map (M := .powers (g t)) (T := .powers (f (g t)))
      (Localization.Away (f (g t))) f (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]))
      (HomogeneousLocalization.val (HomogeneousLocalization.map g (by
        rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]) (.mk c)))
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rfl

/-- A chosen homogeneous chart computes the projective map from global sections. -/
theorem basicOpen_ι_fromOfGlobalSections
    (f : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    {d : ℕ} (hd : 0 < d) (t : ProjectiveCoordinateRing R n) (ht : t ∈ 𝒜 d) :
    (X.basicOpen (f t)).ι ≫ Proj.fromOfGlobalSections 𝒜 f hf =
      Proj.toBasicOpenOfGlobalSections 𝒜 f rfl hd ht ≫ (Proj.basicOpen 𝒜 t).ι := by
  exact (Proj.openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨d, t, hd, ht⟩

/-- Graded coordinate substitution acts on actual projective maps by composition
with their homogeneous global-coordinate homomorphism. -/
theorem fromOfGlobalSections_comp_gradedMap
    (g : 𝒜 →+*ᵍ 𝒜)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (f : ProjectiveCoordinateRing R n →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hfg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤) :
    Proj.fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hfg =
      Proj.fromOfGlobalSections 𝒜 f hf ≫ Proj.map g hg := by
  apply (Proj.openCoverOfMapIrrelevantEqTop 𝒜 (f.comp g.toRingHom) hfg).hom_ext
  rintro ⟨d, t, hd, ht⟩
  change (X.basicOpen ((f.comp g.toRingHom) t)).ι ≫ _ = _
  rw [basicOpen_ι_fromOfGlobalSections n _ _ hd t ht]
  change _ = (X.basicOpen (f (g t))).ι ≫ _
  rw [← Category.assoc, basicOpen_ι_fromOfGlobalSections n f hf hd (g t) (g.2 ht)]
  simp only [Proj.toBasicOpenOfGlobalSections, Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι]
  congr 1
  congr 1
  congr 1
  rw [Proj.awayι_comp_map g hg hd t ht]
  change Spec.map (CommRingCat.ofHom (chartRingMap n (f.comp g.toRingHom) t)) ≫ _ =
    Spec.map (CommRingCat.ofHom (chartRingMap n f (g t))) ≫
      Spec.map (CommRingCat.ofHom (Away.map g t)) ≫ _
  rw [chartRingMap_comp, CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]

end Langlands.AlgebraicGeometry.ProjectiveSpace.GlobalCoordinates
