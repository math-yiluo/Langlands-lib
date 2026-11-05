import Langlands.GroupScheme.TensorGaloisPoint
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Affine tensor coordinates and canonical coefficient conjugation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.Descent.TensorCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A]

/-- The tensor spectrum presents the pullback of the affine coordinate spectrum. -/
def spectrumIso :
    Spec (CommRingCat.of (K ⊗[k] A)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) (algebraBaseMap k K) :=
  (pullbackSpecIso k K A).symm ≪≫
    pullbackSymmetry (algebraBaseMap k K)
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))

@[reassoc (attr := simp)]
theorem spectrumIso_hom_fst :
    (spectrumIso k K A).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) := by
  simp [spectrumIso]

@[reassoc (attr := simp)]
theorem spectrumIso_hom_snd :
    (spectrumIso k K A).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) := by
  simp [spectrumIso]
  rfl

variable (X : Over (Spec (CommRingCat.of k)))
    (e : (algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of k A)) ≅ X)

/-- A chosen affine coordinate presentation gives actual tensor coordinates after base change. -/
def baseChangeIso :
    Spec (CommRingCat.of (K ⊗[k] A)) ≅ pullback X.hom (algebraBaseMap k K) :=
  spectrumIso k K A ≪≫
    (Over.forget _).mapIso ((Over.pullback (algebraBaseMap k K)).mapIso e)

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst :
    (baseChangeIso k K A X e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) ≫ e.hom.left := by
  simp [baseChangeIso, Over.pullback_map_left]

@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd :
    (baseChangeIso k K A X e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) := by
  simp [baseChangeIso, Over.pullback_map_left]

/-- The corresponding ring equivalence on actual global sections. -/
def sectionsEquiv :
    K ⊗[k] A ≃+* Γ(pullback X.hom (algebraBaseMap k K), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (K ⊗[k] A))).symm ≪≫
    asIso (baseChangeIso k K A X e).inv.appTop).commRingCatIsoToRingEquiv

/-- Canonical semilinear conjugation fixes the original scheme and changes the field factor. -/
def conjugate (σ : K ≃ₐ[k] K) :
    pullback X.hom (algebraBaseMap k K) ⟶ pullback X.hom (algebraBaseMap k K) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ galoisBaseMap k K σ) (by
      rw [Category.assoc, galoisBaseMap_over, pullback.condition])

@[reassoc (attr := simp)]
theorem conjugate_fst (σ : K ≃ₐ[k] K) :
    conjugate k K X σ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem conjugate_snd (σ : K ≃ₐ[k] K) :
    conjugate k K X σ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ galoisBaseMap k K σ :=
  pullback.lift_snd _ _ _

/-- Tensor coefficient conjugation is the actual canonical semilinear scheme map. -/
theorem coefficientConjugate_baseChangeIso (σ : K ≃ₐ[k] K) :
    Spec.map (CommRingCat.ofHom
        (TensorGaloisPoint.coefficientConjugate k K A σ).toRingHom) ≫
        (baseChangeIso k K A X e).hom =
      (baseChangeIso k K A X e).hom ≫ conjugate k K X σ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeIso_hom_fst, conjugate_fst,
      ← Spec.map_comp_assoc]
    congr 2
    ext a
    simp [Algebra.TensorProduct.includeRight_apply]
  · simp only [Category.assoc, baseChangeIso_hom_snd, conjugate_snd,
      baseChangeIso_hom_snd_assoc, ← Spec.map_comp, galoisBaseMap]
    apply congrArg Spec.map
    ext c
    simp [Algebra.TensorProduct.algebraMap_apply]

end Langlands.GroupScheme.Descent.TensorCoordinates
