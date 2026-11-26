import Langlands.AlgebraicGeometry.TwistedOpenGluingBaseChange
import Langlands.AlgebraicGeometry.SurjectiveClosedBaseChangeProper
import Langlands.AlgebraicGeometry.SmoothThickeningLiftingProof

/-! # Smooth proper lifts from twisted gluing data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.TwistedOpenGluing.Data

variable {C S T Y : Scheme.{u}} {D : Data C} {π : C ⟶ S} (hπ : D.IsOver π)
  (t : T ⟶ S) [IsClosedImmersion t] (q : Y ⟶ T)
  (κ' : ∀ i, ((D.baseChange hπ t).V i).toScheme ⟶ Y) [∀ i, IsOpenImmersion (κ' i)]
  (hcov : ⨆ i, (κ' i).opensRange = ⊤)
  (hpre : ∀ i j, (κ' j) ⁻¹ᵁ (κ' i).opensRange ≤
    ((D.baseChange hπ t).V j).ι ⁻¹ᵁ (D.baseChange hπ t).V i)
  (hκ : ∀ i j, (pullback π t).homOfLE
      (inf_le_right : (D.baseChange hπ t).V i ⊓ (D.baseChange hπ t).V j ≤ _) ≫ κ' j =
    restrictTo ((D.baseChange hπ t).θ i j) ((D.baseChange hπ t).pointwise i j) le_rfl
      inf_le_left ≫ κ' i)
  (hq : ∀ i, κ' i ≫ q = ((D.baseChange hπ t).V i).ι ≫ pullback.snd π t)

/-- A scheme over `T` covered compatibly by the pulled-back pieces is the base change of the
glued scheme. -/
def liftIso : Y ≅ pullback (D.toBase hπ) t :=
  ((D.baseChange hπ t).recognize κ' hcov hpre hκ).symm ≪≫ D.baseChangeIso hπ t

include hq in
theorem liftIso_hom_snd :
    (liftIso hπ t κ' hcov hpre hκ).hom ≫ pullback.snd (D.toBase hπ) t = q := by
  rw [liftIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_comp_eq]
  refine (D.baseChange hπ t).hom_ext fun i ↦ ?_
  have h₁ := ι_recognize_hom_assoc (D.baseChange hπ t) κ' hcov hpre hκ i q
  have h₂ := ι_baseChangeIso_hom_assoc hπ t (i : D.J) (pullback.snd (D.toBase hπ) t)
  have h₃ := κ_snd hπ t (i : D.J)
  rw [h₁, hq, h₂]
  exact h₃

include hcov hpre hκ hq in
theorem isProper_toBase [Surjective t] [IsProper q] [LocallyOfFiniteType π] :
    IsProper (D.toBase hπ) := by
  have : LocallyOfFiniteType (D.toBase hπ) := D.locallyOfFiniteType_toBase hπ
  have h : pullback.snd (D.toBase hπ) t = (liftIso hπ t κ' hcov hpre hκ).inv ≫ q := by
    rw [Iso.eq_inv_comp, liftIso_hom_snd hπ t q κ' hcov hpre hκ hq]
  have : IsProper (pullback.snd (D.toBase hπ) t) := by
    rw [h]
    infer_instance
  exact SurjectiveClosedBaseChange.isProper (D.toBase hπ) t

end Langlands.AlgebraicGeometry.TwistedOpenGluing.Data

namespace Langlands.AlgebraicGeometry

/-- A section over the thinner affine base lifts to a section of a smooth scheme over the
thicker affine base. -/
theorem exists_section_lift {R' R : CommRingCat.{u}} (φ : R' ⟶ R) (hφ : Function.Surjective φ.hom)
    (hnil : IsNilpotent (RingHom.ker φ.hom)) {X : Scheme.{u}} (p : X ⟶ Spec R') [Smooth p]
    (σ : Spec R ⟶ pullback p (Spec.map φ)) (hσ : σ ≫ pullback.snd p (Spec.map φ) = 𝟙 _) :
    ∃ s : Spec R' ⟶ X, s ≫ p = 𝟙 _ ∧ Spec.map φ ≫ s = σ ≫ pullback.fst p (Spec.map φ) := by
  obtain ⟨s, hs₁, hs₂⟩ := smoothThickeningLifting p φ hφ hnil (σ ≫ pullback.fst p (Spec.map φ))
    (𝟙 _) (by rw [Category.assoc, pullback.condition, reassoc_of% hσ, Category.comp_id])
  exact ⟨s, hs₂, hs₁⟩

end Langlands.AlgebraicGeometry
