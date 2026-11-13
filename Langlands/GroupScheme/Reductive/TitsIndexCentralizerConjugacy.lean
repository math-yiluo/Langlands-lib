import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Conjugating maximal split tori inside the centralizer of a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {K : Type u} [Field K] {H : GroupScheme (Spec (CommRingCat.of K))}
  {A T₁ T₂ : CommGroupScheme (Spec (CommRingCat.of K))}

/-- Two maximal split tori of a connected reductive group over a field, both
containing the same split torus `a`, are conjugate by a rational point that
centralizes `a`. The conjugation takes place in the dynamic centralizer of a
generic cocharacter of `a`, which represents the centralizer of `a` and is
connected reductive. -/
theorem exists_centralizing_conj_of_isMaximalSplitTorus (hH : IsConnectedReductive H)
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ H)
    {t₁ : T₁.toGrp ⟶ H} {t₂ : T₂.toGrp ⟶ H}
    (h₁ : IsMaximalSplitTorus t₁) (h₂ : IsMaximalSplitTorus t₂)
    (f₁ : A ⟶ T₁) (f₂ : A ⟶ T₂)
    (hf₁ : CommGroupScheme.groupHom f₁ ≫ t₁ = a)
    (hf₂ : CommGroupScheme.groupHom f₂ ≫ t₂ = a) :
    ∃ (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) (φ : T₁ ≅ T₂),
      t₁ ≫ (H.innerIso z).hom = CommGroupScheme.groupHom φ.hom ≫ t₂ ∧
      a ≫ (H.innerIso z).hom = a := by
  have := hH.smooth
  have := hH.isAffineHom
  have := hH.connectedSpace
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨ν, hν⟩ := hA.exists_cocharacter_centralizer_eq a
  let χ := CommGroupScheme.groupHom ν ≫ a
  let j := Dynamic.Affine.centralizerHom χ
  have hj : (torusCentralizer a).IsRepresentedBy j := by
    have h := Dynamic.Affine.isRepresentedBy_centralizerHom χ
    change (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ a)).IsRepresentedBy j at h
    rwa [hν] at h
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
  have hZ : IsConnectedReductive (Dynamic.Affine.centralizerScheme χ) :=
    splitTorusCentralizerReductive K H hH A a hA _ j hj
  have := hZ.smooth
  have := hZ.isAffineHom
  have := hZ.connectedSpace
  obtain ⟨q₁, hq₁, hq₁j⟩ := h₁.lift hj hjc
    (range_le_torusCentralizer_of_factor a t₁ (CommGroupScheme.groupHom f₁) hf₁)
  obtain ⟨q₂, hq₂, hq₂j⟩ := h₂.lift hj hjc
    (range_le_torusCentralizer_of_factor a t₂ (CommGroupScheme.groupHom f₂) hf₂)
  obtain ⟨p, e, hp⟩ := smoothMaximalSplitTorusConjugacy K _ T₁ T₂ q₁ q₂ hq₁ hq₂
  refine ⟨p ≫ j.hom.hom, CommGroupScheme.isoOfGroupIso e, ?_, ?_⟩
  · rw [← hq₁j, ← hq₂j, Category.assoc, comp_innerIso_hom_comp, ← Category.assoc, hp,
      Category.assoc]
    rfl
  · have hmem : p ≫ j.hom.hom ∈ (torusCentralizer a).carrier (Over.mk (𝟙 _)) := by
      rw [← hj.2]
      exact ⟨p, rfl⟩
    exact (mem_torusCentralizer_base_iff a _).1 hmem

end Langlands.GroupScheme
