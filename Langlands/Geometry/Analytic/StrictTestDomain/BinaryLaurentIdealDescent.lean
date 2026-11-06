import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentIdealDescent
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentDiagramComparisonProof
import Langlands.Geometry.Analytic.StrictTestDomain.QuotientTests

/-! # Closed-ideal effectiveness for the actual strict binary Laurent cover -/

noncomputable section

universe u v w x y v' w' x' y'

namespace Langlands.Analytic

namespace BoundedAlgHom.SplitSquare

variable {K : Type u} [NormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  {A₁ : Type w} [NormedCommRing A₁] [NormedAlgebra K A₁]
  {A₂ : Type x} [NormedCommRing A₂] [NormedAlgebra K A₂]
  {A₁₂ : Type y} [NormedCommRing A₁₂] [NormedAlgebra K A₁₂]
  {B : Type v'} [NormedCommRing B] [NormedAlgebra K B]
  {B₁ : Type w'} [NormedCommRing B₁] [NormedAlgebra K B₁]
  {B₂ : Type x'} [NormedCommRing B₂] [NormedAlgebra K B₂]
  {B₁₂ : Type y'} [NormedCommRing B₁₂] [NormedAlgebra K B₁₂]
  {p₁ : BoundedAlgHom K A A₁} {p₂ : BoundedAlgHom K A A₂}
  {r₁ : BoundedAlgHom K A₁ A₁₂} {r₂ : BoundedAlgHom K A₂ A₁₂}

/-- Transport a split square along bounded algebra equivalences of its four
corners commuting with the four maps. The new splitting constant is the old one
multiplied by the forward bound of the overlap equivalence and the larger of
the two inverse bounds of the side equivalences. -/
def congr (S : SplitSquare p₁ p₂ r₁ r₂)
    (q₁ : BoundedAlgHom K B B₁) (q₂ : BoundedAlgHom K B B₂)
    (s₁ : BoundedAlgHom K B₁ B₁₂) (s₂ : BoundedAlgHom K B₂ B₁₂)
    (e : BoundedAlgEquiv K B A) (e₁ : BoundedAlgEquiv K B₁ A₁)
    (e₂ : BoundedAlgEquiv K B₂ A₂) (e₁₂ : BoundedAlgEquiv K B₁₂ A₁₂)
    (hq₁ : ∀ b, e₁ (q₁ b) = p₁ (e b)) (hq₂ : ∀ b, e₂ (q₂ b) = p₂ (e b))
    (hs₁ : ∀ b, e₁₂ (s₁ b) = r₁ (e₁ b)) (hs₂ : ∀ b, e₁₂ (s₂ b) = r₂ (e₂ b)) :
    SplitSquare q₁ q₂ s₁ s₂ where
  comm b := e₁₂.toAlgEquiv.injective (by
    rw [hs₁, hs₂, hq₁, hq₂, S.comm])
  glue b₁ b₂ h := by
    obtain ⟨a, ha₁, ha₂⟩ := S.glue (e₁ b₁) (e₂ b₂) (by rw [← hs₁, ← hs₂, h])
    refine ⟨e.symm a, e₁.toAlgEquiv.injective ?_, e₂.toAlgEquiv.injective ?_⟩
    · rw [hq₁, e.apply_symm_apply, ha₁]
    · rw [hq₂, e.apply_symm_apply, ha₂]
  dense := by
    have hfun : (s₂ : B₂ → B₁₂) = e₁₂.symm ∘ (r₂ ∘ e₂) := by
      funext b
      simp only [Function.comp_apply]
      rw [← hs₂, e₁₂.symm_apply_apply]
    rw [hfun]
    exact e₁₂.symm.toAlgEquiv.surjective.denseRange.comp
      (S.dense.comp e₂.toAlgEquiv.surjective.denseRange r₂.continuous)
      e₁₂.symm.toBoundedAlgHom.continuous
  bound := max e₁.inverse_bounded.choose e₂.inverse_bounded.choose * S.bound *
    e₁₂.bounded.choose
  bound_nonneg := mul_nonneg (mul_nonneg
    ((e₁.inverse_bounded.choose_spec.1.le).trans (le_max_left _ _)) S.bound_nonneg)
    e₁₂.bounded.choose_spec.1.le
  split h := by
    obtain ⟨a₁, a₂, ha, h₁, h₂⟩ := S.split (e₁₂ h)
    have hβ := S.bound_nonneg
    have hC := e₁₂.bounded.choose_spec.1.le
    have hh : ‖e₁₂ h‖ ≤ e₁₂.bounded.choose * ‖h‖ := e₁₂.bounded.choose_spec.2 h
    have side {C C' c z : ℝ} (hC₀ : 0 < C) (hCC' : C ≤ C') (hz : z ≤ C * c)
        (hc : c ≤ S.bound * ‖e₁₂ h‖) : z ≤ C' * S.bound * e₁₂.bounded.choose * ‖h‖ :=
      calc z ≤ C * c := hz
        _ ≤ C * (S.bound * (e₁₂.bounded.choose * ‖h‖)) :=
          mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hh hβ)) hC₀.le
        _ = C * S.bound * e₁₂.bounded.choose * ‖h‖ := by ring
        _ ≤ C' * S.bound * e₁₂.bounded.choose * ‖h‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCC' hβ) hC) (norm_nonneg h)
    refine ⟨e₁.symm a₁, e₂.symm a₂, e₁₂.toAlgEquiv.injective ?_, ?_, ?_⟩
    · rw [map_add, hs₁, hs₂, e₁.apply_symm_apply, e₂.apply_symm_apply, ha]
    · exact side e₁.inverse_bounded.choose_spec.1 (le_max_left _ _)
        (e₁.inverse_bounded.choose_spec.2 a₁) h₁
    · exact side e₂.inverse_bounded.choose_spec.1 (le_max_right _ _)
        (e₂.inverse_bounded.choose_spec.2 a₂) h₂

end BoundedAlgHom.SplitSquare

namespace StrictTestDomain.RationalData

open PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Over a nontrivially normed field, the actual strict binary Laurent square,
with the two actual intersection restrictions, is split. -/
theorem nonempty_laurentSplitSquare (hK : ∃ c : K, 1 < ‖c‖) (f : P) :
    Nonempty (BoundedAlgHom.SplitSquare (laurentUpper f).baseMap (laurentLower f).baseMap
      (interLeft (laurentUpper f) (laurentLower f)).restriction
      (interRight (laurentUpper f) (laurentLower f)).restriction) := by
  obtain ⟨eU, eL, eO, hU, hL, -, hl, hr⟩ := binaryLaurentDiagramComparison K P f
  exact ⟨(BinaryLaurent.splitSquareOfStrict K hK P _).congr _ _ _ _
    (strictEquiv K P).symm eU eL eO hU hL hl hr⟩

/-- A chosen split-square structure on the actual strict binary Laurent square. -/
def laurentSplitSquare (hK : ∃ c : K, 1 < ‖c‖) (f : P) :
    BoundedAlgHom.SplitSquare (laurentUpper f).baseMap (laurentLower f).baseMap
      (interLeft (laurentUpper f) (laurentLower f)).restriction
      (interRight (laurentUpper f) (laurentLower f)).restriction :=
  Classical.choice (nonempty_laurentSplitSquare hK f)

/-- Closed-ideal effectiveness for the actual strict binary Laurent cover: ideals
of the upper and lower Laurent algebras with equal closed extensions to the
actual intersection algebra are the closed extensions of the ideal of base
elements lying in both of them. -/
theorem laurent_closedIdealMap_inf_comap_eq (hK : ∃ c : K, 1 < ‖c‖) (f : P)
    (I₁ : Ideal (laurentUpper f).algebra) (I₂ : Ideal (laurentLower f).algebra)
    (hI : (interLeft (laurentUpper f) (laurentLower f)).restriction.closedIdealMap I₁ =
      (interRight (laurentUpper f) (laurentLower f)).restriction.closedIdealMap I₂) :
    (laurentUpper f).baseMap.closedIdealMap
        (I₁.comap (laurentUpper f).baseMap.toAlgHom.toRingHom ⊓
          I₂.comap (laurentLower f).baseMap.toAlgHom.toRingHom) = I₁ ∧
      (laurentLower f).baseMap.closedIdealMap
        (I₁.comap (laurentUpper f).baseMap.toAlgHom.toRingHom ⊓
          I₂.comap (laurentLower f).baseMap.toAlgHom.toRingHom) = I₂ :=
  (laurentSplitSquare hK f).closedIdealMap_inf_comap_eq
    (PresentedStrictAffinoidAlgebra.isClosed_ideal hK _)
    (PresentedStrictAffinoidAlgebra.isClosed_ideal hK _)
    (PresentedStrictAffinoidAlgebra.isClosed_ideal hK _) I₁ I₂ hI

end StrictTestDomain.RationalData

end Langlands.Analytic
