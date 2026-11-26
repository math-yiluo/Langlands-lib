import Langlands.Global.AdelicEisensteinFiniteCompactChangeProof
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Localized convolution and finite changes of the Iwasawa compact -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K₁ K₂ : Subgroup (AdelicGroupPoints F G)}
  (h₁ : IsIwasawaCompact p K₁) (h₂ : IsIwasawaCompact p K₂)
  (hmax₁ : IsMaximalCompactSubgroup F G K₁) (hmax₂ : IsMaximalCompactSubgroup F G K₂)
  (hArch : K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom)

local notation "A" => AdelicGroupPoints F G
local notation "Df" =>
  (K₁.map (ContinuousMonoidHom.toMonoidHom (finite F G)) ⊓
    K₂.map (ContinuousMonoidHom.toMonoidHom (finite F G)))

include hmax₁ hmax₂ hArch in
/-- The difference of the two heights is unchanged by right translations whose finite
coordinate belongs to both projected compact groups. -/
theorem IsIwasawaCompact.height_sub_mul_eq_of_finite_mem (x t : A) (ht : finite F G t ∈ Df) :
    h₁.height (x * t) - h₂.height (x * t) = h₁.height x - h₂.height x := by
  let Δ (y : A) := h₁.height y - h₂.height y
  have hfinite (y : A) : Δ y = Δ (ofFinite F G (finite F G y)) := by
    simpa only [pair_projections] using h₁.height_sub_pair_eq_of_infinite_eq h₂ hmax₁ hmax₂ hArch
      (infinite F G y) (finite F G y)
  let j := ofFinite F G (finite F G t)
  have hj : finite F G j = finite F G t := finite_ofFinite F G _
  have hjK {K : Subgroup A} (hK : IsMaximalCompactSubgroup F G K)
      (htK : finite F G t ∈ K.map (finite F G).toMonoidHom) : j ∈ K := by
    rw [IsMaximalCompactSubgroup.eq_comap_prod F G K hK]
    change infinite F G j ∈ K.map (infinite F G).toMonoidHom ∧
      finite F G j ∈ K.map (finite F G).toMonoidHom
    exact ⟨by rw [infinite_ofFinite]; exact Subgroup.one_mem _, hj.symm ▸ htK⟩
  calc
    Δ (x * t) = Δ (x * j) := by
      have hprod : finite F G (x * t) = finite F G (x * j) := by
        simp only [map_mul, hj]
      exact (hfinite (x * t)).trans
        ((congrArg (Δ ∘ ofFinite F G) hprod).trans (hfinite (x * j)).symm)
    _ = Δ x := by
      dsimp only [Δ]
      rw [h₁.height_mul_right _ (hjK hmax₁ ht.1), h₂.height_mul_right _ (hjK hmax₂ ht.2)]

omit [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
private theorem parameterTwist_eq_mul_heightDifference (lam : ComplexCharacterParameter F P)
    (f : A → ℂ) (x : A) :
    h₁.parameterTwist f lam x =
      Complex.exp (complexParameterPairing F P lam (h₁.height x - h₂.height x)) *
        h₂.parameterTwist f lam x := by
  have hheight : h₁.height x = (h₁.height x - h₂.height x) + h₂.height x :=
    (sub_add_cancel _ _).symm
  unfold IsIwasawaCompact.parameterTwist IsIwasawaCompact.heightPower
  conv_lhs => rw [hheight, map_add, Complex.exp_add]
  ring

variable [LocallyOfFiniteType G.X.hom]

include hmax₁ hmax₂ hArch in
/-- Localized right convolution commutes with multiplication by the ratio of the two
Iwasawa height powers. -/
theorem IsIwasawaCompact.rightConvolution_parameterTwist_of_finite_support
    {h : A → ℂ} (hs : ∀ t, h t ≠ 0 → finite F G t ∈ Df)
    (lam : ComplexCharacterParameter F P) (f : A → ℂ) (x : A) :
    rightConvolution F G h (h₁.parameterTwist f lam) x =
      Complex.exp (complexParameterPairing F P lam (h₁.height x - h₂.height x)) *
        rightConvolution F G h (h₂.parameterTwist f lam) x := by
  let ratio (y : A) :=
    Complex.exp (complexParameterPairing F P lam (h₁.height y - h₂.height y))
  have hratio (y : A) : h₁.parameterTwist f lam y = ratio y * h₂.parameterTwist f lam y :=
    parameterTwist_eq_mul_heightDifference h₁ h₂ lam f y
  change rightConvolution F G h (h₁.parameterTwist f lam) x =
    ratio x * rightConvolution F G h (h₂.parameterTwist f lam) x
  unfold rightConvolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : h t = 0
  · rw [ht, zero_mul, zero_mul, mul_zero]
  · have hr : ratio (x * t) = ratio x := by
      dsimp only [ratio]
      rw [h₁.height_sub_mul_eq_of_finite_mem h₂ hmax₁ hmax₂ hArch x t (hs _ ht)]
    rw [hratio (x * t), hr, mul_left_comm]

include hmax₁ hmax₂ hArch in
/-- One uniform equation transfers with its original coefficients between the two compacts
when each of its kernels is supported over the common finite compact. -/
theorem IsIwasawaCompact.convolutionEquation_of_finite_support_compact_change {n m : ℕ}
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P) (f : A → ℂ)
    {h : Fin m → A → ℂ} {b : Fin m → (Fin n → ℂ) → ℂ} {c : (Fin n → ℂ) → ℂ}
    (hs : ∀ j t, h j t ≠ 0 → finite F G t ∈ Df)
    (heq : ∀ s x, ∑ j, b j s * rightConvolution F G (h j) (h₂.parameterTwist f (e s)) x =
      c s * h₂.parameterTwist f (e s) x) :
    ∀ s x, ∑ j, b j s * rightConvolution F G (h j) (h₁.parameterTwist f (e s)) x =
      c s * h₁.parameterTwist f (e s) x := by
  intro s x
  let E := Complex.exp (complexParameterPairing F P (e s) (h₁.height x - h₂.height x))
  have hv : h₁.parameterTwist f (e s) x = E * h₂.parameterTwist f (e s) x :=
    parameterTwist_eq_mul_heightDifference h₁ h₂ (e s) f x
  rw [hv]
  calc
    _ = ∑ j, E * (b j s * rightConvolution F G (h j) (h₂.parameterTwist f (e s)) x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h₁.rightConvolution_parameterTwist_of_finite_support h₂ hmax₁ hmax₂ hArch (hs j)]
      exact mul_left_comm (b j s) E _
    _ = _ := by rw [← Finset.mul_sum, heq s x, mul_left_comm]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open AdelicGroupPoints

/-- If the maximal Iwasawa compacts have the same infinite projection, an equation for one
transfers to the other with the same coefficients and kernels supported over the common
finite projection. -/
def HarishChandraFiniteCompactTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G P : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (K₁ K₂ : Subgroup (AdelicGroupPoints F G))
    (h₁ : IsIwasawaCompact p K₁) (h₂ : IsIwasawaCompact p K₂),
    IsMaximalCompactSubgroup F G K₁ → IsMaximalCompactSubgroup F G K₂ →
    K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom →
    ∀ {n m : ℕ} (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F P)
      (f : AdelicGroupPoints F G → ℂ) (h : Fin m → AdelicGroupPoints F G → ℂ)
      (b : Fin m → (Fin n → ℂ) → ℂ) (c : (Fin n → ℂ) → ℂ),
      (∀ j t, h j t ≠ 0 →
        finite F G t ∈ K₁.map (finite F G).toMonoidHom ⊓ K₂.map (finite F G).toMonoidHom) →
      (∀ s x, ∑ j, b j s * rightConvolution F G (h j) (h₂.parameterTwist f (e s)) x =
        c s * h₂.parameterTwist f (e s) x) →
      ∀ s x, ∑ j, b j s * rightConvolution F G (h j) (h₁.parameterTwist f (e s)) x =
        c s * h₁.parameterTwist f (e s) x

theorem harishChandraFiniteCompactTransport : HarishChandraFiniteCompactTransportStatement.{u} := by
  intro F _ _ G P _ _ _ p _ K₁ K₂ h₁ h₂ hmax₁ hmax₂ hArch n m e f h b c hs heq
  exact h₁.convolutionEquation_of_finite_support_compact_change h₂ hmax₁ hmax₂ hArch e f hs heq

end Langlands.Global
