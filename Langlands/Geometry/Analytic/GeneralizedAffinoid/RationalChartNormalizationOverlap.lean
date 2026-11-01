import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNormalizationMaps
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits

/-! # Compatibility of normalization with actual rational restrictions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {L : Type v} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (d e : RationalChart K A) (Q : PresentedStrictAffinoidAlgebra L)
  (ψ : BoundedRingHom A Q) (hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖)
  (τ : Fin d.arity → L) (υ : Fin e.arity → L)
  (hτ : ∀ j, ‖τ j‖ = d.radii j) (hυ : ∀ j, ‖υ j‖ = e.radii j)

private def productScalar : Fin (d.inter e).arity → L := fun a =>
  (Fin.cons 1 τ : Fin (d.arity + 1) → L) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 υ : Fin (e.arity + 1) → L) (finProdFinEquiv.symm a).2

omit [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
include hτ in
private theorem norm_extendedScalar (i : Fin (d.arity + 1)) :
    ‖(Fin.cons 1 τ : Fin (d.arity + 1) → L) i‖ =
      (Fin.cons 1 (fun j => d.radii j) : Fin (d.arity + 1) → ℝ) i := by
  induction i using Fin.cases <;> simp [hτ]

omit [CompleteSpace K] [IsUltrametricDist L] [CompleteSpace L] in
include hτ hυ in
private theorem norm_productScalar (a : Fin (d.inter e).arity) :
    ‖productScalar d e τ υ a‖ = (d.inter e).radii a := by
  change ‖(Fin.cons 1 τ : Fin (d.arity + 1) → L) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 υ : Fin (e.arity + 1) → L) (finProdFinEquiv.symm a).2‖ =
    (Fin.cons 1 (fun j => d.radii j) : Fin (d.arity + 1) → ℝ) (finProdFinEquiv.symm a).1 *
      (Fin.cons 1 (fun j => e.radii j) : Fin (e.arity + 1) → ℝ) (finProdFinEquiv.symm a).2
  rw [norm_mul, norm_extendedScalar d τ hτ, norm_extendedScalar e υ hυ]

omit [CompleteSpace K] [CompleteSpace L] in
private theorem extendedNormalizedNumerator (i : Fin (d.arity + 1)) :
    (Fin.cons (d.normalizedStrict Q ψ τ hτ).denominator
      (d.normalizedStrict Q ψ τ hτ).numerator : Fin (d.arity + 1) → Q) i =
    algebraMap L Q ((Fin.cons 1 τ : Fin (d.arity + 1) → L) i)⁻¹ *
      ψ (presentationMap K A
        ((Fin.cons d.denominator d.numerators : Fin (d.arity + 1) → _) i)) := by
  induction i using Fin.cases <;> simp [normalizedStrict]

omit [CompleteSpace K] in
private theorem normalizedStrict_inter :
    (d.inter e).normalizedStrict Q ψ (productScalar d e τ υ)
        (norm_productScalar d e τ υ hτ hυ) =
      (d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ υ hυ) := by
  unfold normalizedStrict StrictTestDomain.RationalData.inter
  congr 1
  · simp only [inter, map_mul]
  · funext a
    change algebraMap L Q (productScalar d e τ υ a)⁻¹ *
      ψ (presentationMap K A
        (RationalPresentation.RationalIntersection.numerators K A
          d.denominator e.denominator d.numerators e.numerators a)) =
      Langlands.Analytic.RationalIntersection.numerators L Q d.arity e.arity
        (d.normalizedStrict Q ψ τ hτ).denominator
        (e.normalizedStrict Q ψ υ hυ).denominator
        (d.normalizedStrict Q ψ τ hτ).numerator
        (e.normalizedStrict Q ψ υ hυ).numerator a
    unfold Langlands.Analytic.RationalIntersection.numerators
    rw [extendedNormalizedNumerator d Q ψ τ hτ,
      extendedNormalizedNumerator e Q ψ υ hυ]
    simp only [productScalar, RationalPresentation.RationalIntersection.numerators,
      mul_inv_rev, map_mul]
    ring

private def strictDataCongr
    {δ ε : StrictTestDomain.RationalData L Q} (h : δ = ε) :
    BoundedAlgHom L δ.algebra ε.algebra := by
  subst ε
  exact BoundedAlgHom.id L δ.algebra

private theorem strictDataCongr_baseMap
    {δ ε : StrictTestDomain.RationalData L Q} (h : δ = ε) (a : Q) :
    strictDataCongr Q h (δ.baseMap a) = ε.baseMap a := by
  subst ε
  rfl

/-- The actual original product quotient maps to the actual strict intersection
of the normalized charts. -/
def normalizedStrictOverlapMap :
    BoundedRingHom (d.inter e).algebra
      ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ υ hυ)).algebra :=
  (strictDataCongr Q (normalizedStrict_inter d e Q ψ τ υ hτ hυ)).toBoundedRingHom.comp
    ((d.inter e).normalizedStrictMap Q ψ hψ (productScalar d e τ υ)
      (norm_productScalar d e τ υ hτ hυ))

private theorem normalizedStrictOverlapMap_baseMap (a : A) :
    normalizedStrictOverlapMap d e Q ψ hψ τ υ hτ hυ ((d.inter e).baseMap a) =
      ((d.normalizedStrict Q ψ τ hτ).inter
        (e.normalizedStrict Q ψ υ hυ)).baseMap (ψ a) := by
  change strictDataCongr Q (normalizedStrict_inter d e Q ψ τ υ hτ hυ)
    ((d.inter e).normalizedStrictMap Q ψ hψ (productScalar d e τ υ)
      (norm_productScalar d e τ υ hτ hυ) ((d.inter e).baseMap a)) = _
  rw [normalizedStrictMap_baseMap, strictDataCongr_baseMap]

private theorem normalizedStrictOverlapMap_interLeft (a : d.algebra) :
    normalizedStrictOverlapMap d e Q ψ hψ τ υ hτ hυ ((interLeft d e).restriction a) =
      (StrictTestDomain.RationalData.interLeft
        (d.normalizedStrict Q ψ τ hτ) (e.normalizedStrict Q ψ υ hυ)).restriction
          (d.normalizedStrictMap Q ψ hψ τ hτ a) := by
  let δ := d.normalizedStrict Q ψ τ hτ
  let ε := e.normalizedStrict Q ψ υ hυ
  let ω := δ.inter ε
  let F := normalizedStrictOverlapMap d e Q ψ hψ τ υ hτ hυ
  let G := d.normalizedStrictMap Q ψ hψ τ hτ
  let r := (StrictTestDomain.RationalData.interLeft δ ε).restriction
  have h : F.comp (interLeft d e).restriction.toBoundedRingHom =
      r.toBoundedRingHom.comp G := by
    apply d.ringHom_ext_over_base ω.algebra (ω.baseMap.toBoundedRingHom.comp ψ)
      (fun a => (RationalLocalization.norm_baseMap_le L Q _ _ _ (ψ a)).trans (hψ a))
    · intro a
      change F ((interLeft d e).restriction (d.baseMap a)) = ω.baseMap (ψ a)
      have hr := congrArg (fun f : BoundedAlgHom K A (d.inter e).algebra => f a)
        (interLeft d e).comp_baseMap
      change (interLeft d e).restriction (d.baseMap a) = (d.inter e).baseMap a at hr
      rw [hr]
      exact normalizedStrictOverlapMap_baseMap d e Q ψ hψ τ υ hτ hυ a
    · intro a
      change r (G (d.baseMap a)) = ω.baseMap (ψ a)
      rw [normalizedStrictMap_baseMap]
      exact congrArg (fun f : BoundedAlgHom L Q ω.algebra => f (ψ a))
        (StrictTestDomain.RationalData.interLeft δ ε).restriction_comp_baseMap
  exact congrArg (fun f : BoundedRingHom d.algebra ω.algebra => f a) h

private theorem normalizedStrictOverlapMap_interRight (b : e.algebra) :
    normalizedStrictOverlapMap d e Q ψ hψ τ υ hτ hυ ((interRight d e).restriction b) =
      (StrictTestDomain.RationalData.interRight
        (d.normalizedStrict Q ψ τ hτ) (e.normalizedStrict Q ψ υ hυ)).restriction
          (e.normalizedStrictMap Q ψ hψ υ hυ b) := by
  let δ := d.normalizedStrict Q ψ τ hτ
  let ε := e.normalizedStrict Q ψ υ hυ
  let ω := δ.inter ε
  let F := normalizedStrictOverlapMap d e Q ψ hψ τ υ hτ hυ
  let G := e.normalizedStrictMap Q ψ hψ υ hυ
  let r := (StrictTestDomain.RationalData.interRight δ ε).restriction
  have h : F.comp (interRight d e).restriction.toBoundedRingHom =
      r.toBoundedRingHom.comp G := by
    apply e.ringHom_ext_over_base ω.algebra (ω.baseMap.toBoundedRingHom.comp ψ)
      (fun a => (RationalLocalization.norm_baseMap_le L Q _ _ _ (ψ a)).trans (hψ a))
    · intro a
      change F ((interRight d e).restriction (e.baseMap a)) = ω.baseMap (ψ a)
      have hr := congrArg (fun f : BoundedAlgHom K A (d.inter e).algebra => f a)
        (interRight d e).comp_baseMap
      change (interRight d e).restriction (e.baseMap a) = (d.inter e).baseMap a at hr
      rw [hr]
      exact normalizedStrictOverlapMap_baseMap d e Q ψ hψ τ υ hτ hυ a
    · intro a
      change r (G (e.baseMap a)) = ω.baseMap (ψ a)
      rw [normalizedStrictMap_baseMap]
      exact congrArg (fun f : BoundedAlgHom L Q ω.algebra => f (ψ a))
        (StrictTestDomain.RationalData.interRight δ ε).restriction_comp_baseMap
  exact congrArg (fun f : BoundedRingHom e.algebra ω.algebra => f b) h

/-- Actual compatibility on the original product intersection is preserved
by normalization, for independent coefficient-field universes. -/
theorem normalizedStrictMap_compatible (a : d.algebra) (b : e.algebra)
    (hab : (interLeft d e).restriction a = (interRight d e).restriction b) :
    (StrictTestDomain.RationalData.interLeft
      (d.normalizedStrict Q ψ τ hτ) (e.normalizedStrict Q ψ υ hυ)).restriction
        (d.normalizedStrictMap Q ψ hψ τ hτ a) =
    (StrictTestDomain.RationalData.interRight
      (d.normalizedStrict Q ψ τ hτ) (e.normalizedStrict Q ψ υ hυ)).restriction
        (e.normalizedStrictMap Q ψ hψ υ hυ b) := by
  rw [← normalizedStrictOverlapMap_interLeft, ← normalizedStrictOverlapMap_interRight, hab]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
