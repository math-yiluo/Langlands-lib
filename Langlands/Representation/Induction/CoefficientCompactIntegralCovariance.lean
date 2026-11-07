import Langlands.Representation.Induction.CoefficientCompactCoinvariants
import Langlands.Representation.Induction.CompactAutomorphismIntegralProof

/-! # Naturality and automorphism covariance of the native compact integral -/

noncomputable section

namespace Langlands.Induction.Coefficient

open MeasureTheory MeasureTheory.Measure
open Langlands.Jacquet.CoefficientRestriction
open scoped NNReal ENNReal

universe uR uG uV uW

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module R V] [Module ℂ V]
  [IsScalarTower ℂ R V]
  {W : Type uW} [AddCommGroup W] [Module R W] [Module ℂ W]
  [IsScalarTower ℂ R W]

/-- Restrict an actual coefficient intertwiner to complex scalars. -/
def complexIntertwiningMap {K : Type*} [Group K]
    {σ : Representation R K V} {τ : Representation R K W} (T : σ.IntertwiningMap τ) :
    (complexRepresentation σ).IntertwiningMap (complexRepresentation τ) where
  toLinearMap := T.toLinearMap.restrictScalars ℂ
  isIntertwining' g := LinearMap.ext fun v =>
    congrArg (fun f : V →ₗ[R] W => f v) (T.isIntertwining' g)

@[simp]
theorem complexIntertwiningMap_apply {K : Type*} [Group K]
    {σ : Representation R K V} {τ : Representation R K W}
    (T : σ.IntertwiningMap τ) (v : V) :
    complexIntertwiningMap T v = T v := rfl

/-- The scalar-restriction comparison commutes with actual quotient maps. -/
theorem fullCoinvariantsComplexEquiv_natural {K : Type*} [Group K]
    {σ : Representation R K V} {τ : Representation R K W}
    (T : σ.IntertwiningMap τ)
    (q : Representation.Coinvariants (complexRepresentation σ)) :
    fullCoinvariantsComplexEquiv τ
        (Representation.Coinvariants.map _ _ (complexIntertwiningMap T) q) =
      Representation.Coinvariants.map σ τ T (fullCoinvariantsComplexEquiv σ q) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rfl

/-- Restriction and postcomposition preserve the same compact functions. -/
theorem compactFunctionsComplexEquiv_natural (H : Subgroup G)
    {σ : Representation R H V} {τ : Representation R H W}
    (T : σ.IntertwiningMap τ) (f : CompactFunctions H σ) :
    compactFunctionsComplexEquiv H τ (compactInducedMap H T f) =
      compactInducedMap H (complexIntertwiningMap T) (compactFunctionsComplexEquiv H σ f) := by
  ext x
  rfl

section Naturality

variable (H : Subgroup G) {σ : Representation R H V} {τ : Representation R H W}
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]
  (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]

/-- Native naturality before descent, for inducing intertwiners in independent universes. -/
theorem compactCoinvariantIntegral_natural (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) :
    compactCoinvariantIntegral H τ ν (compactInducedMap H T f) =
      Representation.Coinvariants.map σ τ T (compactCoinvariantIntegral H σ ν f) := by
  change fullCoinvariantsComplexEquiv τ
    (Induction.compactCoinvariantIntegral H (complexRepresentation τ) ν
      (compactFunctionsComplexEquiv H τ (compactInducedMap H T f))) = _
  rw [compactFunctionsComplexEquiv_natural,
    Induction.compactCoinvariantIntegral_natural, fullCoinvariantsComplexEquiv_natural]
  rfl

variable (hν : ∀ g : G, MeasurePreserving (QuotientIntegration.rightTranslate H g) ν ν)

/-- The descended native quotient integral is natural on every original quotient class. -/
theorem compactCoinvariantDesc_natural_apply (T : σ.IntertwiningMap τ)
    (q : Representation.Coinvariants (compactInduced H σ)) :
    compactCoinvariantDesc H τ ν hν
        (Representation.Coinvariants.map _ _ (compactInducedMap H T) q) =
      Representation.Coinvariants.map σ τ T (compactCoinvariantDesc H σ ν hν q) := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  exact compactCoinvariantIntegral_natural H ν T f

/-- The same naturality as an equality of native coefficient-linear maps. -/
theorem compactCoinvariantDesc_natural (T : σ.IntertwiningMap τ) :
    (compactCoinvariantDesc H τ ν hν).comp
        (Representation.Coinvariants.map _ _ (compactInducedMap H T)) =
      (Representation.Coinvariants.map σ τ T).comp (compactCoinvariantDesc H σ ν hν) := by
  apply LinearMap.ext
  intro q
  exact compactCoinvariantDesc_natural_apply H ν hν T q

end Naturality

section AutomorphismQuotient

variable (H : Subgroup G) (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

/-- The native relation quotients before and after a subgroup automorphism
have the same original vector classes. -/
def automorphismCoinvariantsEquiv (σ : Representation R H V) :
    Representation.Coinvariants (automorphismInducing H α hα σ) ≃ₗ[R]
      Representation.Coinvariants σ where
  __ := Representation.Coinvariants.lift (automorphismInducing H α hα σ)
    (Representation.Coinvariants.mk σ) (fun h => LinearMap.ext fun v =>
      Representation.Coinvariants.mk_self_apply σ
        (QuotientIntegration.subgroupAutomorphism H α hα h) v)
  invFun := Representation.Coinvariants.lift σ
    (Representation.Coinvariants.mk (automorphismInducing H α hα σ)) (fun h => by
      apply LinearMap.ext
      intro v
      change Representation.Coinvariants.mk (automorphismInducing H α hα σ)
        (σ h v) = Representation.Coinvariants.mk (automorphismInducing H α hα σ) v
      let e := QuotientIntegration.subgroupAutomorphism H α hα
      have key := Representation.Coinvariants.mk_self_apply
        (automorphismInducing H α hα σ) (e.symm h) v
      change Representation.Coinvariants.mk (automorphismInducing H α hα σ)
        (σ (e (e.symm h)) v) = _ at key
      simpa only [e.apply_symm_apply] using key)
  left_inv q := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
    rfl
  right_inv q := by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
    rfl

omit [Algebra ℂ R] [IsTopologicalGroup G] [Module ℂ V] [IsScalarTower ℂ R V] in
@[simp]
theorem automorphismCoinvariantsEquiv_mk (σ : Representation R H V) (v : V) :
    automorphismCoinvariantsEquiv H α hα σ
      (Representation.Coinvariants.mk (automorphismInducing H α hα σ) v) =
        Representation.Coinvariants.mk σ v := rfl

omit [Algebra ℂ R] [IsTopologicalGroup G] [Module ℂ V] [IsScalarTower ℂ R V]
  [Module ℂ W] [IsScalarTower ℂ R W] in
/-- The native automorphism comparison is natural for all native intertwiners. -/
theorem automorphismCoinvariantsEquiv_natural
    {σ : Representation R H V} {τ : Representation R H W}
    (T : σ.IntertwiningMap τ)
    (q : Representation.Coinvariants (automorphismInducing H α hα σ)) :
    automorphismCoinvariantsEquiv H α hα τ
        (Representation.Coinvariants.map _ _ (automorphismInducingMap H α hα T) q) =
      Representation.Coinvariants.map σ τ T
        (automorphismCoinvariantsEquiv H α hα σ q) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rfl

omit [IsTopologicalGroup G] in
/-- Scalar restriction does not change the automorphism transport. -/
theorem automorphismCoinvariantsEquiv_complex (σ : Representation R H V)
    (q : Representation.Coinvariants
      (complexRepresentation (automorphismInducing H α hα σ))) :
    automorphismCoinvariantsEquiv H α hα σ
        (fullCoinvariantsComplexEquiv (automorphismInducing H α hα σ) q) =
      fullCoinvariantsComplexEquiv σ
        (Induction.automorphismCoinvariantsEquiv H α hα (complexRepresentation σ) q) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ q
  rfl

/-- Compact precomposition retains the original values under scalar restriction. -/
theorem compactFunctionsComplexEquiv_precompose (σ : Representation R H V)
    (f : CompactFunctions H σ) :
    compactFunctionsComplexEquiv H (automorphismInducing H α hα σ)
        (precomposeCompactInducedEquiv H α hα σ f) =
      precomposeCompactInducedEquiv H α hα (complexRepresentation σ)
        (compactFunctionsComplexEquiv H σ f) := by
  ext x
  rfl

end AutomorphismQuotient

section IntegralCovariance

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H]
  {μG : Measure G} {μH : Measure H}
  [IsHaarMeasure μG] [μG.Regular] [IsHaarMeasure μH] [μH.Regular]
  [IsMulRightInvariant μH]
  [MeasurableSpace (QuotientIntegration.LeftQuotient H)]
  [BorelSpace (QuotientIntegration.LeftQuotient H)]
  (ν : Measure (QuotientIntegration.LeftQuotient H)) [IsFiniteMeasureOnCompacts ν]
  (hν : QuotientIntegration.IsCompatible H μG μH ν)
  (α : G ≃ₜ* G) (hα : ∀ x : G, α x ∈ H ↔ x ∈ H)

include hH hν in
/-- The actual native integral of forward precomposition scales by the
subgroup-to-ambient Haar ratio, transported on original vector classes. -/
theorem compactCoinvariantIntegral_automorphism (σ : Representation R H V)
    (f : CompactFunctions H σ) :
    automorphismCoinvariantsEquiv H α hα σ
        (compactCoinvariantIntegral H (automorphismInducing H α hα σ) ν
          (precomposeCompactInducedEquiv H α hα σ f)) =
      ((((mulEquivHaarChar (QuotientIntegration.subgroupAutomorphism H α hα) /
          mulEquivHaarChar α : ℝ≥0) : ℝ) : ℂ)) • compactCoinvariantIntegral H σ ν f := by
  change automorphismCoinvariantsEquiv H α hα σ
    (fullCoinvariantsComplexEquiv (automorphismInducing H α hα σ)
      (Induction.compactCoinvariantIntegral H
        (complexRepresentation (automorphismInducing H α hα σ)) ν
        (compactFunctionsComplexEquiv H (automorphismInducing H α hα σ)
          (precomposeCompactInducedEquiv H α hα σ f)))) = _
  rw [compactFunctionsComplexEquiv_precompose, automorphismCoinvariantsEquiv_complex]
  change fullCoinvariantsComplexEquiv σ
    (Induction.automorphismCoinvariantsEquiv H α hα (complexRepresentation σ)
      (Induction.compactCoinvariantIntegral H
        (automorphismInducing H α hα (complexRepresentation σ)) ν
        (precomposeCompactInducedEquiv H α hα (complexRepresentation σ)
          (compactFunctionsComplexEquiv H σ f)))) = _
  rw [Induction.compactCoinvariantIntegral_automorphism H hH ν hν α hα]
  rw [map_smul]
  rfl

end IntegralCovariance

end Langlands.Induction.Coefficient
