import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing
import Langlands.Representation.Unitary.AdmissibleFormUniqueness

/-! # The inner product of two wave packets (Proposition VII.2.2, `M = M' = G`)

Waldspurger, Proposition VII.2.2 (ii) for `M = M' = G` (printed pp. 318–319): for orbits `O`,
`O'` of discrete series of `G` and sections `ψ`, `ψ'`, the inner product `(f_{ψ'}, f_ψ)_G` is
`∫_O (ψ'_ω, ψ_ω) dω` if `O' = O` and `0` otherwise. Here `W(G|G|G) = {1}`,
`γ(G|G) = c(G|G) = 1`, `µ(ω) = 1` and `⁰c_{G|G}(1, ω)` is the identity.

The product `( , )` on `L(ω, G) = E ⊗ Ě` is that of V.2:
`(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)` for a positive invariant form on `E` and the
induced form on `Ě`. The definition `discreteSeriesCoefficientForm` uses a chosen positive
invariant form on the chosen representative of `ω`; `discreteSeriesCoefficientForm_eq` shows that
every positive invariant form gives the same product, as noted in V.2.

The proof follows Waldspurger's: Fubini (the double integral is assumed absolutely convergent)
gives `(f_{ψ'}, f_ψ)_G = ∫_{O'} (E^G_G ψ'_{ω'}, f_ψ)_G dω'`, and each pairing
`(E^G_G ψ'_{ω'}, f_ψ)_G` is `0` if `ω' ∉ O` and `μ_A(A_G ∩ G¹) (ψ'_{ω'}, ψ_{ω'})` if `ω' ∈ O`
(`RationalOrbitWavePacketPairing`). Instead of passing through `f̂_ψ` (formula (1) of the proof
and Proposition VII.2.1), the pairings computed in the proof of Proposition VII.2.1 are used
directly. The constant `μ_A(A_G ∩ G¹)` coming from the Fourier inversion over `A_G` is kept;
Waldspurger normalizes `mes(A_G ∩ K) = 1` instead (I.1).
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u uV

section Fubini

/-- **Fubini for a wave packet paired with a function**: if
`(g, ω) ↦ conj(e_ω(g)) f(g)` is integrable on `G × O`, then
`∫_G conj(∫_O e_ω(g) dω) f(g) dg = ∫_O ∫_G conj(e_ω(g)) f(g) dg dω`. -/
theorem integral_conj_integral_mul_eq_integral_integral {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μX : Measure X} {μY : Measure Y} [SFinite μX] [SFinite μY]
    (e : Y → X → ℂ) (f : X → ℂ)
    (hint : Integrable (fun p : X × Y => conj (e p.2 p.1) * f p.1) (μX.prod μY)) :
    ∫ x, conj (∫ y, e y x ∂μY) * f x ∂μX = ∫ y, ∫ x, conj (e y x) * f x ∂μX ∂μY := by
  have h : ∀ x, conj (∫ y, e y x ∂μY) * f x = ∫ y, conj (e y x) * f x ∂μY := fun x => by
    rw [← integral_conj, integral_mul_const]
  simp_rw [h]
  exact integral_integral_swap hint

end Fubini

section ClassForm

open CategoryTheory Langlands.Plancherel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (μ : Measure (G ⧸ A)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

/-- On an irreducible admissible representation, the form on `A ⊗ Ã` induced by a positive
invariant form does not depend on that form: two such forms differ by a positive scalar, and the
induced form on `Ã` scales by its inverse. -/
theorem coefficientTensorInvariantForm_independent (B : SmoothRep.{0, u, uV} ℂ G)
    (hB : IsAdmissible B.representation) (hi : B.representation.IsIrreducible)
    (b c : InvariantPositiveForm B.representation) :
    coefficientTensorInvariantForm B hcof hB b = coefficientTensorInvariantForm B hcof hB c := by
  obtain ⟨a, ha, rfl⟩ := b.exists_pos_rescale_eq c hcof hB hi
  exact (coefficientTensorInvariantForm_rescale B hcof hB b a ha).symm

/-- **The product on `L(ω, G) = E ⊗ Ě`** (Waldspurger V.2 for `P = G`): for a discrete-series
class `ω` with chosen representative `E`,
`(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)`, built from a chosen positive invariant form on
`E` (one exists by `isUnitarizable_of_isSquareIntegrable`) and the induced form on `Ě`. -/
def discreteSeriesCoefficientForm (ω : DiscreteSeriesClass.{u, uV} A hA μ) :
    InvariantPositiveForm (coefficientTensorAction (Quotient.out ω.val).obj) :=
  (coefficientTensorInvariantForm _ hcof (isSquareIntegrableModCentralSubgroup_out A hA μ ω).1
    (Classical.choice (isUnitarizable_of_isSquareIntegrable A hA μ
      (out_representation_central A hA μ ω) hcof (isSquareIntegrableModCentralSubgroup_out A hA μ ω)
      (Quotient.out ω.val).property.1))).rescale
    (discreteSeriesFormalDegree A hA μ hcof ω)⁻¹
    (inv_pos.mpr (discreteSeriesFormalDegree_pos A hA μ hcof ω))

/-- The product of V.2 does not depend on the positive invariant form on `E`: it is
`d(ω)⁻¹` times the form induced by any positive invariant form `b`. -/
theorem discreteSeriesCoefficientForm_eq (ω : DiscreteSeriesClass.{u, uV} A hA μ)
    (b : InvariantPositiveForm (Quotient.out ω.val).obj.representation) :
    discreteSeriesCoefficientForm A hA μ hcof ω =
      (coefficientTensorInvariantForm _ hcof (isSquareIntegrableModCentralSubgroup_out A hA μ ω).1
        b).rescale (discreteSeriesFormalDegree A hA μ hcof ω)⁻¹
        (inv_pos.mpr (discreteSeriesFormalDegree_pos A hA μ hcof ω)) := by
  unfold discreteSeriesCoefficientForm
  congr 1
  exact coefficientTensorInvariantForm_independent hcof _
    (isSquareIntegrableModCentralSubgroup_out A hA μ ω).1 (Quotient.out ω.val).property.1 _ b

/-- The product of V.2 on coefficient tensors: `(ψ₂, ψ₁) = d(ω)⁻¹ (ψ₂, ψ₁)_b` for every positive
invariant form `b` on the chosen representative of `ω`. -/
theorem discreteSeriesCoefficientForm_inner (ω : DiscreteSeriesClass.{u, uV} A hA μ)
    (b : InvariantPositiveForm (Quotient.out ω.val).obj.representation)
    (ψ₂ ψ₁ : CoefficientTensor (Quotient.out ω.val).obj) :
    (discreteSeriesCoefficientForm A hA μ hcof ω).inner ψ₂ ψ₁ =
      ((discreteSeriesFormalDegree A hA μ hcof ω : ℝ) : ℂ)⁻¹ *
        (coefficientTensorInvariantForm _ hcof
          (isSquareIntegrableModCentralSubgroup_out A hA μ ω).1 b).inner ψ₂ ψ₁ := by
  rw [discreteSeriesCoefficientForm_eq A hA μ hcof ω b, InvariantPositiveForm.rescale_inner,
    Complex.ofReal_inv]

variable [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {ν : Measure (LeftQuotient A)} (hνμ : ν.map (normalLeftQuotientHomeomorph A) = μ)

include hνμ in
/-- **III.1 (3) on `A\G` with the product of V.2**: for a discrete-series class `ω`,
`(E^G_G ψ₂, E^G_G ψ₁)_{A\G} = (ψ₂, ψ₁)`, with the pairing on `A\G` read through the chosen
representatives `q̇ = Quotient.out q`. -/
theorem integral_conj_mul_out_self_eq_inner (ω : DiscreteSeriesClass.{u, uV} A hA μ)
    (ψ₂ ψ₁ : CoefficientTensor (Quotient.out ω.val).obj) :
    ∫ q, conj (coefficientTensorMap _ ψ₂ q.out) * coefficientTensorMap _ ψ₁ q.out ∂ν =
      (discreteSeriesCoefficientForm A hA μ hcof ω).inner ψ₂ ψ₁ := by
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrable A hA μ (out_representation_central A hA μ ω)
    hcof (isSquareIntegrableModCentralSubgroup_out A hA μ ω) (Quotient.out ω.val).property.1
  rw [discreteSeriesCoefficientForm_inner A hA μ hcof ω b]
  exact integral_conj_mul_out_self A hA μ hcof hνμ ω b ψ₂ ψ₁

end ClassForm

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] instRationalOrbitWavePacket1 instRationalOrbitWavePacket2
  instRationalOrbitWavePacket3 instRationalOrbitWavePacket4 instRationalOrbitWavePacket5
  instRationalOrbitWavePacket6 instRationalOrbitWavePacket7

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- **The orbit product** `∫_O µ(ω) (ψ'_ω, ψ_ω) dω` of Proposition VII.2.2 (ii) for
`M = M' = G` (where `µ(ω) = 1`): for sections `ψ'`, `ψ` over the orbit `O` of `ω₀ = omega`,
the integral over `O`, for the I.1 orbit measure, of the product of V.2 of `ψ'_ω` and `ψ_ω`. -/
def rationalOrbitSectionInner :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) →
      (∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) → ℂ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega ψ' ψ
  exact ∫ ω, (discreteSeriesCoefficientForm _ hs.range_le_center mu CompactOpenSubgroup.cofinal
    ω.val).inner (ψ' ω) (ψ ω) ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega

theorem rationalOrbitSectionInner_apply :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (ψ' ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      rationalOrbitSectionInner s hs mu hindex omega ψ' ψ =
        ∫ ω, (discreteSeriesCoefficientForm _ hs.range_le_center mu CompactOpenSubgroup.cofinal
          ω.val).inner (ψ' ω) (ψ ω) ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex
            omega := by
  intro _ _ _ _ _
  rfl

omit [IsAffine T.X.left]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)] in
/-- Two discrete-series orbits are equal or disjoint: if `ω₀' ∉ O`, no element of the orbit `O'`
of `ω₀'` lies in `O`. -/
theorem notMem_discreteSeriesOrbit_of_mem :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      {omega omega' ω : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu},
      omega' ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →
      ω ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega' →
      ω ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega omega' ω homega' hω h
  unfold discreteSeriesOrbit at homega' hω h
  rw [← MulAction.orbit_eq_iff.mpr h, MulAction.orbit_eq_iff.mpr hω] at homega'
  exact homega' (MulAction.mem_orbit_self omega')

variable [MeasurableSpace (GroupScheme.rationalPoints G)]
  [BorelSpace (GroupScheme.rationalPoints G)]
  [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
  [BorelSpace (GroupScheme.rationalPoints.map s).range]
  [MeasurableSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]

/-- **Wave packets on different orbits are orthogonal** (Proposition VII.2.2 (ii) for
`M = M' = G`, the case `O' ≠ O`, where the sum is empty): if `ω₀' ∉ O`, then
`(f_{ψ'}, f_ψ)_G = 0` for every section `ψ'` over the orbit `O'` of `ω₀'`, provided the double
integral `∫_G ∫_{O'} conj((E^G_G ψ'_{ω'})(g)) f_ψ(g) dω' dg` converges absolutely. -/
theorem integral_conj_rationalOrbitWavePacket_mul_eq_zero
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
        omega' ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →
      ∀ (ψ' : ∀ ω' : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega',
          CoefficientTensor (Quotient.out ω'.val.val).obj),
      Integrable (fun p : GroupScheme.rationalPoints G ×
          discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
            (fun psi => (rationalNormCharacters G psi).toMul) omega' =>
          conj (coefficientTensorMap _ (ψ' p.2) p.1) *
            rationalOrbitWavePacket s hs mu hindex omega ψ p.1)
        (μG.prod (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega')) →
      ∫ g, conj (rationalOrbitWavePacket s hs mu hindex omega' ψ' g) *
          rationalOrbitWavePacket s hs mu hindex omega ψ g ∂μG = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ ν hν hνμ ψ hcont hintA omega' homega' ψ' hint
  have : IsFiniteMeasure (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega') :=
    isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega'
  have h1 : ∀ g, conj (rationalOrbitWavePacket s hs mu hindex omega' ψ' g) *
      rationalOrbitWavePacket s hs mu hindex omega ψ g =
        conj (∫ ω', coefficientTensorMap _ (ψ' ω') g
          ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega') *
          rationalOrbitWavePacket s hs mu hindex omega ψ g := fun g => by
    rw [rationalOrbitWavePacket_apply s hs mu hindex omega' ψ' g]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_conj_integral_mul_eq_integral_integral (fun ω' g => coefficientTensorMap _ (ψ' ω') g)
      (rationalOrbitWavePacket s hs mu hindex omega ψ) hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hint.prod_left_ae] with ω' hω'
  exact integral_conj_mul_rationalOrbitWavePacket_eq_zero s hs mu hindex hG hAc omega μA μG ν hν
    hνμ ψ hcont hintA ω'.val (notMem_discreteSeriesOrbit_of_mem s hs mu homega' ω'.2) (ψ' ω') hω'

/-- **Proposition VII.2.2 (ii) for `M = M' = G`, one orbit**: for sections `ψ'`, `ψ` over the
same orbit `O`, `(f_{ψ'}, f_ψ)_G = μ_A(A_G ∩ G¹) ∫_O (ψ'_ω, ψ_ω) dω`, provided the double
integral `∫_G ∫_O conj((E^G_G ψ'_ω)(g)) f_ψ(g) dω dg` converges absolutely. -/
theorem integral_conj_rationalOrbitWavePacket_mul
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ (ψ' : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      Integrable (fun p : GroupScheme.rationalPoints G ×
          discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
            (fun psi => (rationalNormCharacters G psi).toMul) omega =>
          conj (coefficientTensorMap _ (ψ' p.2) p.1) *
            rationalOrbitWavePacket s hs mu hindex omega ψ p.1)
        (μG.prod (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega)) →
      ∫ g, conj (rationalOrbitWavePacket s hs mu hindex omega ψ' g) *
          rationalOrbitWavePacket s hs mu hindex omega ψ g ∂μG =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          rationalOrbitSectionInner s hs mu hindex omega ψ' ψ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ ν hν hνμ ψ hcont hintA ψ' hint
  have : IsFiniteMeasure (rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) :=
    isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega
  have h1 : ∀ g, conj (rationalOrbitWavePacket s hs mu hindex omega ψ' g) *
      rationalOrbitWavePacket s hs mu hindex omega ψ g =
        conj (∫ ω, coefficientTensorMap _ (ψ' ω) g
          ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega) *
          rationalOrbitWavePacket s hs mu hindex omega ψ g := fun g => by
    rw [rationalOrbitWavePacket_apply s hs mu hindex omega ψ' g]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_conj_integral_mul_eq_integral_integral (fun ω g => coefficientTensorMap _ (ψ' ω) g)
      (rationalOrbitWavePacket s hs mu hindex omega ψ) hint,
    rationalOrbitSectionInner_apply, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hint.prod_left_ae] with ω hω
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrable _ hs.range_le_center mu
    (out_representation_central _ hs.range_le_center mu ω.val) CompactOpenSubgroup.cofinal
    (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu ω.val)
    (Quotient.out ω.val.val).property.1
  have h2 := integral_conj_mul_rationalOrbitWavePacket_of_mem s hs mu hindex hG hAc omega μA μG ν
    hν hνμ ψ hcont hintA ω.val ω.2 b (ψ' ω) hω
  have h4 := discreteSeriesCoefficientForm_inner _ hs.range_le_center mu CompactOpenSubgroup.cofinal
    ω.val b (ψ' ω) (ψ ω)
  exact h2.trans (congrArg (HMul.hMul _) h4.symm)

end Rational

end Langlands.HarishChandraSchwartz
