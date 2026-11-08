import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing

/-! # The central projection of a wave packet (Theorem VIII.4.2, the inclusion `A₂(G)_χ ⊂ p_χ(…)`)

Waldspurger, proof of Theorem VIII.4.2 (printed p. 330): for `ω ∈ E₂(G)_χ` with orbit `𝒪` and
`ψ ∈ C^∞(𝒪, G)`,
`(p_χ f_ψ)(g) = ∫_{A_G} χ⁻¹(a) f_ψ(a g) da = ∑_{ω' ∈ 𝒪_χ} (E^G_G ψ_{ω'})(g)` by Fourier
inversion, with `𝒪_χ = {ω' ∈ 𝒪 ; χ_{ω'} = χ}` finite; for `ψ` vanishing on `𝒪_χ − {ω}`, this is
`E^G_G ψ_ω`, whence `A₂(G)_χ ⊂ p_χ(°𝒞(G))` once `f_ψ ∈ °𝒞(G)` (Theorem VII.2.5).

For actual rational points (`M = G`), with the wave packet `rationalOrbitWavePacket`:

* `rationalOrbitCentralFiber`: the finite set `𝒪_χ`;
* `integral_central_rationalOrbitWavePacket`: the Fourier inversion formula for `p_χ f_ψ`;
* `integral_central_rationalOrbitWavePacket_of_vanishing`: `p_χ f_ψ = μ_A(A_G ∩ G¹) E^G_G ψ_ω`
  when `ψ` vanishes at the other classes of `𝒪_χ`.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u uV

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitCentralProjection1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitCentralProjection2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance instRationalOrbitCentralProjection3 : T2Space F := BruhatTits.localField_t2Space F
local instance instRationalOrbitCentralProjection4 : T2Space (GroupScheme.rationalPoints G) :=
  rationalPoint_t2Space F G
local instance instRationalOrbitCentralProjection5 :
    LocallyCompactSpace (GroupScheme.rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance instRationalOrbitCentralProjection6 :
    SecondCountableTopology (GroupScheme.rationalPoints G) := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  exact (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
local instance instRationalOrbitCentralProjection7 :
    Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- **`𝒪_χ`**: the classes `ω` of the orbit `𝒪` of `ω₀ = omega` whose central character on
`A_G` is `η`, `𝒪_η = {ω ∈ 𝒪 ; χ_ω = η}` (proof of Theorem VIII.4.2). It is finite
(`finite_setOf_rationalOrbitCentralCharacter_eq`). -/
def rationalOrbitCentralFiber :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      ((GroupScheme.rationalPoints.map s).range →* Circle) →
      Set (discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega eta
  exact {ω | rationalOrbitCentralCharacter s hs mu omega ω = eta}

/-- **The central projection of a wave packet** (proof of Theorem VIII.4.2, `M = G`): for a
section `ψ` over the orbit `𝒪` of `ω₀ = omega`, a character `η` of `A_G` and `g ∈ G(F)`, if
`ω ↦ (E^G_G ψ_ω)(g)` is continuous and `a ↦ f_ψ(a g)` is integrable, then
`∫_{A_G} η(a⁻¹) f_ψ(a g) dμ_A(a) = μ_A(A_G ∩ G¹) ∑_{ω ∈ 𝒪 ; χ_ω = η} (E^G_G ψ_ω)(g)`. -/
theorem integral_central_rationalOrbitWavePacket (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [μA.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle), Continuous eta →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) (g : GroupScheme.rationalPoints G),
      Continuous (fun ω => coefficientTensorMap _ (ψ ω) g) →
      Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA →
      ∫ a, ((eta a⁻¹ : Circle) : ℂ) *
          rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g)
          ∂μA =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          ∑ᶠ ω ∈ rationalOrbitCentralFiber s hs mu omega eta,
            coefficientTensorMap _ (ψ ω) g := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ μA _ eta heta ψ g hcont hintA
  have heq : (fun a : (GroupScheme.rationalPoints.map s).range => ((eta a⁻¹ : Circle) : ℂ) *
      rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g)) =
      rationalOrbitInversionIntegrand s hs mu hindex omega
        (rationalOrbitCentralCharacter s hs mu omega) eta
        (fun ω => coefficientTensorMap _ (ψ ω) g) := by
    funext a
    change _ * rationalOrbitWavePacket s hs mu hindex omega ψ
        ((a : GroupScheme.rationalPoints G) * g) =
      _ * ∫ ω, coefficientTensorMap _ (ψ ω) g *
        ((rationalOrbitCentralCharacter s hs mu omega ω a : Circle) : ℂ)
        ∂rationalNormalizedDiscreteSeriesOrbitMeasure s hs mu hindex omega
    rw [rationalOrbitWavePacket_apply]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (coefficientTensorMap_out_mul _ hs.range_le_center mu ω.val (ψ ω) a g).trans
        (mul_comm _ _))
  have hint : Integrable (rationalOrbitInversionIntegrand s hs mu hindex omega
      (rationalOrbitCentralCharacter s hs mu omega) eta
      (fun ω => coefficientTensorMap _ (ψ ω) g)) μA := by
    rw [← heq]
    refine hintA.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun a => (Circle.norm_coe _).le)
    exact (continuous_subtype_val.comp (heta.comp continuous_inv)).aestronglyMeasurable
  rw [heq]
  exact integral_rationalOrbitCentralInversion_eq_finsum s hs mu hindex hG omega μA eta hcont
    hint

/-- **`p_χ f_ψ = μ_A(A_G ∩ G¹) E^G_G ψ_{ω₁}`** when `ψ` vanishes at the classes `ω ≠ ω₁` of the
orbit with `χ_ω = η`, and `χ_{ω₁} = η` (proof of Theorem VIII.4.2: every coefficient of `ω₁` is
the central projection of a wave packet, given a section with these values). -/
theorem integral_central_rationalOrbitWavePacket_of_vanishing
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [μA.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle), Continuous eta →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj)
      (ω₁ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega),
      ω₁ ∈ rationalOrbitCentralFiber s hs mu omega eta →
      (∀ ω ∈ rationalOrbitCentralFiber s hs mu omega eta, ω ≠ ω₁ → ψ ω = 0) →
      ∀ g : GroupScheme.rationalPoints G,
      Continuous (fun ω => coefficientTensorMap _ (ψ ω) g) →
      Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA →
      ∫ a, ((eta a⁻¹ : Circle) : ℂ) *
          rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g)
          ∂μA =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          coefficientTensorMap _ (ψ ω₁) g := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ μA _ eta heta ψ ω₁ hω₁ hvan g hcont hintA
  rw [integral_central_rationalOrbitWavePacket s hs mu hindex hG omega μA eta heta ψ g hcont hintA]
  congr 1
  have hfin : (rationalOrbitCentralFiber s hs mu omega eta).Finite :=
    finite_setOf_rationalOrbitCentralCharacter_eq s hs mu hindex omega eta
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_eq_single_of_mem ω₁ (hfin.mem_toFinset.mpr hω₁) fun ω hω hne => ?_
  rw [hvan ω (hfin.mem_toFinset.mp hω) hne, map_zero]
  rfl

end Rational

end Langlands.HarishChandraSchwartz
