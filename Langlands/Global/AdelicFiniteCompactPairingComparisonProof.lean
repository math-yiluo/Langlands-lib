import Langlands.Global.AdelicFiniteCompactPairingComparisonStatement
import Langlands.Analysis.Local.CompactFactorizationModularComparison
import Langlands.Global.AdelicSquareIntegrableCompactChange
import Langlands.Global.AdelicStandardPositiveLog
import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicLocalModularComparison
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof
import Langlands.Global.AdelicIwasawaCompatibleMeasureReduction
import Langlands.Global.AdelicNormOneHaarRightInvariantProof
import Langlands.Global.AdelicEisensteinCompactBounds

/-! # Proof of the finite compact comparison for `A^2_P` and the Levi pairings (3.7)

`Langlands.Global.finiteCompactPairingComparison` proves
`Langlands.Global.FiniteCompactPairingComparisonStatement`.

* The finite partition and the clopen fibres of `Δ = H_P^{K₁} - H_P^{K₂}` come from
  `IsIwasawaCompact.finite_range_height_sub` and
  `IsIwasawaCompact.exists_parameterTwist_clopen_decomposition`.
* The cut `1_{Δ = v} φ` of `φ ∈ A^2_P(K₁)` lies in `A^2_P(K₁)` (automorphy by
  `IsAutomorphicFunctionOn.indicator_finite`, the `A^n_P` condition and the `L²` bound by left
  `P(𝔸)`-invariance of `Δ`), hence in `A^2_P(K₂)` by
  `StandardParabolicFamily.isSquareIntegrableInducedForm_of_compact_change`.
* For the pairings, the slice `S_θ(g) = ∫_{M(F) \ M(𝔸)^1} θ(m g) dm` of a continuous
  invariant `θ ≥ 0` supported in `{Δ = v}` is left `P(𝔸)^1`-invariant. The function
  `Φ(g) = δ_P(a(g)) S_θ(x a(g)⁻¹ g)`, with `a(g)` a continuous lift of `H_P^{K₁}(g)` to `P(𝔸)`,
  satisfies `Φ(p g) = δ_P(p) Φ(g)`, so
  `CompactFactorization.exists_lintegral_compact_eq_of_modular` compares its integrals over
  `K₁` and `K₂` with a constant independent of `θ`. On `K₁` it is `S_θ(x k)`, on `K₂` it is
  `δ_P(x) δ_P(x')⁻¹ S_θ(x' k)`, and Tonelli turns these into the pairing integrals. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductIntegrable

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

section Characters

/-- Inverses change the sign of the logarithmic functional. -/
private theorem characterLog_inv' (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
    (x : AdelicGroupPoints F H) : characterLog F H x⁻¹ = -characterLog F H x := by
  have h := characterLog_mul F H x x⁻¹
  rw [mul_inv_cancel, characterLog_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- A character norm depends only on the logarithmic functional. -/
private theorem characterNorm_eq_of_characterLog_eq (H : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine H.X.left] (χ : AlgebraicCharacter F H) {a b : AdelicGroupPoints F H}
    (h : characterLog F H a = characterLog F H b) : characterNorm F H χ a = characterNorm F H χ b := by
  have hab : a * b⁻¹ ∈ normOneSubgroup F H := by
    rw [← characterLog_eq_zero_iff, characterLog_mul, characterLog_inv', h, add_neg_cancel]
  have h1 : characterNorm F H χ (a * b⁻¹) = 1 := (mem_normOneSubgroup F H _).mp hab χ
  calc characterNorm F H χ a = characterNorm F H χ (a * b⁻¹ * b) := by rw [inv_mul_cancel_right]
    _ = characterNorm F H χ b := by rw [map_mul, h1, one_mul]

/-- A continuous section of the logarithmic functional of `P`, through the positive points of
the split component. -/
private theorem exists_characterLog_section :
    ∃ σ : Multiplicative (RealCharacterDual F (𝓕.P J)) →ₜ* AdelicGroupPoints F (𝓕.P J),
      ∀ ℓ, characterLog F (𝓕.P J) (σ ℓ) = Multiplicative.toAdd ℓ := by
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.val, 𝓕.f J⟩, 𝓕.isCompatible J⟩
  have hinj := characterRestrict_splitComponent_injective r
  have hsurj := r.isCompatible.levi.characterRestrict_bijective.2
  have hrange : (characterRestrict (𝓕.a J ≫ 𝓕.l J)).range =
      (characterRestrict (𝓕.a J)).range := by
    ext χ
    change (∃ x, characterRestrict (𝓕.a J ≫ 𝓕.l J) x = χ) ↔ ∃ y, characterRestrict (𝓕.a J) y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict (𝓕.l J) x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  let : (characterRestrict (𝓕.a J ≫ 𝓕.l J)).range.FiniteIndex := hrange.symm ▸
    r.isCompatible.splitComponent.finiteIndex_range_characterRestrict
      r.isCompatible.levi.isConnectedReductive
  obtain ⟨D, hD, ⟨e⟩⟩ := r.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let : Fintype D := @Fintype.ofFinite D hD
  refine ⟨PositiveRealTorus.logSection F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) hinj D e, fun ℓ => ?_⟩
  exact congrArg Multiplicative.toAdd
    (PositiveRealTorus.characterLogHom_logSection F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) hinj D e ℓ)

/-- The modular character of `P(𝔸)` is the idele norm of `det(Ad | Lie P)`. -/
private theorem modularCharacter_eq_adjointNorm (q : AdelicGroupPoints F (𝓕.P J)) :
    Measure.modularCharacter q =
      (characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul q : ℝ≥0) := by
  have hsm : Smooth (𝓕.P J).X.hom := (𝓕.isCompatible J).parabolic.smooth
  exact modularCharacter_eq_characterNorm_of_local F (𝓕.P J) _
    (PlaceGroupPoints.localModularCharacterAdjointDeterminant F (𝓕.P J) hsm) q

/-- A point of `P(𝔸)` with zero logarithmic functional is `l(m) u` with `m ∈ M(𝔸)^1` and `u` in
the unipotent radical. -/
private theorem exists_levi_normOne_decomposition {y : AdelicGroupPoints F (𝓕.P J)}
    (hy : y ∈ normOneSubgroup F (𝓕.P J)) :
    ∃ m ∈ normOneSubgroup F (𝓕.M J), ∃ u : AdelicGroupPoints F (𝓕.U J),
      map F (𝓕.M J) (𝓕.P J) (𝓕.l J) m * map F (𝓕.U J) (𝓕.P J) (𝓕.iU J) u = y := by
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.val, 𝓕.f J⟩, 𝓕.isCompatible J⟩
  let : IsIso (subgroupMultiplication (𝓕.l J) (𝓕.iU J)) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r 𝓕.connectedReductive
      (𝓕.isUnipotentRadical J)
  have hsurj := r.isCompatible.levi.characterRestrict_bijective.2
  let m : AdelicGroupPoints F (𝓕.M J) := leviComponent (𝓕.l J) (𝓕.iU J) y
  let u : AdelicGroupPoints F (𝓕.U J) := radicalComponent (𝓕.l J) (𝓕.iU J) y
  have hsplit : map F (𝓕.M J) (𝓕.P J) (𝓕.l J) m * map F (𝓕.U J) (𝓕.P J) (𝓕.iU J) u = y :=
    leviComponent_mul_radicalComponent (𝓕.l J) (𝓕.iU J) y
  refine ⟨m, ?_, u, hsplit⟩
  have hy0 : characterLog F (𝓕.P J) y = 0 := (characterLog_eq_zero_iff F (𝓕.P J) y).mpr hy
  have hu0 : characterLog F (𝓕.P J) (map F (𝓕.U J) (𝓕.P J) (𝓕.iU J) u) = 0 := by
    rw [characterLog_map, characterLog_eq_zero_of_isUnipotent
      (𝓕.isUnipotentRadical J).1.isUnipotent, map_zero]
  have hm0 : realCharacterDualMap F (𝓕.M J) (𝓕.P J) (𝓕.l J) (characterLog F (𝓕.M J) m) = 0 := by
    rw [← characterLog_map]
    calc characterLog F (𝓕.P J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) m)
        = characterLog F (𝓕.P J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) m) +
            characterLog F (𝓕.P J) (map F (𝓕.U J) (𝓕.P J) (𝓕.iU J) u) := by rw [hu0, add_zero]
      _ = 0 := by rw [← characterLog_mul, hsplit, hy0]
  apply (characterLog_eq_zero_iff F (𝓕.M J) m).mp
  apply AddMonoidHom.ext
  intro χ
  obtain ⟨χ', rfl⟩ := hsurj χ
  exact DFunLike.congr_fun hm0 χ'

end Characters

section Slice

/-- The slice `g ↦ ∫_{M(F) \ M(𝔸)^1} θ(m g) dm` of a function `θ ≥ 0` on `G(𝔸)`. -/
private def leviSlice (θ : AdelicGroupPoints F G → ℝ≥0∞) (g : AdelicGroupPoints F G) : ℝ≥0∞ :=
  ∫⁻ z, θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      ((Quotient.out z : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) * g)
    ∂(normOneRationalQuotientHaarMeasure F (𝓕.M J))

section Generic

variable {E : Type} (θ : AdelicGroupPoints F G → E)
  (hθΓ : ∀ r₀ ∈ parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J), ∀ g, θ (r₀ * g) = θ g)

include hθΓ in
/-- A left `U(𝔸) M(F)`-invariant function is left invariant under the rational points of
`M(𝔸)^1`, in Levi coordinates. -/
private theorem rational_invariant (g : AdelicGroupPoints F G) :
    ∀ r₀ ∈ rationalNormOneSubgroup F (𝓕.M J), ∀ n : normOneSubgroup F (𝓕.M J),
      θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
          ((r₀ * n : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) * g) =
        θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (n : AdelicGroupPoints F (𝓕.M J)) * g) := by
  intro r₀ hr n
  have hr' : ((r₀ : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) ∈
      rationalSubgroup F (𝓕.M J) := (mem_rationalNormOneSubgroup_iff r₀).mp hr
  have hmem := map_map_mem_parabolicQuotientSubgroup (𝓕.p J) (𝓕.iU J) (𝓕.l J) hr'
  rw [Subgroup.coe_mul, map_mul, mul_assoc, InducedInnerProductIntegrable.map_comp_apply]
  exact hθΓ _ hmem _

include hθΓ in
/-- The slice integrand `(x, z) ↦ θ(m_z h(x))` is continuous on `X × M(F) \ M(𝔸)^1`. -/
private theorem continuous_slice_integrand [TopologicalSpace E] (hθ : Continuous θ)
    {X : Type} [TopologicalSpace X] (h : X → AdelicGroupPoints F G) (hh : Continuous h) :
    Continuous (fun z : X × NormOneRationalQuotient F (𝓕.M J) =>
      θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          h z.1)) := by
  refine LeftCosetSpace.continuous_out_of_invariant (rationalNormOneSubgroup F (𝓕.M J))
    (fun x (n : normOneSubgroup F (𝓕.M J)) =>
      θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (n : AdelicGroupPoints F (𝓕.M J)) * h x)) ?_ ?_
  · exact hθ.comp (((map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).continuous.comp
      (continuous_subtype_val.comp continuous_snd)).mul (hh.comp continuous_fst))
  · intro x r₀ hr n
    exact rational_invariant 𝓕 J θ hθΓ (h x) r₀ hr n

include hθΓ in
/-- The pairing integrand `(k, z) ↦ θ(x m_z k)` is continuous on `K × M(F) \ M(𝔸)^1` for
`x ∈ 𝔄_P`. -/
private theorem continuous_pairing_integrand [TopologicalSpace E] (hθ : Continuous θ)
    (K : Subgroup (AdelicGroupPoints F G)) {x : AdelicGroupPoints F (𝓕.P J)}
    (hx : x ∈ 𝓕.positiveSplitComponent J) :
    Continuous (fun z : K × NormOneRationalQuotient F (𝓕.M J) =>
      θ (map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          (z.1 : AdelicGroupPoints F G))) := by
  have hcomm : ∀ (n : AdelicGroupPoints F (𝓕.M J)) (k : AdelicGroupPoints F G),
      map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) n * k =
        map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) n * (map F (𝓕.P J) G (𝓕.p J) x * k) := by
    intro n k
    rw [(𝓕.commute_positiveSplitComponent_levi J ⟨x, hx⟩ n).eq, mul_assoc]
  simp_rw [hcomm]
  exact continuous_slice_integrand 𝓕 J θ hθΓ hθ
    (fun k : K => map F (𝓕.P J) G (𝓕.p J) x * (k : AdelicGroupPoints F G))
    (continuous_const.mul continuous_subtype_val)

end Generic

variable (θ : AdelicGroupPoints F G → ℝ≥0∞)
  (hθΓ : ∀ r₀ ∈ parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J), ∀ g, θ (r₀ * g) = θ g)

include hθΓ in
private theorem measurable_leviSlice (hθ : Continuous θ) : Measurable (𝓕.leviSlice J θ) := by
  have hc := continuous_slice_integrand 𝓕 J θ hθΓ hθ (fun g : AdelicGroupPoints F G => g)
    continuous_id
  have hm : Measurable (fun z : NormOneRationalQuotient F (𝓕.M J) × AdelicGroupPoints F G =>
      θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.1 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          z.2)) :=
    (hc.comp continuous_swap).measurable
  exact hm.lintegral_prod_left'

include hθΓ in
/-- The slice is left invariant under `P(𝔸)^1 = U(𝔸) M(𝔸)^1`. -/
private theorem leviSlice_normOne_mul (hθ : Continuous θ) {y : AdelicGroupPoints F (𝓕.P J)}
    (hy : y ∈ normOneSubgroup F (𝓕.P J)) (g : AdelicGroupPoints F G) :
    𝓕.leviSlice J θ (map F (𝓕.P J) G (𝓕.p J) y * g) = 𝓕.leviSlice J θ g := by
  obtain ⟨m, hm, u, rfl⟩ := exists_levi_normOne_decomposition 𝓕 J hy
  have hM : IsConnectedReductive (𝓕.M J) := (𝓕.isCompatible J).levi.isConnectedReductive
  have := normOneHaarRightInvariant F (𝓕.M J) hM.smooth hM.connectedSpace
  let m' : normOneSubgroup F (𝓕.M J) := ⟨m, hm⟩
  let Γ₀ := rationalNormOneSubgroup F (𝓕.M J)
  let iP := map F (𝓕.P J) G (𝓕.p J)
  let lP := map F (𝓕.M J) (𝓕.P J) (𝓕.l J)
  let uP := map F (𝓕.U J) (𝓕.P J) (𝓕.iU J)
  let f : normOneSubgroup F (𝓕.M J) → ℝ≥0∞ := fun n =>
    θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) (n : AdelicGroupPoints F (𝓕.M J)) * g)
  have hf : Continuous f := hθ.comp (((map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).continuous.comp
    continuous_subtype_val).mul continuous_const)
  have hfinv : ∀ r₀ ∈ Γ₀, ∀ n, f (r₀ * n) = f n := rational_invariant 𝓕 J θ hθΓ g
  have hpt : ∀ z : NormOneRationalQuotient F (𝓕.M J),
      θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
          ((Quotient.out z : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (iP (lP m * uP u) * g)) =
        f (Quotient.out (LeftCosetSpace.rightTranslate Γ₀ m' z)) := by
    intro z
    have hz : LeftCosetSpace.rightTranslate Γ₀ m' z =
        LeftCosetSpace.mk Γ₀ (Quotient.out z * m') := by
      conv_lhs => rw [← Quotient.out_eq z]
      rfl
    rw [hz, LeftCosetSpace.out_mk_of_invariant Γ₀ f hfinv]
    let n : AdelicGroupPoints F (𝓕.M J) :=
      ((Quotient.out z : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) * m
    have hU : lP n * uP u * (lP n)⁻¹ ∈ (SubgroupFunctor.range (𝓕.iU J)).carrier _ :=
      (𝓕.isUnipotentRadical J).1.isNormal _ _ _ trivial ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hU
    have hwP : uP w = lP n * uP u * (lP n)⁻¹ := hw
    have hwG : map F (𝓕.U J) G (𝓕.iU J ≫ 𝓕.p J) w ∈
        parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J) :=
      Subgroup.mem_sup_left ⟨w, rfl⟩
    have hmul : map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
          ((Quotient.out z : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (iP (lP m * uP u) * g) =
        map F (𝓕.U J) G (𝓕.iU J ≫ 𝓕.p J) w *
          (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) n * g) := by
      rw [InducedInnerProductIntegrable.map_comp_apply, InducedInnerProductIntegrable.map_comp_apply,
        InducedInnerProductIntegrable.map_comp_apply]
      calc iP (lP ((Quotient.out z : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J))) *
            (iP (lP m * uP u) * g) = iP (lP n * uP u) * g := by
            simp only [n, map_mul, mul_assoc]
        _ = iP (uP w * lP n) * g := by rw [hwP, inv_mul_cancel_right]
        _ = iP (uP w) * (iP (lP n) * g) := by rw [map_mul, mul_assoc]
    change θ _ = θ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
      (((Quotient.out z : normOneSubgroup F (𝓕.M J)) * m' : normOneSubgroup F (𝓕.M J)) :
        AdelicGroupPoints F (𝓕.M J)) * g)
    rw [Subgroup.coe_mul, hmul]
    exact hθΓ _ hwG _
  unfold leviSlice
  refine (lintegral_congr hpt).trans ?_
  exact (measurePreserving_rightTranslate_normOneRationalQuotientHaarMeasure F (𝓕.M J) m').lintegral_comp
    (LeftCosetSpace.measurable_out_of_invariant Γ₀ hf.measurable hfinv)

include hθΓ in
/-- Tonelli in the pairing: the pairing integral of `θ` at `x ∈ 𝔄_P` is the integral over `K` of
the slice at `x k`. -/
private theorem lintegral_pairing_eq_slice (hθ : Continuous θ) (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G))) {x : AdelicGroupPoints F (𝓕.P J)}
    (hx : x ∈ 𝓕.positiveSplitComponent J) :
    ∫⁻ z, θ (map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          (z.1 : AdelicGroupPoints F G)) ∂(𝓕.squareIntegrablePairingMeasure K hK J) =
      ∫⁻ k, 𝓕.leviSlice J θ (map F (𝓕.P J) G (𝓕.p J) x * (k : AdelicGroupPoints F G))
        ∂(compactHaarProbability F G K hK) := by
  have hcomm : ∀ (n : AdelicGroupPoints F (𝓕.M J)) (k : AdelicGroupPoints F G),
      map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) n * k =
        map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) n * (map F (𝓕.P J) G (𝓕.p J) x * k) := by
    intro n k
    rw [(𝓕.commute_positiveSplitComponent_levi J ⟨x, hx⟩ n).eq, mul_assoc]
  simp_rw [hcomm]
  have hc := continuous_slice_integrand 𝓕 J θ hθΓ hθ
    (fun k : K => map F (𝓕.P J) G (𝓕.p J) x * (k : AdelicGroupPoints F G))
    (continuous_const.mul continuous_subtype_val)
  rw [squareIntegrablePairingMeasure, lintegral_prod _ hc.measurable.aemeasurable]
  rfl

end Slice

section Comparison

/-- `δ_P(q)`, the idele norm of `det(Ad(q) | Lie P)`, as an extended nonnegative real. -/
private def adjointNorm (q : AdelicGroupPoints F (𝓕.P J)) : ℝ≥0∞ :=
  ((characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul q : ℝ≥0) : ℝ≥0∞)

private theorem adjointNorm_mul (q q' : AdelicGroupPoints F (𝓕.P J)) :
    𝓕.adjointNorm J (q * q') = 𝓕.adjointNorm J q * 𝓕.adjointNorm J q' := by
  simp only [adjointNorm, map_mul, Units.val_mul, ENNReal.coe_mul]

private theorem adjointNorm_one : 𝓕.adjointNorm J 1 = 1 := by
  simp only [adjointNorm, map_one, Units.val_one, ENNReal.coe_one]

private theorem adjointNorm_ne_top (q : AdelicGroupPoints F (𝓕.P J)) : 𝓕.adjointNorm J q ≠ ∞ :=
  ENNReal.coe_ne_top

private theorem adjointNorm_ne_zero (q : AdelicGroupPoints F (𝓕.P J)) : 𝓕.adjointNorm J q ≠ 0 := by
  unfold adjointNorm
  exact_mod_cast (Units.ne_zero _)

private theorem continuous_adjointNorm : Continuous (𝓕.adjointNorm J) :=
  ENNReal.continuous_coe.comp (Units.continuous_val.comp
    (characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul).continuous)

private theorem adjointNorm_eq_of_characterLog_eq {q q' : AdelicGroupPoints F (𝓕.P J)}
    (h : characterLog F (𝓕.P J) q = characterLog F (𝓕.P J) q') :
    𝓕.adjointNorm J q = 𝓕.adjointNorm J q' := by
  unfold adjointNorm
  rw [characterNorm_eq_of_characterLog_eq (𝓕.P J) _ h]

local notation "𝔦" => AdelicGroupPoints.map F (𝓕.P J) G (𝓕.p J)

variable [IsClosedImmersion (𝓕.p J).hom.hom.left] (K₁ K₂ : Subgroup (AdelicGroupPoints F G))
  (hK₁ : IsIwasawaCompact (𝓕.p J) K₁) (hK₂ : IsIwasawaCompact (𝓕.p J) K₂)

/-- **The comparison of pairing integrals.** There is `c > 0` such that for every continuous
left `U(𝔸) M(F)`-invariant `θ ≥ 0` vanishing off `{Δ = v}` and all `x, x' ∈ 𝔄_P` with
`H_P(x') = H_P(x) - v`, `δ_P(x') ∫_{K₁ × [M]^1} θ(x m k) = c δ_P(x) ∫_{K₂ × [M]^1} θ(x' m k)`. -/
private theorem exists_pairing_lintegral_comparison :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ θ : AdelicGroupPoints F G → ℝ≥0∞, Continuous θ →
        (∀ r₀ ∈ parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J), ∀ g, θ (r₀ * g) = θ g) →
        ∀ v : RealCharacterDual F (𝓕.P J), (∀ g, hK₁.height g - hK₂.height g ≠ v → θ g = 0) →
        ∀ x x' : AdelicGroupPoints F (𝓕.P J), x ∈ 𝓕.positiveSplitComponent J →
          x' ∈ 𝓕.positiveSplitComponent J →
          characterLog F (𝓕.P J) x' = characterLog F (𝓕.P J) x - v →
          𝓕.adjointNorm J x' * ∫⁻ z, θ (map F (𝓕.P J) G (𝓕.p J) x *
              map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
                ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
              (z.1 : AdelicGroupPoints F G)) ∂(𝓕.squareIntegrablePairingMeasure K₁ hK₁.isCompact J) =
            c * 𝓕.adjointNorm J x * ∫⁻ z, θ (map F (𝓕.P J) G (𝓕.p J) x' *
              map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
                ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
              (z.1 : AdelicGroupPoints F G)) ∂(𝓕.squareIntegrablePairingMeasure K₂ hK₂.isCompact J) := by
  obtain ⟨σ, hσ⟩ := exists_characterLog_section 𝓕 J
  have hsec : ∀ ℓ, characterLog F (𝓕.P J) (σ (Multiplicative.ofAdd ℓ)) = ℓ := fun ℓ => hσ _
  obtain ⟨c, hc, hA⟩ := CompactFactorization.exists_lintegral_compact_eq_of_modular
    (𝔦).toMonoidHom (isClosedEmbedding_map F (𝓕.P J) G (𝓕.p J)) K₁ K₂ hK₁.isCompact
    hK₂.isCompact hK₁.exists_eq hK₂.exists_eq (compactHaarProbability F G K₁ hK₁.isCompact)
    (compactHaarProbability F G K₂ hK₂.isCompact)
  refine ⟨c, hc, fun θ hθ hθΓ v hsupp x x' hx hx' hxx' => ?_⟩
  let a : AdelicGroupPoints F G → AdelicGroupPoints F (𝓕.P J) :=
    fun g => σ (Multiplicative.ofAdd (hK₁.height g))
  let Φ : AdelicGroupPoints F G → ℝ≥0∞ := fun g =>
    𝓕.adjointNorm J (a g) * 𝓕.leviSlice J θ (𝔦 (x * (a g)⁻¹) * g)
  have ha_cont : Continuous a := σ.continuous.comp (continuous_ofAdd.comp hK₁.continuous_height)
  have hΦm : Measurable Φ := by
    refine (((continuous_adjointNorm 𝓕 J).comp ha_cont).measurable).mul
      ((measurable_leviSlice 𝓕 J θ hθΓ hθ).comp ?_)
    exact (((𝔦).continuous.comp (continuous_const.mul ha_cont.inv)).mul continuous_id).measurable
  have hΦeq : ∀ (q : AdelicGroupPoints F (𝓕.P J)) (g : AdelicGroupPoints F G),
      Φ ((𝔦).toMonoidHom q * g) = (Measure.modularCharacter q : ℝ≥0∞) * Φ g := by
    intro q g
    change Φ (𝔦 q * g) = _
    have hh : hK₁.height (𝔦 q * g) = characterLog F (𝓕.P J) q + hK₁.height g :=
      hK₁.height_map_mul q g
    have ha : a (𝔦 q * g) = σ (Multiplicative.ofAdd (characterLog F (𝓕.P J) q)) * a g := by
      simp only [a, hh, ofAdd_add, map_mul]
    have hNa : 𝓕.adjointNorm J (σ (Multiplicative.ofAdd (characterLog F (𝓕.P J) q))) =
        𝓕.adjointNorm J q := adjointNorm_eq_of_characterLog_eq 𝓕 J (hsec _)
    have hy : x * (a (𝔦 q * g))⁻¹ * q * a g * x⁻¹ ∈ normOneSubgroup F (𝓕.P J) := by
      rw [← characterLog_eq_zero_iff]
      simp only [characterLog_mul, characterLog_inv', ha, hsec]
      abel
    have hslice : 𝓕.leviSlice J θ (𝔦 (x * (a (𝔦 q * g))⁻¹) * (𝔦 q * g)) =
        𝓕.leviSlice J θ (𝔦 (x * (a g)⁻¹) * g) := by
      rw [← leviSlice_normOne_mul 𝓕 J θ hθΓ hθ hy (𝔦 (x * (a g)⁻¹) * g)]
      congr 1
      simp only [← mul_assoc, ← map_mul]
      congr 2
      group
    have hmod : (Measure.modularCharacter q : ℝ≥0∞) = 𝓕.adjointNorm J q := by
      rw [modularCharacter_eq_adjointNorm]
      rfl
    change 𝓕.adjointNorm J (a (𝔦 q * g)) *
        𝓕.leviSlice J θ (𝔦 (x * (a (𝔦 q * g))⁻¹) * (𝔦 q * g)) = _
    rw [hslice, hmod, ha, adjointNorm_mul, hNa, mul_assoc]
  have key := hA Φ hΦm hΦeq
  have hK₁eval : ∀ k : K₁, Φ k = 𝓕.leviSlice J θ (𝔦 x * (k : AdelicGroupPoints F G)) := by
    intro k
    have h0 : hK₁.height k = 0 := hK₁.height_of_mem k.2
    simp only [Φ, a, h0, ofAdd_zero, map_one, inv_one, mul_one, adjointNorm_one, one_mul]
  have hK₂eval : ∀ k : K₂, Φ k = 𝓕.adjointNorm J (σ (Multiplicative.ofAdd v)) *
      𝓕.leviSlice J θ (𝔦 x' * (k : AdelicGroupPoints F G)) := by
    intro k
    have h20 : hK₂.height k = 0 := hK₂.height_of_mem k.2
    by_cases hΔ : hK₁.height k - hK₂.height k = v
    · have hv : hK₁.height k = v := by rw [h20, sub_zero] at hΔ; exact hΔ
      have hy : x * (σ (Multiplicative.ofAdd v))⁻¹ * x'⁻¹ ∈ normOneSubgroup F (𝓕.P J) := by
        rw [← characterLog_eq_zero_iff]
        simp only [characterLog_mul, characterLog_inv', hsec, hxx']
        abel
      simp only [Φ, a, hv]
      congr 1
      rw [← leviSlice_normOne_mul 𝓕 J θ hθΓ hθ hy (𝔦 x' * (k : AdelicGroupPoints F G)),
        ← mul_assoc, ← map_mul, inv_mul_cancel_right]
    · have hzero : ∀ w : AdelicGroupPoints F (𝓕.P J),
          𝓕.leviSlice J θ (𝔦 w * (k : AdelicGroupPoints F G)) = 0 := by
        intro w
        unfold leviSlice
        refine (lintegral_congr fun z => hsupp _ ?_).trans lintegral_zero
        rw [InducedInnerProductIntegrable.map_comp_apply, ← mul_assoc, ← map_mul,
          hK₁.height_map_mul, hK₂.height_map_mul, add_sub_add_left_eq_sub]
        exact hΔ
      simp only [Φ, hzero, mul_zero]
  rw [lintegral_pairing_eq_slice 𝓕 J θ hθΓ hθ K₁ hK₁.isCompact hx,
    lintegral_pairing_eq_slice 𝓕 J θ hθΓ hθ K₂ hK₂.isCompact hx']
  have e1 : ∫⁻ k, Φ k ∂(compactHaarProbability F G K₁ hK₁.isCompact) =
      ∫⁻ k, 𝓕.leviSlice J θ (𝔦 x * (k : AdelicGroupPoints F G))
        ∂(compactHaarProbability F G K₁ hK₁.isCompact) := lintegral_congr hK₁eval
  have e2 : ∫⁻ k, Φ k ∂(compactHaarProbability F G K₂ hK₂.isCompact) =
      𝓕.adjointNorm J (σ (Multiplicative.ofAdd v)) *
        ∫⁻ k, 𝓕.leviSlice J θ (𝔦 x' * (k : AdelicGroupPoints F G))
          ∂(compactHaarProbability F G K₂ hK₂.isCompact) := by
    rw [lintegral_congr hK₂eval, lintegral_const_mul' _ _ (adjointNorm_ne_top 𝓕 J _)]
  have hNx : 𝓕.adjointNorm J x = 𝓕.adjointNorm J x' * 𝓕.adjointNorm J (σ (Multiplicative.ofAdd v)) := by
    rw [← adjointNorm_mul]
    apply adjointNorm_eq_of_characterLog_eq
    rw [characterLog_mul, hsec, hxx', sub_add_cancel]
  change 𝓕.adjointNorm J x' * ∫⁻ k, 𝓕.leviSlice J θ (𝔦 x * (k : AdelicGroupPoints F G))
      ∂(compactHaarProbability F G K₁ hK₁.isCompact) = _
  rw [← e1, key, e2, hNx]
  ring

end Comparison

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InducedInnerProductIntegrable

/-- **The finite compact comparison** (Delorme 2023, (3.7); Mœglin–Waldspurger I.1.13): for two
maximal Iwasawa compacts with the same infinite projection, `Δ = H_P^{K₁} - H_P^{K₂}` has finite
range and clopen fibres, the cuts of `A^2_P(K₁)` lie in `A^2_P(K₂)`, and the pairings of the
cuts on `K₁` at `x` and on `K₂` at `x'` (with `H_P(x') = H_P(x) - v`) are integrable together
and agree after the factors `δ_P(x)⁻¹`, `δ_P(x')⁻¹` up to one positive constant. -/
theorem finiteCompactPairingComparison : FiniteCompactPairingComparisonStatement := by
  intro F _ _ G _ _ _ 𝓕 J _ K₁ K₂ hK₁ hK₂ hmax₁ hmax₂ hinf Δ cut Γ δinv
  have hopen : IsOpen {k : K₁ | k.val ∈ K₂} :=
    IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K₁ K₂ hmax₂ hinf
  have hfin : (Set.range Δ).Finite := hK₁.finite_range_height_sub hK₂ hopen
  obtain ⟨-, hclopen, -⟩ := hK₁.exists_parameterTwist_clopen_decomposition hK₂ hopen
  have hfiber : ∀ v, IsClopen {g | Δ g = v} := hclopen
  have hΔleft : ∀ (q : AdelicGroupPoints F (𝓕.P J)) (g : AdelicGroupPoints F G),
      Δ (map F (𝓕.P J) G (𝓕.p J) q * g) = Δ g := by
    intro q g
    simp only [Δ, hK₁.height_map_mul, hK₂.height_map_mul]
    abel
  have hParabolic : Γ ≤ (map F (𝓕.P J) G (𝓕.p J)).toMonoidHom.range := by
    apply sup_le
    · rintro _ ⟨u, rfl⟩
      exact ⟨map F (𝓕.U J) (𝓕.P J) (𝓕.iU J) u, (map_comp_apply_of_hom (𝓕.iU J) u).symm⟩
    · rintro _ ⟨m, rfl⟩
      exact ⟨map F (𝓕.M J) (𝓕.P J) (𝓕.l J) (rational F (𝓕.M J) m),
        (map_comp_apply_of_hom (𝓕.l J) (rational F (𝓕.M J) m)).symm⟩
  have hΔΓ : ∀ r ∈ Γ, ∀ g, Δ (r * g) = Δ g := by
    intro r hr g
    obtain ⟨q, rfl⟩ := hParabolic hr
    exact hΔleft q g
  have hcutΓ : ∀ (φ : AdelicGroupPoints F G → ℂ), IsLeftInvariantUnder F G Γ φ →
      ∀ v, ∀ r ∈ Γ, ∀ g, cut v φ (r * g) = cut v φ g := by
    intro φ hφ v r hr g
    by_cases hg : Δ g = v
    · have hg' : Δ (r * g) = v := by rw [hΔΓ r hr g, hg]
      change {g | Δ g = v}.indicator φ (r * g) = {g | Δ g = v}.indicator φ g
      rw [Set.indicator_of_mem (show r * g ∈ {g | Δ g = v} from hg'),
        Set.indicator_of_mem (show g ∈ {g | Δ g = v} from hg), hφ r hr g]
    · have hg' : Δ (r * g) ≠ v := by rw [hΔΓ r hr g]; exact hg
      change {g | Δ g = v}.indicator φ (r * g) = {g | Δ g = v}.indicator φ g
      rw [Set.indicator_of_notMem (show r * g ∉ {g | Δ g = v} from hg'),
        Set.indicator_of_notMem (show g ∉ {g | Δ g = v} from hg)]
  refine ⟨⟨hfin.toFinset, fun g => hfin.mem_toFinset.mpr ⟨g, rfl⟩⟩, hfiber, ?_, ?_⟩
  · -- the inducing forms
    intro N d rho hsmooth hcalc φ hφ v
    apply 𝓕.isSquareIntegrableInducedForm_of_compact_change J rho hsmooth hcalc hK₁
      hK₂.isCompact hmax₁ hmax₂ hinf
    obtain ⟨hAut, hEq, hInt⟩ := hφ
    refine ⟨?_, ?_, ?_⟩
    · let δf (b : FiniteAdelicGroupPoints F G) := Δ (ofFinite F G b)
      let L : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
        ⟨K₁.map (finite F G).toMonoidHom ⊓ K₂.map (finite F G).toMonoidHom,
          (IsMaximalCompactSubgroup.isOpen_finite F G K₁ hmax₁).inter
            (IsMaximalCompactSubgroup.isOpen_finite F G K₂ hmax₂)⟩
      have hΔ (g : AdelicGroupPoints F G) : Δ g = δf (finite F G g) := by
        simpa only [pair_projections] using hK₁.height_sub_pair_eq_of_infinite_eq hK₂ hmax₁ hmax₂
          hinf (infinite F G g) (finite F G g)
      have ofFinite_mem {C : Subgroup (AdelicGroupPoints F G)}
          (hC : IsMaximalCompactSubgroup F G C) {k : FiniteAdelicGroupPoints F G}
          (hk : k ∈ C.map (finite F G).toMonoidHom) : ofFinite F G k ∈ C := by
        rw [IsMaximalCompactSubgroup.eq_comap_prod F G C hC]
        change infinite F G (ofFinite F G k) ∈ C.map (infinite F G).toMonoidHom ∧
          finite F G (ofFinite F G k) ∈ C.map (finite F G).toMonoidHom
        rw [infinite_ofFinite, finite_ofFinite]
        exact ⟨one_mem _, hk⟩
      let T : Set (FiniteAdelicGroupPoints F G) := {b | δf b = v}
      have hT : IsClopen T := (hfiber v).preimage (ofFinite F G).continuous
      have hLeft (r : AdelicGroupPoints F G) (hr : r ∈ Γ) (g : AdelicGroupPoints F G) :
          finite F G (r * g) ∈ T ↔ finite F G g ∈ T := by
        change δf (finite F G (r * g)) = v ↔ δf (finite F G g) = v
        rw [← hΔ, ← hΔ, hΔΓ r hr g]
      have hRight (k : FiniteAdelicGroupPoints F G) (hk : k ∈ L)
          (b : FiniteAdelicGroupPoints F G) : b * k ∈ T ↔ b ∈ T := by
        have hk₁ := ofFinite_mem hmax₁ (show k ∈ K₁.map (finite F G).toMonoidHom from hk.1)
        have hk₂ := ofFinite_mem hmax₂ (show k ∈ K₂.map (finite F G).toMonoidHom from hk.2)
        change Δ (ofFinite F G (b * k)) = v ↔ Δ (ofFinite F G b) = v
        rw [map_mul]
        simp only [Δ]
        rw [hK₁.height_mul_right _ hk₁, hK₂.height_mul_right _ hk₂]
      convert hAut.indicator_finite T hT hLeft L hRight using 1
      funext g
      by_cases h : Δ g = v
      · have h' : finite F G g ∈ T := by
          change δf (finite F G g) = v
          rw [← hΔ]
          exact h
        rw [Set.indicator_of_mem (show g ∈ (finite F G) ⁻¹' T from h')]
        exact Set.indicator_of_mem (show g ∈ {g | Δ g = v} from h) φ
      · have h' : finite F G g ∉ T := by
          change ¬δf (finite F G g) = v
          rw [← hΔ]
          exact h
        rw [Set.indicator_of_notMem (show g ∉ (finite F G) ⁻¹' T from h')]
        exact Set.indicator_of_notMem (show g ∉ {g | Δ g = v} from h) φ
    · intro a ha g
      by_cases hg : Δ g = v
      · have hg' : Δ (map F (𝓕.P J) G (𝓕.p J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) a) * g) = v := by
          rw [hΔleft, hg]
        simp only [cut, Set.indicator_of_mem (show _ ∈ {g | Δ g = v} from hg'),
          Set.indicator_of_mem (show g ∈ {g | Δ g = v} from hg)]
        exact hEq a ha g
      · have hg' : Δ (map F (𝓕.P J) G (𝓕.p J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) a) * g) ≠ v := by
          rw [hΔleft]
          exact hg
        simp only [cut, Set.indicator_of_notMem (show _ ∉ {g | Δ g = v} from hg'),
          Set.indicator_of_notMem (show g ∉ {g | Δ g = v} from hg), mul_zero]
    · have hmeas : MeasurableSet {x : K₁ × RestrictionSplitCentre.CanonicalQuotient F (𝓕.M J) |
          Δ (x.1 : AdelicGroupPoints F G) = v} :=
        measurable_fst (((hfiber v).isClosed.preimage continuous_subtype_val).measurableSet)
      convert hInt.indicator hmeas using 1
      funext x
      by_cases hx : Δ (x.1 : AdelicGroupPoints F G) = v
      · have hx' : Δ (map F (𝓕.P J) G (𝓕.p J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) x.2.out) *
            (x.1 : AdelicGroupPoints F G)) = v := by rw [hΔleft, hx]
        rw [Set.indicator_of_mem (show x ∈ _ from hx)]
        simp only [cut, Set.indicator_of_mem (show _ ∈ {g | Δ g = v} from hx')]
      · have hx' : Δ (map F (𝓕.P J) G (𝓕.p J) (map F (𝓕.M J) (𝓕.P J) (𝓕.l J) x.2.out) *
            (x.1 : AdelicGroupPoints F G)) ≠ v := by rw [hΔleft]; exact hx
        rw [Set.indicator_of_notMem (show x ∉ _ from hx)]
        simp only [cut, Set.indicator_of_notMem (show _ ∉ {g | Δ g = v} from hx'), norm_zero,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  · -- the Levi pairings
    obtain ⟨c, hc, hC⟩ := 𝓕.exists_pairing_lintegral_comparison J K₁ K₂ hK₁ hK₂
    refine ⟨c, hc, fun φ ψ hφc hφΓ hψc hψΓ v x x' hx hx' hxx' => ?_⟩
    let Θ : AdelicGroupPoints F G → ℂ := fun g => cut v φ g * starRingEnd ℂ (ψ g)
    have hΘc : Continuous Θ :=
      ((hfiber v).continuous_indicator hφc).mul (Complex.continuous_conj.comp hψc)
    have hΘΓ : ∀ r ∈ Γ, ∀ g, Θ (r * g) = Θ g := by
      intro r hr g
      simp only [Θ, hcutΓ φ hφΓ v r hr g, hψΓ r hr g]
    have hΘsupp : ∀ g, Δ g ≠ v → Θ g = 0 := by
      intro g hg
      simp only [Θ, cut, Set.indicator_of_notMem (show g ∉ {g | Δ g = v} from hg), zero_mul]
    let e₁ : K₁ × NormOneRationalQuotient F (𝓕.M J) → AdelicGroupPoints F G := fun z =>
      map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          (z.1 : AdelicGroupPoints F G)
    let e₂ : K₂ × NormOneRationalQuotient F (𝓕.M J) → AdelicGroupPoints F G := fun z =>
      map F (𝓕.P J) G (𝓕.p J) x' * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
          (z.1 : AdelicGroupPoints F G)
    let μ₁ := 𝓕.squareIntegrablePairingMeasure K₁ hK₁.isCompact J
    let μ₂ := 𝓕.squareIntegrablePairingMeasure K₂ hK₂.isCompact J
    have hf₁ : 𝓕.squareIntegrablePairingIntegrand K₁ J x (cut v φ) ψ = fun z => Θ (e₁ z) := rfl
    have hf₂ : 𝓕.squareIntegrablePairingIntegrand K₂ J x' (cut v φ) ψ = fun z => Θ (e₂ z) := rfl
    have hcont₁ : Continuous (fun z => Θ (e₁ z)) :=
      𝓕.continuous_pairing_integrand J Θ hΘΓ hΘc K₁ hx
    have hcont₂ : Continuous (fun z => Θ (e₂ z)) :=
      𝓕.continuous_pairing_integrand J Θ hΘΓ hΘc K₂ hx'
    -- the norms
    let nx : ℝ := ((characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul x :
      ℝ≥0) : ℝ)
    let nx' : ℝ := ((characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul x' :
      ℝ≥0) : ℝ)
    have hnx : 0 < nx := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hnx' : 0 < nx' := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
    have hN : ∀ y, (𝓕.adjointNorm J y).toReal =
        ((characterNorm F (𝓕.P J) (Lie.adjointDeterminantCharacter (𝓕.P J)).toMul y : ℝ≥0) :
          ℝ) := fun y => rfl
    -- integrability
    have hfinite : ∀ θ : AdelicGroupPoints F G → ℝ≥0∞, Continuous θ →
        (∀ r ∈ Γ, ∀ g, θ (r * g) = θ g) → (∀ g, Δ g ≠ v → θ g = 0) →
        (∫⁻ z, θ (e₁ z) ∂μ₁ < ∞ ↔ ∫⁻ z, θ (e₂ z) ∂μ₂ < ∞) := by
      intro θ h1 h2 h3
      have h := hC θ h1 h2 v h3 x x' hx hx' hxx'
      have hlt : ∀ {a L : ℝ≥0∞}, a ≠ 0 → a ≠ ∞ → (a * L < ∞ ↔ L < ∞) := by
        intro a L ha0 hat
        constructor
        · intro hL
          by_contra hL'
          rw [not_lt, top_le_iff] at hL'
          rw [hL', ENNReal.mul_top ha0] at hL
          exact lt_irrefl _ hL
        · intro hL
          exact ENNReal.mul_lt_top hat.lt_top hL
      have hc0 : (c : ℝ≥0∞) * 𝓕.adjointNorm J x ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hc.ne') (𝓕.adjointNorm_ne_zero J x)
      have hct : (c : ℝ≥0∞) * 𝓕.adjointNorm J x ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (𝓕.adjointNorm_ne_top J x)
      rw [← hlt (𝓕.adjointNorm_ne_zero J x') (𝓕.adjointNorm_ne_top J x'), h, hlt hc0 hct]
    have hint : Integrable (fun z => Θ (e₁ z)) μ₁ ↔ Integrable (fun z => Θ (e₂ z)) μ₂ := by
      have hθ := hfinite (fun g => ‖Θ g‖ₑ) (continuous_enorm.comp hΘc)
        (fun r hr g => by simp only [hΘΓ r hr g])
        (fun g hg => by simp only [hΘsupp g hg, enorm_zero])
      constructor
      · intro h
        exact ⟨hcont₂.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).mpr
          (hθ.mp ((hasFiniteIntegral_iff_enorm).mp h.2))⟩
      · intro h
        exact ⟨hcont₁.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).mpr
          (hθ.mpr ((hasFiniteIntegral_iff_enorm).mp h.2))⟩
    -- the real comparison
    have hreal : ∀ θr : AdelicGroupPoints F G → ℝ, Continuous θr →
        (∀ r ∈ Γ, ∀ g, θr (r * g) = θr g) → (∀ g, Δ g ≠ v → θr g = 0) →
        Integrable (fun z => θr (e₁ z)) μ₁ → Integrable (fun z => θr (e₂ z)) μ₂ →
        nx' * ∫ z, θr (e₁ z) ∂μ₁ = c * nx * ∫ z, θr (e₂ z) ∂μ₂ := by
      intro θr h1 h2 h3 hi₁ hi₂
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₁,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi₂]
      have hp := hC (fun g => ENNReal.ofReal (θr g)) (ENNReal.continuous_ofReal.comp h1)
        (fun r hr g => by simp only [h2 r hr g]) v
        (fun g hg => by simp only [h3 g hg, ENNReal.ofReal_zero]) x x' hx hx' hxx'
      have hn := hC (fun g => ENNReal.ofReal (-θr g))
        (ENNReal.continuous_ofReal.comp h1.neg) (fun r hr g => by simp only [h2 r hr g]) v
        (fun g hg => by simp only [h3 g hg, neg_zero, ENNReal.ofReal_zero]) x x' hx hx' hxx'
      have hp' := congrArg ENNReal.toReal hp
      have hn' := congrArg ENNReal.toReal hn
      simp only [ENNReal.toReal_mul, hN, ENNReal.coe_toReal] at hp' hn'
      rw [mul_sub, mul_sub, hp', hn']
    rw [hf₁, hf₂]
    refine ⟨hint, ?_⟩
    by_cases hI₁ : Integrable (fun z => Θ (e₁ z)) μ₁
    · have hI₂ : Integrable (fun z => Θ (e₂ z)) μ₂ := hint.mp hI₁
      have hre := hreal (fun g => (Θ g).re) (Complex.continuous_re.comp hΘc)
        (fun r hr g => by simp only [hΘΓ r hr g])
        (fun g hg => by simp only [hΘsupp g hg, Complex.zero_re]) hI₁.re hI₂.re
      have him := hreal (fun g => (Θ g).im) (Complex.continuous_im.comp hΘc)
        (fun r hr g => by simp only [hΘΓ r hr g])
        (fun g hg => by simp only [hΘsupp g hg, Complex.zero_im]) hI₁.im hI₂.im
      have hI : (nx' : ℂ) * ∫ z, Θ (e₁ z) ∂μ₁ = ((c : ℝ) * nx : ℝ) * ∫ z, Θ (e₂ z) ∂μ₂ := by
        apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          rw [show (∫ z, Θ (e₁ z) ∂μ₁).re = ∫ z, (Θ (e₁ z)).re ∂μ₁ from (integral_re hI₁).symm,
            show (∫ z, Θ (e₂ z) ∂μ₂).re = ∫ z, (Θ (e₂ z)).re ∂μ₂ from (integral_re hI₂).symm]
          exact hre
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          rw [show (∫ z, Θ (e₁ z) ∂μ₁).im = ∫ z, (Θ (e₁ z)).im ∂μ₁ from (integral_im hI₁).symm,
            show (∫ z, Θ (e₂ z) ∂μ₂).im = ∫ z, (Θ (e₂ z)).im ∂μ₂ from (integral_im hI₂).symm]
          exact him
      simp only [δinv, IwasawaCompatibleMeasure.parameterPower_neg_modulusParameter]
      change ((nx : ℂ))⁻¹ * _ = (c : ℂ) * (((nx' : ℂ))⁻¹ * _)
      have hnx0 : (nx : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
      have hnx0' : (nx' : ℂ) ≠ 0 := by exact_mod_cast hnx'.ne'
      field_simp
      push_cast at hI
      linear_combination hI
    · have hI₂ : ¬Integrable (fun z => Θ (e₂ z)) μ₂ := fun h => hI₁ (hint.mpr h)
      rw [integral_undef hI₁, integral_undef hI₂, mul_zero, mul_zero, mul_zero]

end Langlands.Global
