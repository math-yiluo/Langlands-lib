import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitLaurentSmoothness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology

/-! # Continuity of `f ↦ ψ_f[O, P]` (Waldspurger, Proposition VII.1.3)

Waldspurger, Proposition VII.1.3 (printed p. 316): for `f ∈ C(G)`, `ψ_f[O, P] ∈ C^∞(O, P)`, and
the map `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]`, is continuous. `FourierOrbitSmoothness` proves the
first assertion; this module proves the second for the topology of `C(G)` of III.6
(`HarishChandraSchwartz.Basic`) and the topology of `C^∞(O, P)` of VI.3 (`OrbitSectionTopology`):
`fourierOrbitSectionCLM` is `f ↦ ψ_f[O, P]` as a continuous linear map, and
`fourierOrbitLaurentSectionCLM` is the same map for Laurent coordinates.

The proof follows the source. For `M = G`, the twisted coefficients of `f` along a fixed level
`C_{K'}` are finite combinations, with coefficients independent of `f`, of the functions
`z ↦ ∫ f(g) ⟨ω(g) v, v̌⟩ χ_z(g) dg`, whose derivatives satisfy Waldspurger's estimate (2)
(`exists_norm_torusPartialDerivList_twistTensorEquiv_coefficientFourierTransform_le`). The general
case reduces to `M` by Lemma VII.1.2 and the continuity of `f ↦ f^{(P),Ind}(k₁, k₂)`: a linear
form on the compact picture `L_K` is, on the elements right invariant under `H × H`, a finite
combination of linear forms of the values at representatives of `(K × K)/(H × H)`
(`exists_norm_torusPartialDerivList_fourierOrbitSection_le`). Continuity on each level
`C_H → C^∞(O, P)^{(H ∩ K) × (H ∩ K)}` then follows from the seminorm bounds, and the universal
property of the inductive limit `C(G)` (III.6 (1)) gives the continuous linear map.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open Langlands.HarmonicAnalysis.TorusFourier
open scoped ComplexConjugate NNReal ENNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe u v

section LevelBound

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, v} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  {J : Type*} [Fintype J] [DecidableEq J] {n : G → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h)
  {K₀ : CompactOpenSubgroup G} (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n)
  {C : ℝ} (hnσ : ∀ g, ‖n g‖ ≤ C * (1 + σ g))

include hnm hnσ in
/-- **Waldspurger's estimate behind Proposition VII.1.3 for `M = G`, uniformly on a level**: for
a compact open subgroup `K'`, a linear form `λ` on `A ⊗ Ã` and a list `l` of torus directions,
there are `s` and `c` with `sup_z |∂_l (z ↦ λ(π(f χ_z)))(z)| ≤ c ν_s(f)` for every `f ∈ C(G)`
bi-invariant under `K'`. -/
theorem exists_norm_torusPartialDerivList_schwartzActionTensor_twist_le
    (K' : CompactOpenSubgroup G) (lam : Module.Dual ℂ (CoefficientTensor A)) (l : List J) :
    ∃ s c : ℝ, ∀ f : Space Ξ σ, IsBiInvariant K'.toSubgroup f → ∀ z : J → Circle,
      ‖torusPartialDerivList l
          (fun y => lam (schwartzActionTensor A hw hA hT (Space.twist hn hK₀ y f))) z‖ ≤
        c * (nu Ξ σ s f).toReal := by
  let K := K'.inf K₀
  have : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) := hA.2 K.1
  let b := Module.finBasis ℂ (fixedVectors A.representation K.toSubgroup)
  let ι := Fin (Module.finrank ℂ (fixedVectors A.representation K.toSubgroup))
  let ℓ : ι → SmoothDual A.representation := fun i =>
    fixedFunctional A.representation hA.1 K (b.coord i)
  let Φ : ι → ι → Space Ξ σ →ₗ[ℂ] smoothFiniteTorusFunctions J := fun i j =>
    twistedCoefficientFamily hw hnm hnσ (continuous_coefficient hA.1 (b i) (ℓ j))
      (exists_nu_coefficient_ne_top hw hT (b i) (ℓ j)).choose_spec
  have hΦ : ∀ i j, ∃ s c' : ℝ, ∀ (f : Space Ξ σ) (z : J → Circle),
      ‖torusPartialDerivList l (Φ i j f) z‖ ≤ c' * (nu Ξ σ s f).toReal := fun i j =>
    exists_norm_torusPartialDerivList_twistedCoefficientFamily_le hw hnm hnσ
      (continuous_coefficient hA.1 (b i) (ℓ j))
      (exists_nu_coefficient_ne_top hw hT (b i) (ℓ j)).choose_spec l
  choose s c' hsc using hΦ
  let a : ι → ι → ℂ := fun i j => lam ((b j : A) ⊗ₜ[ℂ] ℓ i)
  refine ⟨∑ i, ∑ j, |s i j|, ∑ i, ∑ j, ‖a i j‖ * |c' i j|, fun f hf z => ?_⟩
  have hK : ∀ y, IsBiInvariant K.toSubgroup (Space.twist hn hK₀ y f : G → ℂ) := fun y =>
    (hf.mono (CompactOpenSubgroup.inf_le_left K' K₀)).twistedFunction hn
      (fun k hk => hK₀ k (CompactOpenSubgroup.inf_le_right K' K₀ hk)) y
  let F : smoothFiniteTorusFunctions J := ∑ i, ∑ j, a i j • Φ i j f
  have hF : (fun y => lam (schwartzActionTensor A hw hA hT (Space.twist hn hK₀ y f))) =
      (F : (J → Circle) → ℂ) := by
    funext y
    rw [schwartzActionTensor_eq_sum A hw hA hT b (hK y)]
    simp only [map_sum, map_smul, smul_eq_mul, F, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smoothDual_schwartzAction_twist A hw hA hT hn hK₀ hnm hnσ, mul_comm]
    rfl
  have hD : torusPartialDerivList l (F : (J → Circle) → ℂ) =
      fun y => ∑ i, ∑ j, a i j * torusPartialDerivList l (Φ i j f) y := by
    rw [← torusPartialDerivListLinear_apply]
    simp only [F, map_sum, map_smul, AddSubmonoidClass.coe_finsetSum]
    funext y
    simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      torusPartialDerivListLinear_apply]
  rw [hF, hD]
  have hσ0 := hw.nonneg
  have hmono : ∀ i j, (nu Ξ σ (s i j) f).toReal ≤ (nu Ξ σ (∑ i, ∑ j, |s i j|) f).toReal :=
    fun i j => by
      refine ENNReal.toReal_mono (Space.nu_ne_top f _) (nu_mono hσ0 ?_ _)
      calc s i j ≤ |s i j| := le_abs_self _
        _ ≤ ∑ j', |s i j'| :=
          Finset.single_le_sum (f := fun j' => |s i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', |s i' j'| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |s i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  calc ‖∑ i, ∑ j, a i j * torusPartialDerivList l (Φ i j f) z‖
      ≤ ∑ i, ∑ j, ‖a i j * torusPartialDerivList l (Φ i j f) z‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖a i j‖ * |c' i j| * (nu Ξ σ (∑ i, ∑ j, |s i j|) f).toReal := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖torusPartialDerivList l (Φ i j f) z‖ ≤ c' i j * (nu Ξ σ (s i j) f).toReal :=
              hsc i j f z
          _ ≤ |c' i j| * (nu Ξ σ (s i j) f).toReal :=
              mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
          _ ≤ |c' i j| * (nu Ξ σ (∑ i, ∑ j, |s i j|) f).toReal :=
              mul_le_mul_of_nonneg_left (hmono i j) (abs_nonneg _)
    _ = (∑ i, ∑ j, ‖a i j‖ * |c' i j|) * (nu Ξ σ (∑ i, ∑ j, |s i j|) f).toReal := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

variable (χ : (J → Circle) → G →* ℂˣ) (hχ : ∀ z, IsOpen ((χ z).ker : Set G))
  (hχn : ∀ z g, ((χ z g : ℂˣ) : ℂ) = torusCharacter (n g) z)
  (hA' : ∀ z, IsAdmissible (A.twist (χ z) (hχ z)).representation)
  (hT' : ∀ z, HasTemperedCoefficients Ξ σ (A.twist (χ z) (hχ z)).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hA hT hn hK₀ hnm hnσ hχn in
/-- **Proposition VII.1.3 for `M = G`, continuity in seminorm form on a level**: with the twist
removed from the dual factor, the Fourier transforms `z ↦ (A ⊗ χ_z)^(d)(f)` satisfy
`sup_z |∂_l (z ↦ λ((A ⊗ χ_z)^(d)(f)))(z)| ≤ c ν_s(f)` for every `f ∈ C(G)` bi-invariant under
a fixed compact open subgroup `K'`. -/
theorem exists_norm_torusPartialDerivList_twistTensorEquiv_coefficientFourierTransform_le
    (K' : CompactOpenSubgroup G) (lam : Module.Dual ℂ (CoefficientTensor A)) (d : ℝ)
    (l : List J) :
    ∃ s c : ℝ, ∀ f : Space Ξ σ, IsBiInvariant K'.toSubgroup f → ∀ z : J → Circle,
      ‖torusPartialDerivList l
          (fun y => lam (twistTensorEquiv A (χ y) (hχ y)
            (coefficientFourierTransform (A.twist (χ y) (hχ y)) hw (hA' y) (hT' y) hΞ hσ d f)))
          z‖ ≤
        c * (nu Ξ σ s f).toReal := by
  obtain ⟨s, c, hc⟩ := exists_norm_torusPartialDerivList_schwartzActionTensor_twist_le A hw hA
    hT hn hK₀ hnm hnσ K' ((d : ℂ) • lam) l
  refine ⟨s, c, fun f hf z => ?_⟩
  have heq : (fun y => lam (twistTensorEquiv A (χ y) (hχ y)
      (coefficientFourierTransform (A.twist (χ y) (hχ y)) hw (hA' y) (hT' y) hΞ hσ d f))) =
      fun y => ((d : ℂ) • lam) (schwartzActionTensor A hw hA hT
        (Space.twist hn hK₀ y (Space.check hΞ hσ f))) := by
    funext y
    rw [coefficientFourierTransform_apply, map_smul,
      twistTensorEquiv_schwartzActionTensor A hw hA hT (χ y) (hχ y) (hA' y) (hT' y) hn hK₀ y
        (hχn y), map_smul, LinearMap.smul_apply]
  rw [heq]
  have h := hc (Space.check hΞ hσ f) (by exact IsBiInvariant.check hf) z
  rwa [show nu Ξ σ s (Space.check hΞ hσ f) = nu Ξ σ s f from nu_check hΞ hσ s f] at h

end LevelBound

section ConstantTermBounds

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)] {M U : Subgroup G}
  {νU : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}
  (hD : ConstantTermData νU δ) (hE : ConstantTermEstimate νU δ Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

/-- If `f` is bi-invariant under `H`, then `f^{(P),Ind}(g₁, g₂)` is bi-invariant under
`(g₁ H g₁⁻¹ ∩ g₂ H g₂⁻¹) ∩ M`, a compact open subgroup of `M` independent of `f`. -/
theorem Space.isBiInvariant_constantTermInd (H : CompactOpenSubgroup G) {f : Space Ξ σ}
    (hf : IsBiInvariant H.toSubgroup f) (g : G × G) :
    IsBiInvariant ((H.translate g.1 g.2).subgroupOf hD.isClosed).toSubgroup
      (Space.constantTermInd hD hE ht htM f g) :=
  hD.isBiInvariant (Space.continuous (Space.translate ht g.1 g.2 f)) (hf.translate g.1 g.2)

/-- Continuity of `f ↦ f^{(P),Ind}(g₁, g₂)`, `C(G) → C(M)`, in seminorm form:
`ν^M_s(f^{(P),Ind}(g₁, g₂)) ≤ c ν_{s'}(f)`. -/
theorem Space.exists_nu_constantTermInd_le (g : G × G) (s : ℝ) :
    ∃ s' c : ℝ, 0 ≤ c ∧ ∀ f : Space Ξ σ,
      (nu ΞM σM s (Space.constantTermInd hD hE ht htM f g)).toReal ≤
        c * (nu Ξ σ s' f).toReal := by
  obtain ⟨d', c₁, hc₁⟩ := hE.nu_le ht.pos ht.nonneg htM.pos htM.nonneg s
  obtain ⟨d, hd⟩ := ht.nu_translate_le g.1 g.2
  obtain ⟨c₂, hc₂0, hc₂⟩ := hd d'
  refine ⟨d' + d, c₁ * c₂, mul_nonneg c₁.2 hc₂0, fun f => ?_⟩
  have h1 := hc₁ (Space.translate ht g.1 g.2 f) (Space.nu_ne_top _ _)
  have h2 := hc₂ f
  calc (nu ΞM σM s (Space.constantTermInd hD hE ht htM f g)).toReal
      ≤ ((c₁ : ℝ≥0∞) * (ENNReal.ofReal c₂ * nu Ξ σ (d' + d) f)).toReal := by
        refine ENNReal.toReal_mono ?_ (h1.trans (mul_le_mul_of_nonneg_left h2 zero_le))
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Space.nu_ne_top f _))
    _ = c₁ * c₂ * (nu Ξ σ (d' + d) f).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂0,
          ENNReal.coe_toReal, mul_assoc]

end ConstantTermBounds

section Orbit

universe uG uV uI uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : ∀ A : UnitaryOrbitRepresentative ν π,
    IsSquareIntegrableModCentralSubgroup C hC A.val.obj.representation μM)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **`ψ_f[O, P]` is fixed by `H × H` when `f` is bi-invariant under `H`**: by Lemma VII.1.1 (i),
`(π(x₁) ⊗ π̌(x₂)) f̂(ω, P) = (ρ(x₁)λ(x₂)f)^(ω, P) = f̂(ω, P)` at every representative `ω`. -/
theorem productInducedOrbitRepresentation_fourierOrbitSection (ht : TranslationWeights Ξ σ)
    {H : Subgroup G} {f : Space Ξ σ} (hf : IsBiInvariant H f) (x : G × G) (hx₁ : x.1 ∈ H)
    (hx₂ : x.2 ∈ H) :
    productInducedOrbitRepresentation h hU ν π x
        (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f) =
      fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f := by
  funext A
  exact (inducedFourierTransform_translate h hU hP hm K hK hPK hG hδ A.val.obj hcof C hC μM
    (hsq A) A.val.property.1 hw (hT A) hΞ hσ ht x.1 x.2 f).symm.trans
    (congrArg (inducedFourierTransform h hU hP hm K hK hPK hG hδ A.val.obj hcof C hC μM (hsq A)
      A.val.property.1 hw (hT A) hΞ hσ)
      (Space.ext fun g => congrFun (hf.translate_eq hx₁ hx₂) g))


variable {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle)) (hνc : ∀ i, Continuous (ν i))
  (hPK' : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hsqπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
  (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] [MeasurableInv M]
  [μL.IsInvInvariant] [SFinite μL] {ΞM σM : M → ℝ} (hwM : L2Weights μL ΞM σM)
  (hTπ : HasTemperedCoefficients ΞM σM π.obj.representation)
  (hTM : ∀ A : UnitaryOrbitRepresentative ν π,
    HasTemperedCoefficients ΞM σM A.val.obj.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
  {νU : Measure U} [νU.IsMulLeftInvariant] [νU.IsMulRightInvariant] [SFinite νU]
  (hD : ConstantTermData νU (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hνU : IsConjModulus h.levi_le_normalizer νU
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate νU
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)
  (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
  (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : νU {u : U | (u : G) ∈ K} = 1)
  {n : M → J → ℤ} (hn : ∀ g h, n (g * h) = n g + n h) {K₀ : CompactOpenSubgroup M}
  (hK₀ : ∀ k ∈ K₀.toSubgroup, n k = 0) (hnm : Measurable n) {Cn : ℝ}
  (hnσ : ∀ m, ‖n m‖ ≤ Cn * (1 + σM m))
  (hne : ∀ z m, (((unitaryTorusParameter ν e z).val m : ℂˣ) : ℂ) = torusCharacter (n m) z)
  (hint : ∀ (f : Space Ξ σ) (A : UnitaryOrbitRepresentative ν π)
    (ψ : productInducedCoefficientObject h hU A.val.obj),
    Integrable
      (fun x : G × K => conj (CompactInduction.integrand h hU A.val.obj K x.1 ψ x.2) * f x.1)
      (μ.prod (CompactInduction.measure K hK)))

omit [DecidableEq J] in
/-- For `f ∈ C(G)` bi-invariant under `H`, `ψ_f[O, P]` lies in the level
`C^∞(O, P)^{H×H}`. -/
theorem fourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule (H : OpenSubgroup G)
    {f : Space Ξ σ} (hf : IsBiInvariant H.toSubgroup f) :
    (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
        hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne
        hint f).val ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hνc hm hPK' H :=
  ⟨(fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
      hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne
      hint f).property, fun x =>
    productInducedOrbitRepresentation_fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C
      hC μM hsq hw hT hΞ hσ ht hf x.val x.property.1 x.property.2⟩

set_option maxHeartbeats 2000000 in
/-- **The key estimate of Proposition VII.1.3**: for a compact open subgroup `H` of `G`, a list
`l` of torus directions and a linear form `ℓ` on the compact picture `L_K`, there are `s` and `c`
with `sup_z |∂_l (ℓ ∘ R ψ_f[O, P])(z)| ≤ c ν_s(f)` for every `f ∈ C(G)` bi-invariant under
`H`. -/
theorem exists_norm_torusPartialDerivList_fourierOrbitSection_le (H : CompactOpenSubgroup G)
    (l : List J) (ℓ : Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)) :
    ∃ s c : ℝ, ∀ f : Space Ξ σ, IsBiInvariant H.toSubgroup f → ∀ z : J → Circle,
      ‖torusPartialDerivList l (fun y => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K
          hP hK hνc hm hPK' e (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C
          hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw
          hMK hUK hn hK₀ hnm hnσ hne hint f) y)) z‖ ≤
        c * (nu Ξ σ s f).toReal := by
  classical
  have : IsTopologicalGroup (K.prod K) :=
    inferInstanceAs (IsTopologicalGroup (K.prod K).toSubgroup)
  have : CompactSpace (K.prod K) := isCompact_iff_compactSpace.mp (by
    rw [OpenSubgroup.coe_prod]
    exact hK.prod hK)
  let Lo : OpenSubgroup (K.prod K) :=
    (H.1.prod H.1).comap (K.prod K).toSubgroup.subtype continuous_subtype_val
  let Q := (K.prod K) ⧸ Lo.toSubgroup
  have : Fintype Q := Fintype.ofFinite Q
  let χ : (J → Circle) → M →* ℂˣ := fun z => (unitaryTorusParameter ν e z).val.toMonoidHom
  let hχ : ∀ z, IsOpen ((χ z).ker : Set M) := fun z =>
    unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)
  let Rp : (J → Circle) → UnitaryOrbitRepresentative ν π :=
    unitaryOrbitParameterRepresentative ν π e
  let dπ := representationFormalDegree C hC μM hcof hsqπ π.property.1
  have hdeg : ∀ z, representationFormalDegree C hC μM hcof (hsq (Rp z)) (Rp z).val.property.1 =
      dπ := fun z =>
    representationFormalDegree_unitaryTwist C hC μM hcof (χ z) (hχ z)
      (fun m => by
        change ‖((χ z m : ℂˣ) : ℂ)‖ = 1
        rw [show ((χ z m : ℂˣ) : ℂ) = torusCharacter (n m) z from hne z m,
          norm_torusCharacter]) hsqπ π.property.1
  let E := LinearMap.pi fun k : K.prod K =>
    Induction.FiniteProductTensorBijective.evalLinear (k := ℂ)
      ((P.prod P).comap (K.prod K).toSubgroup.subtype)
      (compactPictureInducingRepresentation (h.prod h) (K.prod K)
        (productLeviObject π.obj π.obj.contragredient)) k
  have hEinj : Function.Injective E := fun F₁ F₂ h₁₂ =>
    Induction.FiniteProductTensorBijective.smoothFunctions_ext _ _ fun k => congrFun h₁₂ k
  have hval : ∀ (f : Space Ξ σ) (z : J → Circle) (k : K.prod K),
      E (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hνc hm hPK' e
          (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ
          hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm
          hnσ hne hint f) z) k =
        twistTensorEquiv π.obj (χ z) (hχ z)
          (coefficientFourierTransform (π.obj.twist (χ z) (hχ z)) hwM (hsq (Rp z)).1
            (hTM (Rp z)) hΞM hσM dπ (Space.constantTermInd hD hE ht htM f (k : G × G))) :=
    fun f z k => by
      refine (productInducedFamilyRestriction_eval ν e h K hP hK hνc hm hU hPK' π.obj
        (productInducedOrbitPullback ν π e h hU (fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π
            hcof C hC μM hsq hw hT hΞ hσ f)) z k).trans ?_
      refine (congrArg (productCompactTwistTensorEquiv ν (unitaryTorusParameter ν e z) π.obj)
        (eval_inducedFourierTransform h hU hP hm K hK hPK hG hδ (Rp z).val.obj hcof C hC μM
          (hsq (Rp z)) (Rp z).val.property.1 hw (hT (Rp z)) hΞ hσ hδU hwM (hTM (Rp z)) hΞM hσM
          hD hνU hE ht htM hμK hPKiw hMK hUK f (hint f (Rp z)) (k : G × G))).trans ?_
      rw [hdeg z]
      rfl
  -- the compact-picture elements that are right invariant under `Lo`
  let W : Submodule ℂ (ProductInducedCompactPicture h K π.obj) :=
    { carrier := {F | ∀ (k : K.prod K) (x : Lo.toSubgroup), E F (k * x) = E F k}
      add_mem' := fun {F₁ F₂} h₁ h₂ k x => by
        simp only [map_add, Pi.add_apply]
        rw [h₁ k x, h₂ k x]
      zero_mem' := fun k x => by simp only [map_zero, Pi.zero_apply]
      smul_mem' := fun c F hF k x => by
        simp only [map_smul, Pi.smul_apply]
        rw [hF k x] }
  let Φ := LinearMap.pi fun q : Q => (LinearMap.proj (Quotient.out q) ∘ₗ E) ∘ₗ W.subtype
  have hΦ : Function.Injective Φ := by
    intro F₁ F₂ h₁₂
    apply Subtype.ext
    apply hEinj
    funext k
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul Lo.toSubgroup k
    have h₃ := congrFun h₁₂ (QuotientGroup.mk k : Q)
    change E F₁.1 (QuotientGroup.mk k : Q).out = E F₂.1 (QuotientGroup.mk k : Q).out at h₃
    rw [hx, F₁.2 k x, F₂.2 k x] at h₃
    exact h₃
  obtain ⟨Ψ, hΨ⟩ := Φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hΦ)
  let lam : Q → Module.Dual ℂ (CoefficientTensor π.obj) := fun q =>
    ℓ ∘ₗ W.subtype ∘ₗ Ψ ∘ₗ LinearMap.single ℂ (fun _ : Q => CoefficientTensor π.obj) q
  have hdecomp : ∀ F : W, ℓ (F : ProductInducedCompactPicture h K π.obj) =
      ∑ q, lam q (E (F : ProductInducedCompactPicture h K π.obj) (Quotient.out q)) := by
    intro F
    have h₁ : (F : ProductInducedCompactPicture h K π.obj) = W.subtype (Ψ (Φ F)) := by
      rw [← LinearMap.comp_apply Ψ Φ, hΨ]
      rfl
    calc ℓ (F : ProductInducedCompactPicture h K π.obj) =
          ℓ (W.subtype (Ψ (∑ q, Pi.single q (Φ F q)))) := by
          rw [Finset.univ_sum_single (Φ F), ← h₁]
      _ = ∑ q, lam q (E (F : ProductInducedCompactPicture h K π.obj) (Quotient.out q)) := by
          rw [map_sum, map_sum, map_sum]
          rfl
  have hmem : ∀ f : Space Ξ σ, IsBiInvariant H.toSubgroup f → ∀ z,
      productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hνc hm hPK' e
          (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ
          hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm
          hnσ hne hint f) z ∈ W := by
    intro f hf z k x
    have hl : (((x : K.prod K) : G × G)) ∈
        ((H.1.prod H.1 : OpenSubgroup (G × G)) : Set (G × G)) := x.2
    rw [OpenSubgroup.coe_prod] at hl
    rw [hval, hval]
    congr 2
    exact Space.constantTermInd_mul_of_isBiInvariant hD hE ht htM f hf hl.1 hl.2 (k : G × G)
  -- the bound on `M` for each coset representative
  let Kq : Q → CompactOpenSubgroup M := fun q =>
    (H.translate ((Quotient.out q : K.prod K) : G × G).1
      ((Quotient.out q : K.prod K) : G × G).2).subgroupOf hD.isClosed
  have hAq := fun q : Q =>
    exists_norm_torusPartialDerivList_twistTensorEquiv_coefficientFourierTransform_le π.obj hwM
      hsqπ.1 hTπ hn hK₀ hnm hnσ χ hχ (fun z m => hne z m) (fun z => (hsq (Rp z)).1)
      (fun z => hTM (Rp z)) hΞM hσM (Kq q) (lam q) dπ l
  choose sA cA hcA using hAq
  have hBq := fun q : Q =>
    Space.exists_nu_constantTermInd_le hD hE ht htM ((Quotient.out q : K.prod K) : G × G) (sA q)
  choose s' c' hc'0 hc' using hBq
  refine ⟨∑ q, |s' q|, ∑ q, |cA q| * c' q, fun f hf z => ?_⟩
  -- the summands are smooth torus functions
  let Fq : Q → (J → Circle) → ℂ := fun q y =>
    lam q (twistTensorEquiv π.obj (χ y) (hχ y)
      (coefficientFourierTransform (π.obj.twist (χ y) (hχ y)) hwM (hsq (Rp y)).1
        (hTM (Rp y)) hΞM hσM dπ
        (Space.constantTermInd hD hE ht htM f ((Quotient.out q : K.prod K) : G × G))))
  have hFq : ∀ q, IsSmoothFiniteTorusFunction (Fq q) := fun q =>
    isSmoothFiniteTorusFunction_of_mem_finiteSmoothFamilies
      (mem_finiteSmoothFamilies_linearMap
        (twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies π.obj hwM hsqπ.1
          hTπ hn hK₀ hnm hnσ χ hχ (fun z m => hne z m) (fun z => (hsq (Rp z)).1)
          (fun z => hTM (Rp z)) hΞM hσM dπ
          (Space.constantTermInd hD hE ht htM f ((Quotient.out q : K.prod K) : G × G)))
        (lam q))
  let S : smoothFiniteTorusFunctions J := ∑ q, ⟨Fq q, hFq q⟩
  have hS : (fun y => ℓ (productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hνc hm hPK' e
      (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
      hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne
      hint f) y)) = (S : (J → Circle) → ℂ) := by
    funext y
    rw [hdecomp ⟨_, hmem f hf y⟩]
    simp only [S, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hval]
  have hDS : torusPartialDerivList l (S : (J → Circle) → ℂ) =
      fun y => ∑ q, torusPartialDerivList l (Fq q) y := by
    rw [← torusPartialDerivListLinear_apply]
    simp only [S, map_sum, AddSubmonoidClass.coe_finsetSum]
    funext y
    simp only [Finset.sum_apply, torusPartialDerivListLinear_apply]
  rw [hS, hDS]
  have hσ0 := ht.nonneg
  have hmono : ∀ q, (nu Ξ σ (s' q) f).toReal ≤ (nu Ξ σ (∑ q, |s' q|) f).toReal := fun q => by
    refine ENNReal.toReal_mono (Space.nu_ne_top f _) (nu_mono hσ0 ?_ _)
    calc s' q ≤ |s' q| := le_abs_self _
      _ ≤ ∑ q', |s' q'| :=
        Finset.single_le_sum (f := fun q' => |s' q'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ q)
  calc ‖∑ q, torusPartialDerivList l (Fq q) z‖
      ≤ ∑ q, ‖torusPartialDerivList l (Fq q) z‖ := norm_sum_le _ _
    _ ≤ ∑ q, |cA q| * c' q * (nu Ξ σ (∑ q, |s' q|) f).toReal := by
        refine Finset.sum_le_sum fun q _ => ?_
        calc ‖torusPartialDerivList l (Fq q) z‖
            ≤ cA q * (nu ΞM σM (sA q) (Space.constantTermInd hD hE ht htM f
                ((Quotient.out q : K.prod K) : G × G))).toReal :=
              hcA q _ (Space.isBiInvariant_constantTermInd hD hE ht htM H hf _) z
          _ ≤ |cA q| * (nu ΞM σM (sA q) (Space.constantTermInd hD hE ht htM f
                ((Quotient.out q : K.prod K) : G × G))).toReal :=
              mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
          _ ≤ |cA q| * (c' q * (nu Ξ σ (s' q) f).toReal) :=
              mul_le_mul_of_nonneg_left (hc' q f) (abs_nonneg _)
          _ ≤ |cA q| * (c' q * (nu Ξ σ (∑ q, |s' q|) f).toReal) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hmono q) (hc'0 q)) (abs_nonneg _)
          _ = |cA q| * c' q * (nu Ξ σ (∑ q, |s' q|) f).toReal := (mul_assoc _ _ _).symm
    _ = (∑ q, |cA q| * c' q) * (nu Ξ σ (∑ q, |s' q|) f).toReal := (Finset.sum_mul _ _ _).symm

omit [DecidableEq J] in
/-- The restriction of `f ↦ ψ_f[O, P]` to the level `C_H` of `C(G)`, with values in the level
`C^∞(O, P)^{(H ∩ K) × (H ∩ K)}`. -/
def fourierOrbitSectionLevelLinear (H : CompactOpenSubgroup G) :
    Level Ξ σ H →ₗ[ℂ] OrbitSectionLevel ν π e h hU K hP hK hνc hm hPK' (H.1 ⊓ K) :=
  LinearMap.codRestrict (orbitSectionLevelSubmodule ν π e h hU K hP hK hνc hm hPK' (H.1 ⊓ K))
    ((productInducedSmoothOrbitSections ν π e h hU K hP hK hνc hm hPK').subtype ∘ₗ
        fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
        e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ
        hne hint ∘ₗ Space.ofLevel H)
    fun f => orbitSectionLevelSubmodule_antitone ν π e h hU K hP hK hνc hm hPK' inf_le_left
      (fourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule h hU hP hm K hK hPK hG hδ ν π
          hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM
          hPKiw hMK hUK hn hK₀ hnm hnσ hne hint H.1
        (Level.isBiInvariant f))

omit [DecidableEq J] in
theorem toSections_fourierOrbitSectionLevelLinear (H : CompactOpenSubgroup G)
    (f : Level Ξ σ H) :
    OrbitSectionLevel.toSections ν π e h hU K hP hK hνc hm hPK' (H.1 ⊓ K)
        (fourierOrbitSectionLevelLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ
        e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ
        hne hint H f) =
      fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
          hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ
          hne hint (Space.ofLevel H f) :=
  rfl

/-- **Proposition VII.1.3, continuity on a level**: `f ↦ ψ_f[O, P]` is continuous from the
level `C_H` of `C(G)` to the level `C^∞(O, P)^{(H ∩ K) × (H ∩ K)}`. -/
theorem continuous_fourierOrbitSectionLevelLinear (H : CompactOpenSubgroup G) :
    Continuous (fourierOrbitSectionLevelLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT
        hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm
        hnσ hne hint H) := by
  refine (Level.withSeminorms H).continuous_of_isBounded
    (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hνc hm hPK' (H.1 ⊓ K)) _ ?_
  refine Seminorm.IsBounded.of_real fun i => ?_
  obtain ⟨s, c, hc⟩ := exists_norm_torusPartialDerivList_fourierOrbitSection_le h hU hP hm K hK hPK
      hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE
      ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne hint H i.1 i.2
  refine ⟨{s}, max c 0, fun f => ?_⟩
  rw [Finset.sup_singleton]
  change orbitSectionSeminorm ν π e h hU K hP hK hνc hm hPK' (i.1, i.2)
      (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
      hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne
      hint (Space.ofLevel H f)) ≤
    max c 0 * (nu Ξ σ s f).toReal
  refine (orbitSectionSeminorm_le_iff ν π e h hU K hP hK hνc hm hPK' i.1 i.2 _
    (mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg)).mpr fun z => ?_
  exact (hc (Space.ofLevel H f) (Level.isBiInvariant f) z).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)

/-- **Waldspurger's map `C(G) → C^∞(O, P)`, `f ↦ ψ_f[O, P]`, as a continuous linear map**
(Proposition VII.1.3), for the topology of `C(G)` of III.6 and the topology of `C^∞(O, P)` of
VI.3. -/
def fourierOrbitSectionCLM : Space Ξ σ →L[ℂ] OrbitSectionSpace ν π e h hU K hP hK hνc hm hPK' :=
  Space.mkCLM (fourierOrbitSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT
      hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm
      hnσ hne hint : Space Ξ σ →ₗ[ℂ] OrbitSectionSpace ν π e h hU K hP hK hνc hm hPK') fun H =>
    (OrbitSectionSpace.continuous_ofLevel ν π e h hU K hP hK hνc hm hPK' ⟨H.1 ⊓ K,
        inf_le_right⟩).comp
      (continuous_fourierOrbitSectionLevelLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw
          hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn
          hK₀ hnm hnσ hne hint H)

/-- The continuous linear map is `f ↦ ψ_f[O, P]`. -/
theorem toSections_fourierOrbitSectionCLM (f : Space Ξ σ) :
    OrbitSectionSpace.toSections ν π e h hU K hP hK hνc hm hPK' (fourierOrbitSectionCLM h hU hP hm
        K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM
        hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne hint f) = fourierOrbitSmoothSectionLinear
        h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ
        hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne hint f :=
  rfl

theorem fourierOrbitSectionCLM_apply_val (f : Space Ξ σ) :
    (OrbitSectionSpace.toSections ν π e h hU K hP hK hνc hm hPK' (fourierOrbitSectionCLM h hU hP hm
        K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM
        hD hνU hE ht htM hPKiw hMK hUK hn hK₀ hnm hnσ hne hint f)).val =
      fourierOrbitSection h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ f :=
  rfl

/-- **Proposition VII.1.3 with Laurent coordinates**: when the torus coordinates `e` satisfy
`HasLaurentUnitaryCoordinates ν e`, the lattice map is `laurentExponent ν e he`, and only its
growth bound remains a hypothesis. -/
def fourierOrbitLaurentSectionCLM (he : HasLaurentUnitaryCoordinates ν e) {Cl : ℝ}
    (hlσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cl * (1 + σM m)) :
    Space Ξ σ →L[ℂ] OrbitSectionSpace ν π e h hU K hP hK hνc hm hPK' :=
  fourierOrbitSectionCLM h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e hνc hPK' hsqπ
      hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK
    (laurentExponent_mul ν e he) (K₀ := Classical.arbitrary (CompactOpenSubgroup M))
    (fun _ hk => laurentExponent_eq_zero_of_isCompact ν e he hνc
      (Classical.arbitrary (CompactOpenSubgroup M)).2 hk)
    (measurable_laurentExponent ν e he (isOpen_commonNormKernel_of_continuous ν hνc)) hlσ
    (fun z m => (torusCharacter_laurentExponent ν e he m z).symm) hint

theorem toSections_fourierOrbitLaurentSectionCLM (he : HasLaurentUnitaryCoordinates ν e)
    {Cl : ℝ} (hlσ : ∀ m, ‖laurentExponent ν e he m‖ ≤ Cl * (1 + σM m)) (f : Space Ξ σ) :
    OrbitSectionSpace.toSections ν π e h hU K hP hK hνc hm hPK'
        (fourierOrbitLaurentSectionCLM h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT hΞ hσ e
            hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK hint he hlσ f)
            =
      fourierOrbitLaurentSmoothSectionLinear h hU hP hm K hK hPK hG hδ ν π hcof C hC μM hsq hw hT
          hΞ hσ e hνc hPK' hsqπ hμK hδU hwM hTπ hTM hΞM hσM hD hνU hE ht htM hPKiw hMK hUK he hlσ
          hint f :=
  rfl

end Orbit

end Langlands.HarishChandraSchwartz
