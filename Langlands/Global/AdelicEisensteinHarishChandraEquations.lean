import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.AdelicInducedHarishChandraStatement
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicEisensteinCompactBounds

/-! # Harish-Chandra convolution equations for Eisenstein series (Bernstein–Lapid (8.2a))

Bernstein–Lapid §8.4 choose holomorphic families `(h_i(λ), c_i(λ))` with
`δ(h_i(λ)) E(φ, λ) = c_i(λ) E(φ, λ)` in the region of absolute convergence and, for every
`λ₀`, some `c_i(λ₀) ≠ 0` (equations (8.2a)). This module derives such families from the
uniform Harish-Chandra equations for the twists `φ_λ` (`InducedHarishChandraEquationsStatement`):
right convolution commutes with the absolutely convergent sum over `P(F) \ G(F)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- A scalar function that is complex differentiable on `ℂⁿ` is holomorphic on every open
subset `W`, in the sense used by `LocalFinitenessData.IsAdmissible`. -/
theorem isHolomorphicOn_opens_of_differentiable {n : ℕ} {W : TopologicalSpace.Opens (Fin n → ℂ)}
    {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s : W => f s) Set.univ := by
  intro mu
  have h1 : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) (fun s : Fin n → ℂ => mu (f s)) :=
    (mu.differentiable.comp hf).mdifferentiable
  have h2 : MDifferentiable 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) (Subtype.val : W → Fin n → ℂ) :=
    (contMDiff_subtype_val (n := 1)).mdifferentiable one_ne_zero
  exact (h1.comp h2).mdifferentiableOn

namespace AdelicGroupPoints

section Convolution

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The chosen representative in `G(F) ⊆ G(𝔸)` of a coset in `P(F) \ G(F)`. -/
abbrev parabolicCosetRep (p : P ⟶ G) (q : ParabolicRationalCosets F p) : AdelicGroupPoints F G :=
  ((Quotient.out q : rationalSubgroup F G) : AdelicGroupPoints F G)

/-- Right convolution with a continuous compactly supported `h` commutes with the sum over
`P(F) \ G(F)` defining the Eisenstein series, as soon as the terms `φ_λ(γ x g)` are dominated
by a summable function of `γ` for `g` in the support of `h`:
`δ(h) E(φ, λ)(x) = ∑_γ (δ(h) φ_λ)(γ x)`, and the right-hand side is summable. -/
theorem IsIwasawaCompact.rightConvolution_eisensteinSeries (hK : IsIwasawaCompact p K)
    {φ : AdelicGroupPoints F G → ℂ} (hφ : Continuous φ) (lam : ComplexCharacterParameter F P)
    {h : AdelicGroupPoints F G → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h)
    (x : AdelicGroupPoints F G) {B : ParabolicRationalCosets F p → ℝ} (hB : Summable B)
    (hbound : ∀ q, ∀ g ∈ tsupport h, ‖hK.eisensteinTerm φ lam (x * g) q‖ ≤ B q) :
    Summable (fun q => rightConvolution F G h (hK.parameterTwist φ lam)
        (parabolicCosetRep p q * x)) ∧
      rightConvolution F G h (hK.eisensteinSeries φ lam) x =
        ∑' q, rightConvolution F G h (hK.parameterTwist φ lam) (parabolicCosetRep p q * x) := by
  let mu : Measure (AdelicGroupPoints F G) := Measure.haar
  let Fc : ParabolicRationalCosets F p → AdelicGroupPoints F G → ℂ :=
    fun q g => h g * hK.eisensteinTerm φ lam (x * g) q
  have hcont : ∀ q, Continuous (Fc q) := fun q =>
    hh.mul ((hK.continuous_parameterTwist hφ lam).comp
      (continuous_const.mul (continuous_const.mul continuous_id)))
  have hint : ∀ q, Integrable (Fc q) mu := fun q =>
    (hcont q).integrable_of_hasCompactSupport (hhc.mul_right (f' := fun g =>
      hK.eisensteinTerm φ lam (x * g) q))
  have hhint : Integrable (fun g => ‖h g‖) mu := (hh.integrable_of_hasCompactSupport hhc).norm
  have hpt : ∀ q g, ‖Fc q g‖ ≤ ‖h g‖ * B q := by
    intro q g
    by_cases hg : h g = 0
    · simp [Fc, hg]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound q g (subset_tsupport _ hg)) (norm_nonneg _)
  have hIc : ∀ q, ∫ g, ‖Fc q g‖ ∂mu ≤ (∫ g, ‖h g‖ ∂mu) * B q := by
    intro q
    rw [← integral_mul_const]
    exact integral_mono (hint q).norm (hhint.mul_const _) (hpt q)
  have hsum : Summable (fun q => ∫ g, ‖Fc q g‖ ∂mu) :=
    Summable.of_nonneg_of_le (fun q => integral_nonneg fun g => norm_nonneg _) hIc
      (hB.mul_left _)
  have hconv : ∀ q, rightConvolution F G h (hK.parameterTwist φ lam)
      (parabolicCosetRep p q * x) = ∫ g, Fc q g ∂mu := by
    intro q
    unfold rightConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show h g * hK.parameterTwist φ lam (parabolicCosetRep p q * x * g) =
      h g * hK.eisensteinTerm φ lam (x * g) q
    rw [mul_assoc]
    rfl
  refine ⟨?_, ?_⟩
  · refine Summable.of_norm_bounded hsum fun q => ?_
    rw [hconv q]
    exact norm_integral_le_integral_norm _
  · rw [tsum_congr hconv, integral_tsum_of_summable_integral_norm hint hsum]
    unfold rightConvolution
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show h g * hK.eisensteinSeries φ lam (x * g) =
      ∑' q, h g * hK.eisensteinTerm φ lam (x * g) q
    rw [tsum_mul_left]
    rfl

end Convolution

end AdelicGroupPoints

/-- Bernstein–Lapid (8.2a), number field case. In the setting of
`EisensteinAbsoluteConvergenceStatement` there is `R` such that for all linear coordinates
`e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there are an index type `Idx`, for `i ∈ Idx` finitely many smooth
compactly supported bi-`K_∞`-finite test functions `h i k` on `G(𝔸)`, and entire functions
`b i k`, `c i` on `ℂⁿ`, such that for every `s` some `c i s` is nonzero, and at every `s` with
`e s` `R`-regular the Eisenstein series `E = E(φ, e s)` satisfies
`∑_k b i k s · δ(h i k) E = c i s · E` pointwise on `G(𝔸)`, for every `i`. -/
def EisensteinHarishChandraEquationsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
      ∃ R : ℝ, ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
        ∃ (Idx : Type u) (m : Idx → ℕ) (h : ∀ i, Fin (m i) → AdelicGroupPoints F G → ℂ)
          (b : ∀ i, Fin (m i) → (Fin n → ℂ) → ℂ) (c : Idx → (Fin n → ℂ) → ℂ),
          (∀ i k, IsAdelicTestFunction F G (h i k) ∧
            IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
              (h i k) ∧
            IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom)
              (fun g => h i k g⁻¹)) ∧
          (∀ i k, Differentiable ℂ (b i k)) ∧ (∀ i, Differentiable ℂ (c i)) ∧
          (∀ s, ∃ i, c i s ≠ 0) ∧
          ∀ s : Fin n → ℂ, r.IsRegularParameter hA hT R (e s) →
            ∀ i (x : AdelicGroupPoints F G),
              ∑ k, b i k s * rightConvolution F G (h i k) (hK.eisensteinSeries φ (e s)) x =
                c i s * hK.eisensteinSeries φ (e s) x

/-- The uniform Harish-Chandra equations for the twists `φ_λ` give the Harish-Chandra
equations (8.2a) for the Eisenstein series in its region of absolute convergence
(`eisensteinAbsoluteConvergence`). The index type is `ℂⁿ`: the equations indexed by `s₀`
are those of `InducedHarishChandraEquationsStatement` at `s₀`. -/
theorem eisensteinHarishChandraEquations_of_induced
    (hHC : InducedHarishChandraEquationsStatement.{u}) :
    EisensteinHarishChandraEquationsStatement.{u} := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc φ
    hKmax hrho hφ
  obtain ⟨R, hR⟩ := eisensteinAbsoluteConvergence F G P M U A p iU l a r hA hT hG hU K hK rho
    hsmooth hcalc φ hKmax hrho hφ
  refine ⟨R, fun n e => ?_⟩
  choose m h b c hh hb hc hc0 heq using fun s₀ : Fin n → ℂ =>
    hHC F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ n e s₀
  refine ⟨ULift.{u} (Fin n → ℂ), fun i => m i.down, fun i => h i.down, fun i => b i.down,
    fun i => c i.down, fun i k => hh i.down k, fun i k => hb i.down k, fun i => hc i.down,
    fun s => ⟨ULift.up s, hc0 s⟩, ?_⟩
  intro s hs i x
  have hφc : Continuous φ := hφ.2.1.1
  have hconv : ∀ k : Fin (m i.down),
      Summable (fun q => rightConvolution F G (h i.down k) (hK.parameterTwist φ (e s))
          (parabolicCosetRep p q * x)) ∧
        rightConvolution F G (h i.down k) (hK.eisensteinSeries φ (e s)) x =
          ∑' q, rightConvolution F G (h i.down k) (hK.parameterTwist φ (e s))
            (parabolicCosetRep p q * x) := by
    intro k
    have htest := (hh i.down k).1
    have hcpt : IsCompact ((fun g => x * g) '' tsupport (h i.down k)) :=
      htest.2.1.isCompact.image (continuous_const.mul continuous_id)
    obtain ⟨B, hB, hBb⟩ := hR _ hcpt n e {s} isCompact_singleton
      (fun s' hs' => by rw [Set.mem_singleton_iff.1 hs']; exact hs)
    exact hK.rightConvolution_eisensteinSeries hφc (e s) htest.1.1 htest.2.1 x hB
      (fun q g hg => hBb q (x * g) ⟨g, hg, rfl⟩ s rfl)
  calc ∑ k, b i.down k s * rightConvolution F G (h i.down k) (hK.eisensteinSeries φ (e s)) x
      = ∑ k, ∑' q, b i.down k s * rightConvolution F G (h i.down k)
          (hK.parameterTwist φ (e s)) (parabolicCosetRep p q * x) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [(hconv k).2, tsum_mul_left]
    _ = ∑' q, ∑ k, b i.down k s * rightConvolution F G (h i.down k)
          (hK.parameterTwist φ (e s)) (parabolicCosetRep p q * x) := by
        rw [Summable.tsum_finsetSum fun k _ => (hconv k).1.mul_left _]
    _ = ∑' q, c i.down s * hK.parameterTwist φ (e s) (parabolicCosetRep p q * x) := by
        congr 1
        funext q
        exact heq i.down s _
    _ = c i.down s * hK.eisensteinSeries φ (e s) x := by
        rw [tsum_mul_left]
        rfl

end Langlands.Global
