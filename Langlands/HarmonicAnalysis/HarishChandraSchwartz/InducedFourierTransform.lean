import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.Representation.Plancherel.CompactProductInducedForm

/-! # The Fourier transform on `L(ω, P)` (Waldspurger VII.1, Lemma VII.1.1)

Waldspurger VII.1 (printed pp. 313–314): for `ω` square integrable on `M`, `E` its space and
`f ∈ C(G)`, the Fourier transform `f̂(ω, P) = d(ω) π(f̌)` is an element of
`L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)`, through the embedding (1) `I_P^G E ⊗ I_P^G Ě ↪ End(I_P^G E)`.
Lemma VII.1.1 states (i) `(ρ(g) λ(h) f)^(ω, P) = (π(g) ⊗ π̌(h)) f̂(ω, P)`,
(ii) `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))` for the product of V.2 on `L(ω, P)`, and
(iii) `(E_P^G f̂(ω, P))(g) = d(ω) θ^G_ω(λ(g) f̌)`.

Here `L(ω, P)` is Worker 200's `productInducedCoefficientObject`, `E_P^G` is its
coefficient map `CompactInduction.coefficientMap` (the integral over `K` with its Haar
probability), and the product of V.2 is `CompactInduction.formalDegreeProductForm`. The
transform is the generic `coefficientFourierTransform` of `FourierTransform` for the normalized
induced representation `I_P^G E` with `d = d(ω)`, carried to `L(ω, P)` by the inverse of the
identification `CompactInduction.coefficientTensorEquiv` of `L(ω, P)` with `I_P^G E ⊗ (I_P^G E)~`.
Lemma VII.1.1 then follows from its generic form and from
`CompactInduction.formalDegreeProductForm_eq_coefficientForm`.

The transform needs the coefficients of `I_P^G E` to have tempered growth (`hT`). By Lemma
VI.2.2 (`norm_coefficientMap_le_xi`) this holds for `Ξ` the function `xi` of the Iwasawa data
when Corollary III.1.2 holds for `M`: `hasTemperedCoefficients_normalizedInduction`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV

section Transform

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
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hi : A.representation.IsIrreducible)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **The Fourier transform `f̂(ω, P)`** (Waldspurger VII.1): `f̂(ω, P) = d(ω) π(f̌)` in
`L(ω, P)`, where `π = I_P^G ω`, `d(ω)` is the formal degree of `ω` and `π(f̌)` is identified with
an element of `I_P^G E ⊗ (I_P^G E)~` by VII.1 (1), then with an element of `L(ω, P)`. -/
def inducedFourierTransform : Space Ξ σ →ₗ[ℂ] productInducedCoefficientObject h hU A :=
  (CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1).symm.toLinearMap ∘ₗ
    coefficientFourierTransform ((normalizedInductionFunctor h hU).obj A) hw
      (CompactInduction.induced_isAdmissible h hU K hK hPK A hm hsq.1) hT hΞ hσ
      (representationFormalDegree C hC μM hcof hsq hi)

/-- Under the identification of `L(ω, P)` with `I_P^G E ⊗ (I_P^G E)~`, `f̂(ω, P)` is the generic
transform `d(ω) π(f̌)`. -/
theorem coefficientTensorEquiv_inducedFourierTransform (f : Space Ξ σ) :
    CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f) =
      coefficientFourierTransform ((normalizedInductionFunctor h hU).obj A) hw
        (CompactInduction.induced_isAdmissible h hU K hK hPK A hm hsq.1) hT hΞ hσ
        (representationFormalDegree C hC μM hcof hsq hi) f :=
  by rw [inducedFourierTransform, LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap,
    Representation.Equiv.apply_symm_apply]

/-- **Lemma VII.1.1 (i)**: `(ρ(g) λ(h) f)^(ω, P) = (π(g) ⊗ π̌(h)) f̂(ω, P)`, where `G × G` acts
on `L(ω, P)` by the induced action. -/
theorem inducedFourierTransform_translate (ht : TranslationWeights Ξ σ) (g₁ g₂ : G)
    (f : Space Ξ σ) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ
        (Space.translate ht g₁ g₂ f) =
      (productInducedCoefficientObject h hU A).representation (g₁, g₂)
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ
          f) := by
  let E := CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1
  change E.symm (coefficientFourierTransform _ hw _ hT hΞ hσ _ (Space.translate ht g₁ g₂ f)) =
    (productInducedCoefficientObject h hU A).representation (g₁, g₂)
      (E.symm (coefficientFourierTransform _ hw _ hT hΞ hσ _ f))
  erw [coefficientFourierTransform_translate]
  exact congrArg (fun T : CoefficientTensor ((normalizedInductionFunctor h hU).obj A) →ₗ[ℂ]
    productInducedCoefficientObject h hU A => T _) (E.symm.isIntertwining' (g₁, g₂))

/-- **Lemma VII.1.1 (iii)**: `(E_P^G f̂(ω, P))(g) = d(ω) θ^G_ω(λ(g) f̌)`, where `θ^G_ω` is the
character of `I_P^G ω`. -/
theorem coefficientMap_inducedFourierTransform (ht : TranslationWeights Ξ σ) (f : Space Ξ σ)
    (g : G) :
    CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδ hsq.1
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f)
        g =
      representationFormalDegree C hC μM hcof hsq hi *
        schwartzCharacter hw (CompactInduction.induced_isAdmissible h hU K hK hPK A hm hsq.1) hT
          (Space.translate ht 1 g (Space.check hΞ hσ f)) := by
  change coefficientTensorMap _
      (CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ
          f)) g = _
  rw [coefficientTensorEquiv_inducedFourierTransform]
  exact coefficientTensorMap_coefficientFourierTransform _ hw _ hT hΞ hσ ht _ f g

/-- **Lemma VII.1.1 (ii)**: `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`, where
`(φ₁, φ₂)_G = ∫_G conj(φ₁(g)) φ₂(g) dg` and `( , )` is the product of V.2 on `L(ω, P)`. -/
theorem integral_conj_coefficientMap_mul_eq_inner [MeasurableInv G] [μ.IsInvInvariant]
    (ψ : productInducedCoefficientObject h hU A) (f : Space Ξ σ) :
    ∫ g, conj (CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδ hsq.1 ψ g) * f g ∂μ =
      (CompactInduction.formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μM hsq
        hi).inner ψ
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ
          f) := by
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μM hcof hsq
  let E := CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδ hsq.1
  let B := CompactInduction.invariantPositiveForm h hU hP K hK hPK hG hδ A b
  have hd := representationFormalDegree_pos C hC μM hcof hsq hi
  rw [CompactInduction.formalDegreeProductForm_eq_coefficientForm h hU hP K hK hPK hG hδ A hcof
    C hC μM hsq hi hm CompactOpenSubgroup.cofinal b]
  change ∫ g, conj (coefficientTensorMap _ (E ψ) g) * f g ∂μ =
    ((coefficientTensorInvariantForm ((normalizedInductionFunctor h hU).obj A)
      CompactOpenSubgroup.cofinal
      (CompactInduction.induced_isAdmissible h hU K hK hPK A hm hsq.1) B).rescale
        (representationFormalDegree C hC μM hcof hsq hi)⁻¹ (inv_pos.mpr hd)).inner (E ψ)
      (E (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ
        f))
  rw [coefficientTensorEquiv_inducedFourierTransform]
  exact integral_conj_coefficientTensorMap_mul_eq_inner _ hw _ hT hΞ hσ _ hd B (E ψ) f

/-- **`f̂(ω, P)` is determined by Lemma VII.1.1 (ii)**: if `(E_P^G ψ, f)_G = (ψ, φ)` for every
`ψ ∈ L(ω, P)`, then `φ = f̂(ω, P)`. -/
theorem inducedFourierTransform_eq_of_forall_integral [MeasurableInv G] [μ.IsInvInvariant]
    (f : Space Ξ σ) (φ : productInducedCoefficientObject h hU A)
    (hφ : ∀ ψ, ∫ g, conj (CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδ hsq.1 ψ g) *
      f g ∂μ = (CompactInduction.formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μM
        hsq hi).inner ψ φ) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f = φ := by
  let B := CompactInduction.formalDegreeProductForm h hU hP K hK hPK hG hδ A hcof C hC μM hsq hi
  let F := inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f
  have hinner : ∀ ψ, B.inner ψ F = B.inner ψ φ := fun ψ =>
    (integral_conj_coefficientMap_mul_eq_inner h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw
      hT hΞ hσ ψ f).symm.trans (hφ ψ)
  let := B.toInnerProductCore
  have hzero : B.inner (F - φ) (F - φ) = 0 := by
    rw [InnerProductSpace.Core.inner_sub_right, hinner, sub_self]
  exact sub_eq_zero.mp (B.definite _ hzero)

end Transform

section Tempered

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]

include hK in
/-- **Tempered coefficients of `I_P^G ω`** (from Lemma VI.2.2): if Corollary III.1.2 holds for
`M` with `Ξ^M` (hypothesis `hcoeff`), then every coefficient of the normalized induced
representation is bounded by `c Ξ(g)`, so `I_P^G ω` has tempered coefficients for `Ξ` and every
`σ`. -/
theorem hasTemperedCoefficients_normalizedInduction (hP : IsClosed (P : Set G))
    (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
    (hG : ∀ g : G, Measure.modularCharacter g = 1)
    (hδP : ∀ q : P, Measure.modularCharacter q =
      (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
    (hA : A.IsAdmissible) (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    (σ : G → ℝ) :
    HasTemperedCoefficients (xi hP₀K δ₀) σ
      ((normalizedInductionFunctor h hU).obj A).representation := by
  intro v ℓ
  let E := CompactInduction.coefficientTensorEquiv h hU A K hK hP hm hPK hG hδP hA
  obtain ⟨c, -, hc⟩ := norm_coefficientMap_le_xi h hU A K hK hP hm hPK hG hδP hA hδ hL hP₀K hMK
    hδ₀ hcoeff (E.symm (v ⊗ₜ[ℂ] ℓ))
  refine ⟨c, 0, fun g => ?_⟩
  have he : CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδP hA
      (E.symm (v ⊗ₜ[ℂ] ℓ)) g = ℓ.val (((normalizedInductionFunctor h hU).obj A).representation
        g v) := by
    change coefficientTensorMap _ (E (E.symm (v ⊗ₜ[ℂ] ℓ))) g = _
    rw [Representation.Equiv.apply_symm_apply, coefficientTensorMap_tmul]
  rw [Real.rpow_zero, mul_one]
  beta_reduce
  rw [← he]
  exact hc g

end Tempered

end Langlands.HarishChandraSchwartz
