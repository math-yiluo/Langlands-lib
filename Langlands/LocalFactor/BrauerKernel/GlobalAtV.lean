import Langlands.LocalFactor.BrauerKernel.GlobalCharacters
import Langlands.LocalFactor.BrauerKernel.GlobalCore
import Langlands.LocalFactor.BrauerKernel.RealizationEpsilon
import Langlands.LocalFactor.BrauerKernel.LocalMapTransport

/-! # The epsilon product at the distinguished place and the generator values -/

noncomputable section

set_option autoImplicit false

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.CompletionPadic Langlands.Global.AdelicFunctoriality
open ClassField.Global ClassField.Global.RelativeWeilGroup CommonClosure Correspondence
open scoped NumberField

section Evaluation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The evaluation of a presentation vanishes when the product of the generator values, raised to
the coefficients and indexed by an enumeration of the support, is `1`. -/
theorem evaluationMap_eq_zero_of_prod {E : Extension F} {ψ : AdditiveCharacter F E}
    {measures : HaarFamily F} (z : Presentation F E) {n : ℕ} (gs : Fin n ≃ z.support)
    (h : ∏ i, ((generatorValue F E ψ measures (gs i).1 : ℂˣ) : ℂ) ^ z (gs i).1 = 1) :
    evaluationMap F E ψ measures z = 0 := by
  have h1 : ∏ g ∈ z.support, generatorValue F E ψ measures g ^ z g = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one, ← h, ← Finset.prod_coe_sort z.support]
    refine (Fintype.prod_equiv gs (fun i => ((generatorValue F E ψ measures (gs i).1 ^
      z (gs i).1 : ℂˣ) : ℂ)) _ fun _ => rfl).symm.trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val]
  have h2 : Additive.toMul (evaluationMap F E ψ measures z) =
      ∏ g ∈ z.support, generatorValue F E ψ measures g ^ z g := by
    rw [evaluationMap, Finsupp.linearCombination_apply, Finsupp.sum, toMul_sum]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [toMul_zsmul, toMul_ofMul]
  exact toMul_eq_one.mp (h2.trans h1)

end Evaluation

section Place

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]

/-- If `w` is the only place of `K'` above `v`, every place above `v` of an intermediate field
`M` is the place under `w`. -/
theorem eq_under_of_unique (hwu : ∀ w' : HeightOneSpectrum (𝓞 K'),
      w'.asIdeal.LiesOver v.asIdeal → w' = w)
    (M : IntermediateField k K') (q : FinitePlacesAbove M v) : q.1 = w.under (𝓞 M) := by
  obtain ⟨w', hw'⟩ := placeAbove K' q.1
  have : q.1.asIdeal.LiesOver v.asIdeal := q.2
  have hw'v : w'.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans w'.asIdeal q.1.asIdeal v.asIdeal
  have hw : w' = w := hwu w' hw'v
  subst hw
  exact (under_eq_of_liesOver w').symm

omit [NumberField k] [NumberField K'] in
/-- The place of `M` under `w` lies over `v`. -/
theorem under_liesOver (M : IntermediateField k K') :
    (w.under (𝓞 M)).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot w.asIdeal (w.under (𝓞 M)).asIdeal v.asIdeal

end Place

section Realization

attribute [local instance] relativeGaloisTopology

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  [IsGalois k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} {e : ReciprocityFamily F}
  {z : Presentation F (Correspondence.baseExtension F)} (D : GaloisTypeDecomposition F e z)
  [Normal F.Carrier D.K.field]
  (θ : (K' ≃ₐ[k] K') ≃* (D.K.field ≃ₐ[F.Carrier] D.K.field))
  (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
  (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* D.K.field)
  (hφ : @Continuous _ _ _ F.canonicalTopology φ)
  (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm)
  (hψ : @Continuous _ _ _ (D.K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
  (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
    algebraMap F.Carrier D.K.field (φ (algebraMap k (v.adicCompletion k) x)))
  (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
    ψ (algebraMap K' (w.adicCompletion K') (σ x)))

set_option maxHeartbeats 4000000 in
include hφ' hψ hcomp hθ in
/-- **The distinguished place.** In a realization of `D.K/F` as the completion at the only place
`w` above `v` of a Galois extension `K'/k`, let `Θ_i g` be Hecke characters whose reciprocity
characters are the inflated characters of `D.θ_i g`, and `α` a Hecke character of `k` trivial on
`k_v^×`. If the epsilon product of the place `v` for the characters `(α ∘ N) · ‖·‖^{t_i g} · Θ_i g`
is `1`, then the evaluation of `z` vanishes for the base character of the transport of `ψv`. -/
theorem evaluationMap_eq_zero_of_placeEpsilon
    (hM : LocalRelativeWeilMapExistenceStatement.{0})
    (hN3 : LocalTransferReciprocityStatement.{0})
    (hCC : LocalClassField.CommonClosureReciprocityExistence.{0})
    (I : ∀ (p : ℕ) [Fact p.Prime], ClassFieldTheory.Local.InvariantFamily.{0, 0} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    (c : FundamentalClass.ClassFamily.{0})
    (hc : FundamentalClass.Generates c ∧ FundamentalClass.Restriction c ∧
      FundamentalClass.Inflation c ∧ FundamentalClass.LocalCompatibility I c)
    (he : NormalizedReciprocity F e)
    (hwu : ∀ w' : HeightOneSpectrum (𝓞 K'), w'.asIdeal.LiesOver v.asIdeal → w' = w)
    {n : ℕ} (gs : Fin n ≃ z.support) (α : HeckeCharacter k) (hα : α.finiteComponent v = 1)
    (Θ₁ Θ₂ : ∀ g, HeckeCharacter (globalField D k K' θ g))
    (hΘ₁ : ∀ g, continuousReciprocityCharacter c (globalField D k K' θ g) K' (Θ₁ g) =
      globalCharacter D c k K' θ hc.2.1 g (D.θ₁ g))
    (hΘ₂ : ∀ g, continuousReciprocityCharacter c (globalField D k K' θ g) K' (Θ₂ g) =
      globalCharacter D c k K' θ hc.2.1 g (D.θ₂ g))
    (ψv : NontrivialAdditiveCharacter (padicField v))
    (μv : ∀ j : (Σ i, FinitePlacesAbove (globalField D k K' θ (gs i).1) v),
      LocalAdditiveHaarMeasure (towerPadicField v j.2.1))
    (hplace : placeEpsilonRatioProduct (fun i => z (gs i).1)
      (fun i => globalField D k K' θ (gs i).1)
      (fun i => HeckeCharacter.normComp α *
        HeckeCharacter.normPower (globalField D k K' θ (gs i).1) (D.t₁ (gs i).1) * Θ₁ (gs i).1)
      (fun i => HeckeCharacter.normComp α *
        HeckeCharacter.normPower (globalField D k K' θ (gs i).1) (D.t₂ (gs i).1) * Θ₂ (gs i).1)
      v ψv μv = 1)
    (ψb : AdditiveCharacter F (Correspondence.baseExtension F))
    (hψb : IsBaseCharacter F (PadicField.ConductorTransport.additiveCharacter (padicField v) F
      (realizationPadicEquiv v φ hφ) ψv) ψb)
    (measures : HaarFamily F) :
    evaluationMap F _ ψb measures z = 0 := by
  refine evaluationMap_eq_zero_of_prod z gs ?_
  rw [← hplace]
  unfold placeEpsilonRatioProduct
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hg : (gs i).1 ∈ z.support := (gs i).2
  have : w.asIdeal.LiesOver (w.under (𝓞 (globalField D k K' θ (gs i).1))).asIdeal :=
    liesOver_under w
  have huv : (w.under (𝓞 (globalField D k K' θ (gs i).1))).asIdeal.LiesOver v.asIdeal :=
    under_liesOver v w (globalField D k K' θ (gs i).1)
  let q₀ : FinitePlacesAbove (globalField D k K' θ (gs i).1) v :=
    ⟨w.under (𝓞 (globalField D k K' θ (gs i).1)), huv⟩
  rw [Fintype.prod_eq_single q₀ fun q hq =>
    absurd (Subtype.ext (eq_under_of_unique v w hwu (globalField D k K' θ (gs i).1) q)) hq]
  congr 1
  -- the local maps at the place under `w`
  have hw' : w.asIdeal.LiesOver
      (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension))).asIdeal :=
    liesOver_under w
  have hu' : (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension))).asIdeal.LiesOver
      v.asIdeal :=
    under_liesOver v w (realizationSubfield D.K θ (gs i).1.extension)
  obtain ⟨eCu, heCu⟩ := hCC (residuePrime (w.under (𝓞 (globalField D k K' θ (gs i).1))))
    (padicField (w.under (𝓞 (globalField D k K' θ (gs i).1))))
    (padicField (w.under (𝓞 (globalField D k K' θ (gs i).1)))).canonicalTopologicalData
  have hew := (LocalClassField.commonClosureGeometricProof _
    (padicField (w.under (𝓞 (globalField D k K' θ (gs i).1)))) eCu heCu).2
    (towerPadicField (w.under (𝓞 (globalField D k K' θ (gs i).1))) w)
    (completionPadicAlgHom (w.under (𝓞 (globalField D k K' θ (gs i).1))) w)
  obtain ⟨ι, hι, hιt⟩ := exists_localMap_padicFieldAt hM hN3 I hI c hc
    (w.under (𝓞 (globalField D k K' θ (gs i).1))) w _ hew
    (residuePrime_eq v (w.under (𝓞 (globalField D k K' θ (gs i).1))))
  have hgeo := (LocalClassField.commonClosureGeometricProof (residuePrime v) F e he).2
    (towerPadicField v (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension))))
    (realizationBaseAlgHom v (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension))) φ hφ')
  have h₁ := fieldCharacter_eq_realizationTransport v D.K θ w φ ψ hφ hφ' hψ hcomp hθ
    (gs i).1.extension (D.le _ hg) (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension)))
    e he (gs i).1.first (D.t₁ (gs i).1) (D.θ₁ (gs i).1) (D.θ₁_spec _ hg) ι hι (hιt _ hgeo) α hα
    (Θ₁ (gs i).1) fun x => by
      obtain ⟨hx, hval⟩ := globalCharacter_apply D c k K' θ hc.2.1 (gs i).1 (D.θ₁ (gs i).1) x
      exact ⟨hx, (DFunLike.congr_fun (hΘ₁ (gs i).1) x).trans hval⟩
  have h₂ := fieldCharacter_eq_realizationTransport v D.K θ w φ ψ hφ hφ' hψ hcomp hθ
    (gs i).1.extension (D.le _ hg) (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension)))
    e he (gs i).1.second (D.t₂ (gs i).1) (D.θ₂ (gs i).1) (D.θ₂_spec _ hg) ι hι (hιt _ hgeo) α hα
    (Θ₂ (gs i).1) fun x => by
      obtain ⟨hx, hval⟩ := globalCharacter_apply D c k K' θ hc.2.1 (gs i).1 (D.θ₂ (gs i).1) x
      exact ⟨hx, (DFunLike.congr_fun (hΘ₂ (gs i).1) x).trans hval⟩
  exact generatorValue_eq_realizationEpsilon v D.K θ w φ ψ hφ hφ' hψ hcomp hθ (gs i).1
    (D.le _ hg) (w.under (𝓞 (realizationSubfield D.K θ (gs i).1.extension))) _ _ h₁ h₂ ψv ψb
    hψb measures (μv ⟨i, q₀⟩)

end Realization

end Langlands.LocalFactor.NonabelianBrauer
