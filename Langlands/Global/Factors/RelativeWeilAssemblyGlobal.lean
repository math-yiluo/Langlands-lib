import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Global.Factors.RelativeWeilAssemblyHecke

/-!
# The global product package of a Brauer decomposition

Products, with integer exponents, of Hecke functional-equation packages over intermediate
fields, regrouped over the finite places of the base field.
-/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine

open Filter Topology
open NumberField IsDedekindDomain
open scoped NumberField
open Langlands.Global Langlands.Global.HeckeFunctionalEquation Langlands.Global.AdelicFunctoriality

variable {F : Type u} [Field F] [NumberField F]

/-- The additive components at the places of `K` of `ψ ∘ Tr`, built from components `ψf` of
`ψ` at the places of `F`. -/
def traceComponents {K : Type u} [Field K] [NumberField K] [Algebra F K]
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (u : FinitePlace K) :
    @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField u).Carrier _
      (CompletionPadic.topologicalData u).topology :=
  localTraceCharacter (u.under (𝓞 F)) u (ψf (u.under (𝓞 F)))

theorem isFiniteAdditiveComponent_traceComponents {K : Type u} [Field K] [NumberField K]
    [Algebra F K] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) (u : FinitePlace K) :
    IsFiniteAdditiveComponent (traceAdditiveCharacter (L := K) ψ hψ) u (traceComponents ψf u) :=
  isFiniteAdditiveComponent_traceAdditiveCharacter ψ hψ (u.under (𝓞 F)) (ψf _) (hψf _)
    ⟨u, liesOver_under u⟩

theorem exists_traceAdditiveCharacter_ne_one {K : Type u} [Field K] [NumberField K]
    [Algebra F K] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (diagonal F x) = 1) :
    ∃ x : Adeles K, traceAdditiveCharacter (L := K) ψ hψ x ≠ 1 := by
  by_contra! h
  exact (traceAdditiveCharacter (L := K) ψ hψ).nontrivial (DFunLike.ext _ _ h)

/-- The Hecke package of `λ` over a finite extension `K` of `F`, for `ψ ∘ Tr`, regrouped over
the finite places of `F`, with any exceptional set `B` outside which the regrouped epsilon
factors are `1`. -/
theorem hasGlobalEquation_heckePushforward (hH : HeckeGlobalFunctionalEquationStatement.{u})
    {K : Type u} [Field K] [NumberField K] [Algebra F K]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) (lam : HeckeCharacter K)
    (μK : ∀ u : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData u)
        (traceComponents ψf u))
    (D : HeckeArchData lam (traceAdditiveCharacter (L := K) ψ hψ)) (B : Finset (FinitePlace F))
    (hB : ∀ z ∉ B, ∀ u ∈ placesAbove K z, ∀ s : ℂ,
      finiteEpsilon lam (traceComponents ψf) μK u s = 1) :
    HasGlobalEquation (fun z s => ∏ u ∈ placesAbove K z, heckeL lam u s)
      (fun z s => ∏ u ∈ placesAbove K z, heckeL lam⁻¹ u s)
      (fun z s => ∏ u ∈ placesAbove K z, finiteEpsilon lam (traceComponents ψf) μK u s)
      D.A D.Ad D.Ae B := by
  classical
  obtain ⟨S, hS, P⟩ := hasGlobalEquation_of_heckeArchData hH lam
    (traceAdditiveCharacter (L := K) ψ hψ) (exists_traceAdditiveCharacter_ne_one ψ hψ)
    (traceAdditiveCharacter_diagonal ψ hψ) (traceComponents ψf)
    (isFiniteAdditiveComponent_traceComponents ψ hψ ψf hψf) μK D
  let T : Finset (FinitePlace F) := B ∪ S.image (fun q : FinitePlace K => q.under (𝓞 F))
  have P' := P.pushforwardPlaces hS T
    (fun q hq => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq))
  exact P'.changeSet (fun z _ hzB s => Finset.prod_eq_one fun u hu => hB z hzB u hu s)
    (fun z hzB hzT => absurd (Finset.mem_union_left _ hzB) hzT)

/-- The Hecke package of `χ` over `F` itself, with any exceptional set `B` outside which its
epsilon factors are `1`. -/
theorem hasGlobalEquation_heckeBase (hH : HeckeGlobalFunctionalEquationStatement.{u})
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ1 : ∃ x : Adeles F, ψ x ≠ 1) (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v)) (χ : HeckeCharacter F)
    (μ : ∀ v : FinitePlace F,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (D : HeckeArchData χ ψ) (B : Finset (FinitePlace F))
    (hB : ∀ z ∉ B, ∀ s : ℂ, finiteEpsilon χ ψf μ z s = 1) :
    HasGlobalEquation (heckeL χ) (heckeL χ⁻¹) (finiteEpsilon χ ψf μ) D.A D.Ad D.Ae B := by
  obtain ⟨S, hS, P⟩ := hasGlobalEquation_of_heckeArchData hH χ ψ hψ1 hψ ψf hψf μ D
  exact P.changeSet (fun z _ hzB s => hB z hzB s) (fun z _ hzS s => hS z hzS s)

/-- The product package of a Brauer decomposition: `χ` over `F` with exponent `d`, and, for
each `i`, the quotient of the regrouped packages of `λ i` and `λ' i` over `K i` with exponent
`r i`. -/
theorem hasGlobalEquation_brauerProduct (hH : HeckeGlobalFunctionalEquationStatement.{u})
    {E : Type u} [Field E] [NumberField E] [Algebra F E]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ1 : ∃ x : Adeles F, ψ x ≠ 1) (hψ : ∀ x : F, ψ (diagonal F x) = 1)
    (ψf : ∀ v : FinitePlace F,
      @HarmonicAnalysis.UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hψf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (μ : ∀ v : FinitePlace F,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v))
    (d : ℤ) (χ : HeckeCharacter F) (DF : HeckeArchData χ ψ)
    {n : ℕ} (r : Fin n → ℤ) (K : Fin n → IntermediateField F E)
    (lam lam' : ∀ i, HeckeCharacter (K i))
    (μK : ∀ i (u : FinitePlace (K i)),
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData u)
        (traceComponents ψf u))
    (DK : ∀ i, HeckeArchData (lam i) (traceAdditiveCharacter (L := K i) ψ hψ))
    (DK' : ∀ i, HeckeArchData (lam' i) (traceAdditiveCharacter (L := K i) ψ hψ))
    (B : Finset (FinitePlace F))
    (hBF : ∀ z ∉ B, ∀ s : ℂ, finiteEpsilon χ ψf μ z s = 1)
    (hBK : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (lam i) (traceComponents ψf) (μK i) u s = 1)
    (hBK' : ∀ i, ∀ z ∉ B, ∀ u ∈ placesAbove (K i) z, ∀ s : ℂ,
      finiteEpsilon (lam' i) (traceComponents ψf) (μK i) u s = 1) :
    HasGlobalEquation
      (fun z s => heckeL χ z s ^ d * ∏ i ∈ Finset.univ,
        ((∏ u ∈ placesAbove (K i) z, heckeL (lam i) u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i) u s)⁻¹) ^ r i)
      (fun z s => heckeL χ⁻¹ z s ^ d * ∏ i ∈ Finset.univ,
        ((∏ u ∈ placesAbove (K i) z, heckeL (lam i)⁻¹ u s) *
          (∏ u ∈ placesAbove (K i) z, heckeL (lam' i)⁻¹ u s)⁻¹) ^ r i)
      (fun z s => finiteEpsilon χ ψf μ z s ^ d * ∏ i ∈ Finset.univ,
        ((∏ u ∈ placesAbove (K i) z, finiteEpsilon (lam i) (traceComponents ψf) (μK i) u s) *
          (∏ u ∈ placesAbove (K i) z,
            finiteEpsilon (lam' i) (traceComponents ψf) (μK i) u s)⁻¹) ^ r i)
      (fun s => DF.A s ^ d * ∏ i ∈ Finset.univ, ((DK i).A s * ((DK' i).A s)⁻¹) ^ r i)
      (fun s => DF.Ad s ^ d * ∏ i ∈ Finset.univ, ((DK i).Ad s * ((DK' i).Ad s)⁻¹) ^ r i)
      (fun s => DF.Ae s ^ d * ∏ i ∈ Finset.univ, ((DK i).Ae s * ((DK' i).Ae s)⁻¹) ^ r i)
      B := by
  have PF := (hasGlobalEquation_heckeBase hH ψ hψ1 hψ ψf hψf χ μ DF B hBF).zpow d
  have PK : ∀ i ∈ (Finset.univ : Finset (Fin n)), _ := fun i _ =>
    (((hasGlobalEquation_heckePushforward hH ψ hψ ψf hψf (lam i) (μK i) (DK i) B (hBK i)).mul
      (hasGlobalEquation_heckePushforward hH ψ hψ ψf hψf (lam' i) (μK i) (DK' i) B
        (hBK' i)).inv).zpow (r i))
  exact PF.mul (hasGlobalEquation_finsetProd Finset.univ PK)

/-- Archimedean data concentrated at one place `w₀`: the factors are `A`, `Ad`, `Ae` at `w₀`
and `1` elsewhere. -/
def lumpedArch {I : Type*} [DecidableEq I] (w₀ : I) (A Ad Ae : ℂ → ℂ) (w : I) : LocalFactors :=
  if w = w₀ then ⟨A, Ad, Ae⟩ else ⟨fun _ => 1, fun _ => 1, fun _ => 1⟩

theorem lumpedArch_prod_lFactor {I : Type*} [Fintype I] [DecidableEq I] (w₀ : I)
    (A Ad Ae : ℂ → ℂ) (s : ℂ) :
    ∏ w, (lumpedArch w₀ A Ad Ae w).lFactor s = A s := by
  rw [Finset.prod_eq_single w₀]
  · simp [lumpedArch]
  · intro w _ hw
    simp [lumpedArch, hw]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

theorem lumpedArch_prod_dualLFactor {I : Type*} [Fintype I] [DecidableEq I] (w₀ : I)
    (A Ad Ae : ℂ → ℂ) (s : ℂ) :
    ∏ w, (lumpedArch w₀ A Ad Ae w).dualLFactor s = Ad s := by
  rw [Finset.prod_eq_single w₀]
  · simp [lumpedArch]
  · intro w _ hw
    simp [lumpedArch, hw]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

theorem lumpedArch_prod_epsilonFactor {I : Type*} [Fintype I] [DecidableEq I] (w₀ : I)
    (A Ad Ae : ℂ → ℂ) (s : ℂ) :
    ∏ w, (lumpedArch w₀ A Ad Ae w).epsilonFactor s = Ae s := by
  rw [Finset.prod_eq_single w₀]
  · simp [lumpedArch]
  · intro w _ hw
    simp [lumpedArch, hw]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

theorem lumpedArch_nonzeroMeromorphic {I : Type*} [DecidableEq I] (w₀ : I) {A Ad Ae : ℂ → ℂ}
    (hA : NonzeroMeromorphic A) (hAd : NonzeroMeromorphic Ad) (hAe : NonzeroMeromorphic Ae)
    (w : I) :
    NonzeroMeromorphic (lumpedArch w₀ A Ad Ae w).lFactor ∧
      NonzeroMeromorphic (lumpedArch w₀ A Ad Ae w).dualLFactor ∧
      NonzeroMeromorphic (lumpedArch w₀ A Ad Ae w).epsilonFactor := by
  by_cases hw : w = w₀
  · simp only [lumpedArch, hw, ite_true]
    exact ⟨hA, hAd, hAe⟩
  · simp only [lumpedArch, hw, ite_false]
    exact ⟨nonzeroMeromorphic_one, nonzeroMeromorphic_one, nonzeroMeromorphic_one⟩

end Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
