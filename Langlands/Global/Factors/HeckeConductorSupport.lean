import Langlands.Global.Factors.HeckeMixedProductFormula
import Langlands.Global.Hecke.AdelicLattice

/-! # Finite conductor support for actual global additive characters -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField Langlands.HarmonicAnalysis
open Filter

variable {K : Type u} [Field K] [NumberField K]

variable (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ x : K, ψ (diagonal K x) = 1)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (CompletionPadic.topologicalData v).topology)
    (hf : ∀ v, IsFiniteAdditiveComponent ψ v (ψf v))
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (hR : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v))
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (hC : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v))

include ψ hdiag hf aR hR aC hC

/-- The actual global character gives the lattice product formula for every supplied
finite component and every supplied nonzero archimedean scale. -/
theorem additiveProductFormula_of_global :
    Hecke.AdditiveProductFormula (fun v => (aR v : ℝ)) (fun v => (aC v : ℂ)) ψf := by
  exact mixed_additive_product_formula ψ hdiag ψf hf
    (fun v hv => aR ⟨v, hv⟩) (fun v hv => aC ⟨v, hv⟩)
    (fun v hv => hR ⟨v, hv⟩) (fun v hv => hC ⟨v, hv⟩)

/-- Actual additive conductors have finite support, using diagonal triviality and
lattice arithmetic rather than an assumed adelic pairing equivalence. -/
theorem finite_additiveConductor_support :
    {v : FinitePlace K | (CompletionPadic.topologicalData v).additiveConductor (ψf v) ≠ 0}.Finite := by
  classical
  have hfin := Filter.eventually_cofinite.mp (eventually_additiveConductor_nonneg ψ ψf hf)
  apply Hecke.finite_setOf_additiveConductor_ne_zero
    (fun v => (aR v).ne_zero) (fun v => (aC v).ne_zero)
    (additiveProductFormula_of_global ψ hdiag ψf hf aR hR aC hC) hfin.toFinset
  intro v hv
  by_contra hn
  exact hv (hfin.mem_toFinset.mpr hn)

/-- The conductor vector of the original supplied finite components. -/
def additiveConductorDivisor : FinitePlace K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => (CompletionPadic.topologicalData v).additiveConductor (ψf v))
    (finite_additiveConductor_support ψ hdiag ψf hf aR hR aC hC)

@[simp] theorem additiveConductorDivisor_apply (v : FinitePlace K) :
    additiveConductorDivisor ψ hdiag ψf hf aR hR aC hC v =
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) := rfl

/-- A finite exceptional set for the actual additive conductors. -/
theorem exists_finset_additiveConductor_eq_zero :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S,
      (CompletionPadic.topologicalData v).additiveConductor (ψf v) = 0 := by
  classical
  let n := additiveConductorDivisor ψ hdiag ψf hf aR hR aC hC
  refine ⟨n.support, fun v hv => ?_⟩
  exact (additiveConductorDivisor_apply ψ hdiag ψf hf aR hR aC hC v).symm.trans
    (Finsupp.notMem_support_iff.mp hv)

/-- The finite-epsilon exceptional-set conclusion for every supplied self-dual measure. -/
theorem exists_finset_finiteEpsilon_eq_one (χ : HeckeCharacter K)
    (μ : ∀ v : FinitePlace K,
      LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) (ψf v)) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ s : ℂ,
      finiteEpsilon χ ψf μ v s = 1 := by
  obtain ⟨S, hS⟩ := exists_finset_additiveConductor_eq_zero ψ hdiag ψf hf aR hR aC hC
  exact exists_finset_finiteEpsilon_eq_one_of_additiveConductor χ ψf μ S hS

end Langlands.Global.HeckeFunctionalEquation
