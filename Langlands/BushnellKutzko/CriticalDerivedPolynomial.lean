import Langlands.BushnellKutzko.CriticalDerivedResidue
import Langlands.BushnellKutzko.SubfieldLayerObstructions
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Minpoly.Field

/-! # Lifting the residual polynomial of the normalized symbol -/

noncomputable section

open ValuativeRel IsLocalRing Polynomial
open scoped BigOperators

namespace Langlands.BushnellKutzko.CriticalDerived

universe uF uV uE uK

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {K : Type uK} [Field K] [Algebra F K] [Module K V] [IsScalarTower F K V]
  [FiniteDimensional F K] (hK : ∀ u : Kˣ, subfieldUnits F K V u ∈ 𝓛.stabilizer)

local notation "Oₖ" => subfieldIntegers F K
local instance : IsDiscreteValuationRing Oₖ := subfieldIntegers_isDiscreteValuationRing F K
local notation "kₖ" => ResidueField Oₖ
local notation "kₑ" => ResidueField 𝒪[E]
local notation "ιK" => subfieldEmbedding F K V
local notation "ιE" => subfieldEmbedding F E V

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel E]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem restrictEnd_algebraMap (r : E) :
    restrictEnd (algebraMap E (Module.End E V) r) = ιE r := by
  ext v
  rfl

/-- Evaluate using the matching integral coefficients and the matching degree-zero scalar. -/
theorem eval_symbol_match {z : Module.End E V} (ζ : Oₖ)
    (hz : SymbolEq 𝓛 0 (restrictEnd z) (ιK (ζ : K)))
    (f : kₑ →+* kₖ)
    (hf : ∀ r : 𝒪[E], ∃ t : Oₖ,
      SymbolEq 𝓛 0 (ιE (r : E)) (ιK (t : K)) ∧ f (residue 𝒪[E] r) = residue Oₖ t)
    (P : Polynomial 𝒪[E]) :
    ∃ t : Oₖ, SymbolEq 𝓛 0
        (restrictEnd (aeval z (P.map (algebraMap 𝒪[E] E)))) (ιK (t : K)) ∧
      residue Oₖ t = (P.map (f.comp (residue 𝒪[E]))).eval (residue Oₖ ζ) := by
  classical
  choose r hr using hf
  let s := Finset.range (P.natDegree + 1)
  let t : Oₖ := ∑ i ∈ s, r (P.coeff i) * ζ ^ i
  refine ⟨t, ?_, ?_⟩
  · rw [aeval_def, eval₂_map, P.eval₂_eq_sum_range, map_sum]
    have ht : ιK (t : K) = ∑ i ∈ s, ιK (r (P.coeff i) : K) * (ιK (ζ : K)) ^ i := by
      simp [t]
    rw [ht]
    apply SymbolEq.sum
    intro i _
    simp only [map_mul, map_pow, RingHom.comp_apply, restrictEnd_algebraMap]
    change SymbolEq 𝓛 0 (ιE (P.coeff i : E) * restrictEnd z ^ i) _
    simpa only [mul_zero, add_zero] using (hr (P.coeff i)).1.mul (hz.pow i)
  · rw [eval_map, P.eval₂_eq_sum_range]
    simp only [t, s, map_sum, map_mul, map_pow, RingHom.comp_apply, ← (hr _).2]

variable (𝓒 : LatticeChain 𝒪[E] E V) (hlat : ∀ i, (𝓒.lattice i : Set V) = 𝓛.lattice i)

include hK hlat in
/-- The scalar match at depth zero gives a monic integral lift of the residual minimal
polynomial; its evaluation at `z` is one step deeper. -/
theorem exists_residual_polynomial {z : Module.End E V} (ζ : Oₖ)
    (hζ : residue Oₖ ζ ≠ 0)
    (hz : SymbolEq 𝓛 0 (restrictEnd z) (ιK (ζ : K)))
    (f : kₑ →+* kₖ)
    (hf : ∀ r : 𝒪[E], ∃ t : Oₖ,
      SymbolEq 𝓛 0 (ιE (r : E)) (ιK (t : K)) ∧ f (residue 𝒪[E] r) = residue Oₖ t) :
    ∃ P : Polynomial 𝒪[E], P.Monic ∧ IsUnit (P.coeff 0) ∧
      Irreducible (P.map (residue 𝒪[E])) ∧
      aeval z (P.map (algebraMap 𝒪[E] E)) ∈ 𝓒.endFiltration 1 := by
  let := f.toAlgebra
  let z₀ := residue Oₖ ζ
  let p := minpoly kₑ z₀
  let : Finite kₖ := 𝓛.finite_subfieldResidueField K
  have hzint : IsIntegral kₑ z₀ := Algebra.IsIntegral.isIntegral _
  have hp : p.Monic := minpoly.monic hzint
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic
    ((lifts_iff_coeff_lifts p).mpr fun i => residue_surjective (p.coeff i)) hp
  refine ⟨P, hPm, ?_, hP ▸ minpoly.irreducible hzint, ?_⟩
  · apply (residue_ne_zero_iff_isUnit _).mp
    rw [← coeff_map, hP]
    exact minpoly.coeff_zero_ne_zero hzint hζ
  · obtain ⟨t, ht, ht'⟩ := eval_symbol_match 𝓛 ζ hz f hf P
    have ht₀ : residue Oₖ t = 0 := by
      rw [ht', ← Polynomial.map_map, hP, eval_map]
      exact minpoly.aeval kₑ z₀
    apply (mem_endFiltration_restrictScalars hlat).mpr
    have hm := add_mem ht.2.2 ((scalar_mem_one_iff 𝓛 hK t).mpr ht₀)
    simpa only [sub_add_cancel, zero_add, restrictEnd_apply] using hm

end Langlands.BushnellKutzko.CriticalDerived
