import Langlands.BushnellKutzko.StratumEquivalenceStatement
import Langlands.BushnellKutzko.StratumEquivalenceOrder
import Langlands.BushnellKutzko.StratumEquivalenceCritical
import Langlands.BushnellKutzko.StratumEquivalenceResidueDegree
import Langlands.BushnellKutzko.NormalizerProof

/-! # Invariants of equivalent strata (BK93 (1.5.2), (2.1.4); T5)

Proof of `StratumEquivalenceStatement`, assembled from the helper modules
`StratumEquivalenceOrder` (order, `r`, `n`), `StratumEquivalenceCritical` (`𝔅 + 𝔓` and the
critical exponent), `StratumEquivalenceResidue` (ramification index) and
`StratumEquivalenceResidueDegree` (residue degree).
-/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

namespace StratumEquivalence

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- For the field `F[b]`, the order `𝔄 ∩ End_{F[b]}(V)` is `𝔅 = 𝔄 ∩ ker a_b`. -/
theorem fieldOrder_elementAlgebra (𝓛 : LatticeChain 𝒪[F] F V) {b : Module.End F V}
    (hf : IsField (elementAlgebra b)) :
    letI := hf.toField
    fieldOrder 𝓛 (elementAlgebra b) = centralizerLattice 𝓛 b 0 := by
  let _ := hf.toField
  ext x
  simp only [fieldOrder, centralizerLattice, Submodule.mem_inf, LinearMap.mem_ker,
    adjointMap_apply, sub_eq_zero]
  refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : ∀ (a : elementAlgebra b) (v : V), x (a • v) = a • x v := hx
    ext v
    exact (hx' ⟨b, Algebra.self_mem_adjoin_singleton F b⟩ v).symm
  · intro a v
    have hle : elementAlgebra b ≤ Subalgebra.centralizer F {x} := by
      apply Algebra.adjoin_le
      rintro _ rfl
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hx.symm
    have ha := hle a.2
    rw [Subalgebra.mem_centralizer_iff] at ha
    change x ((a : Module.End F V) v) = (a : Module.End F V) (x v)
    exact LinearMap.congr_fun (ha x rfl) v

/-- Equivalent strata have the same stabilizer `𝔎(𝔄)`, since `𝔎(𝔄)` is the normalizer of
the common order `𝔄`. -/
theorem mem_stabilizer_iff_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T)
    (g : (Module.End F V)ˣ) : g ∈ S.chain.stabilizer ↔ g ∈ T.chain.stabilizer := by
  rw [(normalizer F V S.chain).2.1 g, (normalizer F V T.chain).2.1 g,
    order_eq_of_equivalent h]

variable [FiniteDimensional F V]

/-- Equivalent strata whose fields `F[b]` normalize their chains, and which have the same
`𝔅 + 𝔓`, have the same ramification index and residue degree. -/
theorem invariants_eq_of_equivalent {S T : Stratum 𝒪[F] F V} (h : S.Equivalent T)
    (hsup : centralizerLattice S.chain S.b 0 ⊔ S.chain.endFiltration 1 =
      centralizerLattice T.chain T.b 0 ⊔ T.chain.endFiltration 1)
    (hfS : IsField (elementAlgebra S.b)) (hfT : IsField (elementAlgebra T.b))
    (huS : letI := hfS.toField
      ∀ a : (elementAlgebra S.b)ˣ,
        subfieldUnits F (elementAlgebra S.b) V a ∈ S.chain.stabilizer)
    (huT : letI := hfT.toField
      ∀ a : (elementAlgebra T.b)ˣ,
        subfieldUnits F (elementAlgebra T.b) V a ∈ T.chain.stabilizer) :
    elementRamificationIndex F S.b = elementRamificationIndex F T.b ∧
      elementResidueDegree F S.b = elementResidueDegree F T.b := by
  unfold elementRamificationIndex elementResidueDegree
  simp only [hfS, hfT, ↓reduceDIte]
  let _ := hfS.toField
  let _ := hfT.toField
  have hP := endFiltration_eq_of_equivalent h
  have huT' : ∀ a : (elementAlgebra T.b)ˣ,
      subfieldUnits F (elementAlgebra T.b) V a ∈ S.chain.stabilizer :=
    fun a => (mem_stabilizer_iff_of_equivalent h _).2 (huT a)
  have hM : fieldOrder S.chain (elementAlgebra S.b) ⊔ S.chain.endFiltration 1 =
      fieldOrder S.chain (elementAlgebra T.b) ⊔ S.chain.endFiltration 1 := by
    rw [fieldOrder_elementAlgebra S.chain hfS, fieldOrder_elementAlgebra S.chain hfT, hsup,
      centralizerLattice_congr hP, hP]
  have : FiniteDimensional F (elementAlgebra S.b) :=
    FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule (elementAlgebra S.b))
  have : FiniteDimensional F (elementAlgebra T.b) :=
    FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule (elementAlgebra T.b))
  exact ⟨ramificationIndex_eq_of_sup_eq S.chain huS huT' hM,
    residueDegree_eq_of_sup_eq S.chain huS huT' hM⟩

end StratumEquivalence

open StratumEquivalence in
/-- **BK93 (1.5.2), p. 43, and (2.1.4), p. 50 (T5).** -/
theorem stratumEquivalence : StratumEquivalenceStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S T h
  refine ⟨order_eq_of_equivalent h, r_eq_of_equivalent h, n_eq_of_equivalent h,
    fun hS hT => ?_⟩
  obtain ⟨hsup, hcrit⟩ := sup_eq_and_criticalExponent_eq_of_equivalent h hS hT
  obtain ⟨⟨⟨hfS, huS⟩, -⟩, -⟩ := hS
  obtain ⟨⟨⟨hfT, huT⟩, -⟩, -⟩ := hT
  exact ⟨hsup, hcrit, invariants_eq_of_equivalent h hsup hfS hfT huS huT⟩

end Langlands.BushnellKutzko
