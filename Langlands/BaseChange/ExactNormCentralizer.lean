import Langlands.BaseChange.NormCentralizer
import Langlands.LocalField.CanonicalProof
import Langlands.Weil.Local.ExtensionResidue
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # The twisted centralizer at an exact regular norm -/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

section General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type v} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}

/-- At an exact regular norm, the published centralizer equivalence is given by
coefficient extension, and its image is the entire twisted centralizer. -/
theorem sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq
    (hσ : IsCyclicAlgebra σ l) {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    {δ : GeneralLinear n E} (hn : cyclicNorm σ l δ = baseChange F E n γ) :
    sigmaCentralizer σ n δ = (glCentralizer γ).map (baseChange F E n) := by
  have hx : (1 : GeneralLinear n E)⁻¹ * cyclicNorm σ l δ * 1 = baseChange F E n γ := by
    simpa only [inv_one, one_mul, mul_one] using hn
  let e := normCentralizerEquiv hσ hγ 1 hx
  have he (t : glCentralizer γ) : (e t).val = baseChange F E n t.val := by
    simp only [e, normCentralizerEquiv_apply_val, inv_one, one_mul, mul_one]
  ext g
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := e.surjective ⟨g, hg⟩
    exact ⟨t.val, t.property, (he t).symm.trans (congrArg Subtype.val ht)⟩
  · rintro ⟨t, ht, rfl⟩
    exact he ⟨t, ht⟩ ▸ (e ⟨t, ht⟩).property

end General

/-- The canonical topology on a finite p-adic extension is the module topology over
any intermediate p-adic field with compatible scalar structure. -/
theorem isModuleTopology_padic_extension {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Module.Finite F.Carrier E.Carrier] :
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    IsModuleTopology F.Carrier E.Carrier := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  let : CompleteSpace F.Carrier := F.canonical_complete_proper.1
  let : ContinuousSMul F.Carrier E.Carrier := ⟨by
    simp only [Algebra.smul_def]
    exact ((Langlands.Weil.Local.extension_isometry F E
      (IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier)).continuous.comp
      continuous_fst).mul continuous_snd⟩
  let h : IsModuleTopology F.Carrier E.Carrier := isModuleTopologyOfFiniteDimensional
  exact h

end Langlands.BaseChange
