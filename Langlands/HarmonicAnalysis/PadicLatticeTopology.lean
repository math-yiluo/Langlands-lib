import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Compactness and openness of p-adic additive lattices

The existing lattice topology lemmas, shared by additive self-duality and
Rankin–Selberg cutoff arguments, are collected here with their original names.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Every additive lattice `π^(-n) O` is compact for the supplied topology. -/
theorem isCompact_additiveLattice (n : ℤ) :
    letI := T.topology
    IsCompact (T.additiveLattice n : Set F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hset : (T.additiveLattice n : Set F.Carrier) =
      (fun t => T.uniformizer ^ (-n) * t) '' (T.Integers : Set F.Carrier) := by
    ext x
    rw [SetLike.mem_coe, T.mem_additiveLattice_iff_exists_integer]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [hset]
  exact T.isCompact_integers.image (continuous_const.mul continuous_id)

/-- Every additive lattice `π^(-n) O` is open for the supplied topology. -/
theorem isOpen_additiveLattice (n : ℤ) :
    letI := T.topology
    IsOpen (T.additiveLattice n : Set F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hset : (T.additiveLattice n : Set F.Carrier) =
      (fun x => x / T.uniformizer ^ (-n)) ⁻¹' (T.Integers : Set F.Carrier) := by
    ext x
    exact T.mem_additiveLattice_iff_div_mem_integers n x
  rw [hset]
  exact T.isOpen_integers.preimage (continuous_id.div_const _)

end Langlands.PadicField.TopologicalData
