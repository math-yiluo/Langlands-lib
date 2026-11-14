import Langlands.AllFieldBZ.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.AllFieldBZ.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.HarmonicAnalysis.PadicLatticeTopology

/-!
# All-field port of `Langlands.HarmonicAnalysis.PadicLatticeTopology`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.HarmonicAnalysis.PadicLatticeTopology` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe u
variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

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

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
