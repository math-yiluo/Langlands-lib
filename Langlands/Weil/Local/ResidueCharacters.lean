import Langlands.Weil.Local.DegreeCharacters
import Langlands.LocalField.Normalization.Definitions
import Langlands.LocalField.Canonical

/-!
# Degree characters normalized by the actual residue cardinality

The residue cardinality is calculated from the chosen local-field realization.
The canonical specialization requires only the algebraic p-adic field and a degree.
This module does not supply the actual residue-Galois degree.
-/

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable {W : Type v} [Group W] [TopologicalSpace W]

/-- The actual finite residue cardinality, as a complex unit. -/
noncomputable def residueCardinalityUnit (T : F.TopologicalData) : ℂˣ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : Finite T.ResidueField := inferInstanceAs
    (Finite (IsLocalRing.ResidueField (ValuativeRel.valuation F.Carrier).integer))
  exact cardinalityUnit T.residueCardinality (Nat.card_pos (α := T.ResidueField))

@[simp] theorem residueCardinalityUnit_val (T : F.TopologicalData) :
    (residueCardinalityUnit T : ℂ) = (T.residueCardinality : ℂ) := rfl

/-- The degree character whose degree-one value is the inverse actual residue cardinality. -/
noncomputable def residueNormCharacter (T : F.TopologicalData) (d : W →ₜ* Degree) :
    W →ₜ* ℂˣ := unramifiedCharacter d (residueCardinalityUnit T)⁻¹

theorem residueNormCharacter_apply (T : F.TopologicalData) (d : W →ₜ* Degree) (w : W) :
    (residueNormCharacter T d w : ℂ) =
      (T.residueCardinality : ℂ) ^ (-(d w).toAdd) := by
  simp [residueNormCharacter, zpow_neg]

theorem residueNormCharacter_on_kernel (T : F.TopologicalData) (d : W →ₜ* Degree)
    {w : W} (hw : w ∈ d.toMonoidHom.ker) : residueNormCharacter T d w = 1 :=
  unramifiedCharacter_on_kernel d _ hw

theorem residueNormCharacter_degree_one (T : F.TopologicalData) (d : W →ₜ* Degree)
    {w : W} (hw : d w = Multiplicative.ofAdd (1 : ℤ)) :
    (residueNormCharacter T d w : ℂ) = (T.residueCardinality : ℂ)⁻¹ := by
  simp [residueNormCharacter_apply, hw]

theorem residueNormCharacter_degree_neg_one (T : F.TopologicalData) (d : W →ₜ* Degree)
    {w : W} (hw : d w = Multiplicative.ofAdd (-1 : ℤ)) :
    (residueNormCharacter T d w : ℂ) = (T.residueCardinality : ℂ) := by
  simp [residueNormCharacter_apply, hw]

/-- Specialization to the constructed canonical realization, for every p-adic field. -/
noncomputable abbrev canonicalResidueNormCharacter (F : PadicField.{u} p)
    (d : W →ₜ* Degree) : W →ₜ* ℂˣ :=
  residueNormCharacter F.canonicalTopologicalData d

end Langlands.Weil.Local
