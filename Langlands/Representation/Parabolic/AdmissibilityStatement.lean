import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic
import Langlands.Representation.Induction.Definitions
import Mathlib.RepresentationTheory.Coinvariants

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Every admissible representation of an actual block parabolic kills its
unipotent radical. This is a proposition definition, not its proof. -/
def AdmissibleRadicalTrivialClause : Prop :=
  letI := T.topology
  ∀ σ : Representation ℂ (B.parabolic F.Carrier) V,
    IsAdmissible σ →
    ∀ (u : B.unipotentRadical F.Carrier) (v : V), σ u.val v = v

/-- Inflation along the actual diagonal-block projection preserves and
reflects admissibility. -/
def LeviInflationAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible (σ.comp (B.leviProjection F.Carrier)) ↔ IsAdmissible σ

/-- Unnormalized parabolic induction of an admissible Levi representation is
admissible. The function action is the existing right-translation construction. -/
def InductionAdmissibilityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible σ →
    IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
      (σ.comp (B.leviProjection F.Carrier)))

/-- The actual unnormalized Jacquet quotient of an admissible GL representation
is admissible for the product Levi. -/
def JacquetAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ ρ : Representation ℂ (GeneralLinear n F.Carrier) V,
    IsAdmissible ρ →
    IsAdmissible ((Representation.toCoinvariants
      (ρ.comp (B.parabolic F.Carrier).subtype)
      (B.unipotentRadical F.Carrier)).comp (B.leviInParabolic F.Carrier))

/-- Concrete GL block-parabolic admissibility prerequisites, with the chosen
p-adic topology and independent field and representation universes. -/
def AdmissibilityStatement : Prop :=
  AdmissibleRadicalTrivialClause F T B V ∧
  LeviInflationAdmissibilityClause F T B V ∧
  InductionAdmissibilityClause F T B V ∧
  JacquetAdmissibilityClause F T B V

end Langlands.Parabolic
