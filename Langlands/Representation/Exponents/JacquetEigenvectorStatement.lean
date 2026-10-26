import Langlands.Representation.Exponents.Jacquet

/-!
# Ordinary eigenvectors for generalized normalized Jacquet exponents

The pure-vector extraction step for an admissible representation, using the
existing normalized upper Jacquet module and its split-centre action.
-/

namespace Langlands

universe uF uV

/-- Every generalized normalized upper Jacquet exponent of an admissible
representation has one nonzero eigenvector for the entire split centre,
with the same character. -/
def GLJacquetExponentEigenvectorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      letI := T.topology
      IsAdmissible ρ →
      ∀ (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent B ρ χ →
        ∃ w : B.JacquetModule ρ, w ≠ 0 ∧
          ∀ a : Fin B.length → F.Carrierˣ,
            T.splitCentreJacquet B ρ a w = (χ a : ℂ) • w

end Langlands
