import Langlands.Representation.Classification.RelativeGenericityStatement
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Twist.LeviRealPower
import Langlands.Representation.Unitary.Basic

/-!
# Generic relative Jacquet comparison and irreducible heads

Derived GL_n forms of the constituent-restricted argument in Silberger 1978,
Lemma 5.3, and the generic head argument in Lemma 5.5. These are statements,
not proofs; the all-regular tempered continuation is separate.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW

namespace RelativeJacquetMultiplicity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Actual fine determinant twist, transported through the constructed flattened
Levi equivalence to the common refined subgroup. -/
def fineTwist (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ) :
    Rep.{uV} ℂ (refinedLevi F.Carrier B S) :=
  Rep.of ((T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ).comp
      (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom)

/-- The actual normalized induction from the refined subgroup to the coarse Levi. -/
def innerInduced (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S)) :
    Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
  letI := T.topology
  letI := T.leviTopologicalGroup B
  Rep.of (T.normalizedRefinedInduced B S τ.ρ)

/-- Opposite normalized Jacquet inside the coarse Levi, on its actual coinvariants. -/
def innerJacquet (μ : Rep.{uW} ℂ (B.Levi F.Carrier)) :
    Rep.{uW} ℂ (refinedLevi F.Carrier B S) :=
  Rep.of (T.normalizedRefinedOppositeJacquet B S μ.ρ)

/-- Opposite normalized Jacquet of the actual outer induction, with the same
refined Levi as the inner Jacquet module. -/
def ambientJacquet (μ : Rep.{uW} ℂ (B.Levi F.Carrier)) :
    Rep.{max uF uW} ℂ (refinedLevi F.Carrier B S) :=
  Rep.of (T.normalizedComposedOppositeJacquet B S
    (CuspidalJacquetMultiplicity.induced T B μ).ρ)

end RelativeJacquetMultiplicity

open RelativeJacquetMultiplicity

/-- Generic comparison for actual irreducible constituents of the specified
inner induction, including the criterion for the common multiplicity to be positive. -/
def GLRelativeGenericJacquetMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        IsRelativeGenericParameter (B.flatten S) B v₀ t →
        let τ := fineTwist T B S ω v₀ t
        let I := innerInduced T B S τ
        ∀ μ : Rep.{uW} ℂ (B.Levi F.Carrier),
          Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
          (∃ U : Subrepresentation I.ρ,
            ∃ q : U.toRepresentation.IntertwiningMap μ.ρ, Function.Surjective q) →
          ∃ m : ℕ,
            HasJordanHolderMultiplicity (innerJacquet T B S μ) τ m ∧
            HasJordanHolderMultiplicity (ambientJacquet T B S μ) τ m ∧
            (0 < m ↔ ∃ q : I.ρ.IntertwiningMap μ.ρ, Function.Surjective q)

/-- An irreducible quotient of the specified generic inner induction induces
an outer representation with an irreducible head, including uniqueness of all
irreducible quotient kernels. -/
def GLRelativeGenericHeadStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        IsRelativeGenericParameter (B.flatten S) B v₀ t →
        let τ := fineTwist T B S ω v₀ t
        let I := innerInduced T B S τ
        ∀ μ : Rep.{uW} ℂ (B.Levi F.Carrier),
          Representation.IsIrreducible μ.ρ → IsAdmissible μ.ρ →
          (∃ q : I.ρ.IntertwiningMap μ.ρ, Function.Surjective q) →
          Classification.HasIrreducibleHead (CuspidalJacquetMultiplicity.induced T B μ).ρ

/-- The generic constituent comparison and its head consequence as one family. -/
def GLRelativeGenericComparisonStatement : Prop :=
  GLRelativeGenericJacquetMultiplicityStatement.{uF, uV, uW} ∧
    GLRelativeGenericHeadStatement.{uF, uV, uW}

end Langlands
