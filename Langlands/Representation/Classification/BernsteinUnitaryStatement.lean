import Langlands.Representation.Classification.Segments
import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeOrder
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Unitary.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Bernstein's unitary product and shifted highest-derivative theorems

The three parts of Bernstein's theorem on unitary representations of `GL_n`
over a p-adic field, in the form used as Tadic 1986, Theorem 2.5: irreducibility
and unitarizability of normalized products of irreducible unitarizable blocks,
unitarizability of Hermitian irreducible factors of an irreducible unitarizable
product, and irreducibility and unitarizability of the shifted highest
derivative `ν^(1/2) π^(h)`. All assertions are proposition definitions; none is
proved here.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear HarmonicAnalysis

universe uF uV

section Hermitian

variable {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `ρ` admits a nonzero invariant sesquilinear form, conjugate-linear in the
first and linear in the second variable. For irreducible admissible `ρ` this is
Tadic's Hermitian condition `ρ ≅ ρ^+`, in the convention of
`Langlands.UnitarizabilityContinuationStatement`. -/
def HasNonzeroInvariantSesquilinearForm (ρ : Representation ℂ G V) : Prop :=
  ∃ b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, b ≠ 0 ∧ ∀ (g : G) (v w : V), b (ρ g v) (ρ g w) = b v w

end Hermitian

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Tadic 1986, Theorem 2.5(i) (Bernstein 1984, Corollary 8.2(a)), for a finite
family: the entire normalized product of irreducible unitarizable blocks is
irreducible and unitarizable. -/
def BernsteinUnitaryProductIrreducibility : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      IsUnitarizable (σ i).representation) →
      Representation.IsIrreducible
          ((T.normalizedProductInductionFunctor B).obj σ).representation ∧
        IsUnitarizable ((T.normalizedProductInductionFunctor B).obj σ).representation

/-- The weak form of Tadic 1986, Theorem 2.5(ii) used by Tadic, for a finite
family: if every block is irreducible and admits a nonzero invariant
sesquilinear form, and the entire normalized product is irreducible and
unitarizable, then every block is unitarizable. -/
def BernsteinUnitaryProductFactorUnitarity : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape n)
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
    (∀ i, Representation.IsIrreducible (σ i).representation ∧
      HasNonzeroInvariantSesquilinearForm (σ i).representation) →
    Representation.IsIrreducible
        ((T.normalizedProductInductionFunctor B).obj σ).representation →
    IsUnitarizable ((T.normalizedProductInductionFunctor B).obj σ).representation →
      ∀ i, IsUnitarizable (σ i).representation

/-- The shifted highest derivative `ν^(1/2) π^(h)` on `GL_(N - h)`, where
`h` is the highest positive order recorded by `hd` and `π^(h)` is the actual
Bernstein-Zelevinsky derivative. -/
abbrev shiftedHighestDerivative {N : ℕ}
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ π) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N - hd.order) F.Carrier) :=
  T.segmentFactor
    ((Derivative.generalLinearDerivative T ψ N hd.order hd.le_rank).obj π) (1 / 2)

/-- Tadic 1986, Theorem 2.5(iii) with §1.16 (Bernstein 1984, §7.2, §7.4 and
§8): for an irreducible unitarizable representation `π` of `GL_N`, `N ≥ 1`,
the shifted highest derivative `ν^(1/2) π^(h)` is irreducible and
unitarizable. -/
def BernsteinShiftedHighestDerivativeUnitarity : Prop :=
  letI := T.topology
  ∀ (N : ℕ), 0 < N →
    ∀ (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
      Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
        ∀ hd : Derivative.GeneralLinearHighestDerivativeOrderData T ψ π,
          Representation.IsIrreducible (shiftedHighestDerivative F T ψ hd).representation ∧
            IsUnitarizable (shiftedHighestDerivative F T ψ hd).representation

/-- The three parts of Bernstein's theorem as Tadic 1986, Theorem 2.5 uses them. -/
def BernsteinUnitaryStatements : Prop :=
  BernsteinUnitaryProductIrreducibility.{uF, uV} F T ∧
    BernsteinUnitaryProductFactorUnitarity.{uF, uV} F T ∧
    BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T

end Langlands.Classification
