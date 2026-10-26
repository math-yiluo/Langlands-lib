import Langlands.Representation.Filtration.MultiplicityStatement

/-! Additive multiplicities for actual finite filtrations and exact sequences.
These proposition definitions state claims; they do not prove them. -/

open scoped BigOperators

namespace Langlands

universe uK uG uA uB uC uT

/-- Actual composition series of all graded pieces refine to an actual
composition series of the ambient representation, with summed length and
summed multiplicity of the specified representation. -/
def JordanHolderFiltrationAdditivityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (τ : Rep.{uT} k G) (n : ℕ)
    (s : ObjectRepFiltration A n) (lengths counts : Fin n → ℕ),
    (∀ i : Fin n,
      ∃ t : ObjectRepFiltration (s.gradedRepresentation i) (lengths i),
        t.HasSimpleFactors ∧ t.factorMultiplicity τ = counts i) →
    ∃ t : ObjectRepFiltration A (∑ i : Fin n, lengths i),
      t.HasSimpleFactors ∧ t.factorMultiplicity τ = ∑ i : Fin n, counts i

/-- Every supplied finite invariant filtration of a representation with an
actual finite composition series admits graded composition series whose
lengths and multiplicities sum to the specified ambient length and count. -/
def JordanHolderFiltrationDecompositionStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (τ : Rep.{uT} k G) (N M n : ℕ),
    HasCompositionSeriesLength A N →
    HasJordanHolderMultiplicity A τ M →
    ∀ s : ObjectRepFiltration A n,
      ∃ lengths counts : Fin n → ℕ,
        (∀ i : Fin n,
          ∃ t : ObjectRepFiltration (s.gradedRepresentation i) (lengths i),
            t.HasSimpleFactors ∧ t.factorMultiplicity τ = counts i) ∧
        (∑ i : Fin n, lengths i) = N ∧
        (∑ i : Fin n, counts i) = M

/-- An actual short exact sequence with finite-series witnesses for the
outer representations gives a finite-series witness for the middle one,
with multiplicity equal to the sum of the two supplied counts. -/
def JordanHolderShortExactAdditivityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (C : Rep.{uC} k G)
    (τ : Rep.{uT} k G)
    (i : A.ρ.IntertwiningMap B.ρ) (q : B.ρ.IntertwiningMap C.ρ),
    Function.Injective i →
    Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    ∀ mA mC : ℕ,
      HasJordanHolderMultiplicity A τ mA →
      HasJordanHolderMultiplicity C τ mC →
      HasJordanHolderMultiplicity B τ (mA + mC)

/-- A finite-series witness for the middle representation of an actual
short exact sequence supplies finite-series witnesses for both outer
representations, with counts summing to the supplied middle count. -/
def JordanHolderShortExactDecompositionStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (C : Rep.{uC} k G)
    (τ : Rep.{uT} k G)
    (i : A.ρ.IntertwiningMap B.ρ) (q : B.ρ.IntertwiningMap C.ρ),
    Function.Injective i →
    Function.Surjective q →
    LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap →
    ∀ mB : ℕ,
      HasJordanHolderMultiplicity B τ mB →
      ∃ mA mC : ℕ,
        HasJordanHolderMultiplicity A τ mA ∧
        HasJordanHolderMultiplicity C τ mC ∧
        mA + mC = mB

/-- Supplied finite composition-series multiplicities are monotone along
an actual injective intertwiner. -/
def JordanHolderInjectiveMonotonicityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (τ : Rep.{uT} k G)
    (i : A.ρ.IntertwiningMap B.ρ),
    Function.Injective i →
    ∀ mA mB : ℕ,
      HasJordanHolderMultiplicity A τ mA →
      HasJordanHolderMultiplicity B τ mB →
      mA ≤ mB

/-- Supplied finite composition-series multiplicities are monotone along
an actual surjective intertwiner. -/
def JordanHolderSurjectiveMonotonicityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (τ : Rep.{uT} k G)
    (q : A.ρ.IntertwiningMap B.ρ),
    Function.Surjective q →
    ∀ mA mB : ℕ,
      HasJordanHolderMultiplicity A τ mA →
      HasJordanHolderMultiplicity B τ mB →
      mB ≤ mA

/-- Multiplicities add in the actual binary product representation, whose
carrier lies in the maximum of the two independent carrier universes. -/
def JordanHolderProductAdditivityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (τ : Rep.{uT} k G)
    (mA mB : ℕ),
    HasJordanHolderMultiplicity A τ mA →
    HasJordanHolderMultiplicity B τ mB →
    HasJordanHolderMultiplicity (Rep.of (A.ρ.prod B.ρ)) τ (mA + mB)

/-- The additive Jordan–Hölder multiplicity family. Each clause retains
actual composition-series witnesses and actual maps. -/
def JordanHolderMultiplicityAdditivityStatement : Prop :=
  JordanHolderFiltrationAdditivityStatement.{uK, uG, uA, uT} ∧
  JordanHolderFiltrationDecompositionStatement.{uK, uG, uA, uT} ∧
  JordanHolderShortExactAdditivityStatement.{uK, uG, uA, uB, uC, uT} ∧
  JordanHolderShortExactDecompositionStatement.{uK, uG, uA, uB, uC, uT} ∧
  JordanHolderInjectiveMonotonicityStatement.{uK, uG, uA, uB, uT} ∧
  JordanHolderSurjectiveMonotonicityStatement.{uK, uG, uA, uB, uT} ∧
  JordanHolderProductAdditivityStatement.{uK, uG, uA, uB, uT}

end Langlands
