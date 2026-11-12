import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.SubrepresentationLattice
import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Multiplicities for compact groups and independence of compact coefficients
(Renard IV.1.1 and IV.3.3)

For a compact t.d. group `K`, a smooth representation `V` and an irreducible smooth `σ`, if the
multiplicity `m(σ) = dim Hom_K(V_σ, V)` is finite, then `dim V(σ) = m(σ) dim V_σ` (IV.1.1). For a
unimodular t.d. group countable at infinity, matrix coefficients of pairwise non-isomorphic
irreducible compact representations, with nonzero vectors and smooth functionals, are linearly
independent (IV.3.3, Corollary, last sentence).
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Renard.CompactRepresentation

/-- Renard IV.1.1, sentence after the Corollary: let `K` be a compact, Hausdorff, totally
disconnected topological group, `π` a smooth complex representation of `K` and `σ` an irreducible
smooth complex representation of `K`. Let `V(σ)` be the sum of the images of all intertwiners
`σ → π`, the image of `Hom_K(V_σ, V) ⊗ V_σ → V`. If the multiplicity
`m(σ) = dim Hom_K(V_σ, V)` is finite, then `V(σ)` is finite-dimensional and
`dim V(σ) = m(σ) · dim V_σ`, that is `m(σ) = dim V(σ) / dim V_σ`. -/
def CompactGroupMultiplicityStatement : Prop :=
  ∀ (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [T2Space K] [TotallyDisconnectedSpace K] (π σ : SmoothRep.{0, u, v} ℂ K),
    σ.IsIrreducible →
    FiniteDimensional ℂ (σ.representation.IntertwiningMap π.representation) →
      let isotypic : Subrepresentation π.representation :=
        ⨆ f : σ.representation.IntertwiningMap π.representation, f.range
      FiniteDimensional ℂ isotypic.toSubmodule ∧
        Module.finrank ℂ isotypic.toSubmodule =
          Module.finrank ℂ (σ.representation.IntertwiningMap π.representation) *
            Module.finrank ℂ σ

/-- Renard IV.3.3, Corollary, last sentence: let `G` be a Hausdorff, locally compact, totally
disconnected group, countable at infinity, with a regular Haar measure that is also right
invariant (`G` is unimodular). For pairwise non-isomorphic irreducible smooth representations
`π₁, …, π_r` with compactly supported smooth coefficients, nonzero vectors `xᵢ ∈ πᵢ` and nonzero
smooth functionals `ℓᵢ` on `πᵢ`, the matrix coefficients `g ↦ ℓᵢ(πᵢ(g) xᵢ)` are linearly
independent functions on `G`. -/
def CompactCoefficientLinearIndependenceStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    [μ.IsMulRightInvariant] (r : ℕ) (π : Fin r → SmoothRep.{0, u, v} ℂ G),
    (∀ i, (π i).IsIrreducible) →
    (∀ i, HasCompactSmoothDualCoefficients (π i).representation) →
    (∀ i j, i ≠ j → IsEmpty (π i ≅ π j)) →
    ∀ (x : ∀ i, π i) (ℓ : ∀ i, SmoothDual (π i).representation),
      (∀ i, x i ≠ 0) → (∀ i, ℓ i ≠ 0) →
      LinearIndependent ℂ (fun i => matrixCoefficient (π i).representation (ℓ i) (x i))

/-- Renard IV.1.1 and IV.3.3: the conjunction of the two statements above. -/
def CompactMultiplicityIndependenceStatements : Prop :=
  CompactGroupMultiplicityStatement.{u, v} ∧ CompactCoefficientLinearIndependenceStatement.{u, v}

end Langlands.Renard.CompactRepresentation
