import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Dual.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.LocallyConstant.Basic

/-! # Translation, naturality, and smoothness of matrix coefficients -/

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Right translation acts on the vector; left translation acts by the
inverse element on the dual functional. -/
def MatrixCoefficientTranslationStatement : Prop :=
  ∀ (ρ : Representation R G V) (ℓ : Module.Dual R V) (v : V) (g h : G),
    matrixCoefficient ρ ℓ v (g * h) = matrixCoefficient ρ ℓ (ρ h v) g ∧
    matrixCoefficient ρ ℓ v (h * g) = matrixCoefficient ρ (ρ.dual h⁻¹ ℓ) v g

/-- Intertwiners transport matrix coefficients by pullback of functionals. -/
def MatrixCoefficientNaturalityStatement : Prop :=
  ∀ (ρ : Representation R G V) (σ : Representation R G W)
    (f : ρ.IntertwiningMap σ) (ℓ : Module.Dual R W) (v : V),
    matrixCoefficient σ ℓ (f v) = matrixCoefficient ρ (dualIntertwining f ℓ) v

/-- Smooth vectors in both factors give one open subgroup fixing the
coefficient under both left and right multiplication. -/
def MatrixCoefficientBiInvariantStatement : Prop :=
  ∀ [TopologicalSpace G] (ρ : Representation R G V) (ℓ : Module.Dual R V) (v : V),
    IsSmoothVector ρ.dual ℓ → IsSmoothVector ρ v →
      ∃ K : OpenSubgroup G, ∀ (k : K) (l : K) (g : G),
        matrixCoefficient ρ ℓ v ((k : G) * g * (l : G)) = matrixCoefficient ρ ℓ v g

/-- A smooth vector gives locally constant coefficients against every
algebraic functional when the acting group is a topological group. -/
def MatrixCoefficientLocallyConstantStatement : Prop :=
  ∀ [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation R G V) (ℓ : Module.Dual R V) (v : V),
    IsSmoothVector ρ v → IsLocallyConstant (matrixCoefficient ρ ℓ v)

/-- A coherent matrix-coefficient interface, with topological assumptions
quantified only inside the clauses that use them. -/
def MatrixCoefficientLawsStatement : Prop :=
  MatrixCoefficientTranslationStatement (R := R) (G := G) (V := V) ∧
  MatrixCoefficientNaturalityStatement (R := R) (G := G) (V := V) (W := W) ∧
  MatrixCoefficientBiInvariantStatement (R := R) (G := G) (V := V) ∧
  MatrixCoefficientLocallyConstantStatement (R := R) (G := G) (V := V)

end Langlands
