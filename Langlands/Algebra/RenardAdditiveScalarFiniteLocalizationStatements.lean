import Langlands.Algebra.RenardStableIdealFiniteLocalizationStatements

/-!
# From additive stable generation to scalar-linear finite localization

Internal comparison targets motivated by the nonunital conventions and final
C.II proposition of Renard 2026. Only the additive-to-scalar implications are
asserted; no source convention or converse is selected.
-/

set_option autoImplicit false

namespace Langlands.Algebra.AdditiveScalarStableGeneration

universe uR uA uM

/-- Finite generation among all stable additive subgroups implies finite
generation among scalar-linear stable subspaces of the same action. -/
def ModuleGenerationComparisonStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA) (M : Type uM)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M]
    (ρ : A →ₙₐ[R] Module.End R M),
    (∃ S : Finset M, ∀ P : AddSubgroup M,
      (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
      (↑S : Set M) ⊆ P → P = ⊤) →
    ∃ S : Finset M, ∀ P : Submodule R M,
      (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
      (↑S : Set M) ⊆ P → P = ⊤

/-- Finite stable generation of every additive stable subgroup implies
finite stable generation of every scalar-linear stable subspace. -/
def SubmoduleGenerationComparisonStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA) (M : Type uM)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M]
    (ρ : A →ₙₐ[R] Module.End R M),
    (∀ P : AddSubgroup M,
      (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : AddSubgroup M,
          (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
          (↑S : Set M) ⊆ Q → P ≤ Q) →
    ∀ P : Submodule R M,
      (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : Submodule R M,
          (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
          (↑S : Set M) ⊆ Q → P ≤ Q

end Langlands.Algebra.AdditiveScalarStableGeneration

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Actual localization stabilizes under finite stable generation of all
additive left ideals, the source, and its actual localized action. -/
def AdditiveIdealFiniteLocalizationStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ),
    (∀ P : AddSubgroup B,
      (∀ b x : B, x ∈ P → b * x ∈ P) →
      ∃ S : Finset B, (↑S : Set B) ⊆ P ∧
        ∀ Q : AddSubgroup B,
          (∀ b x : B, x ∈ Q → b * x ∈ Q) →
          (↑S : Set B) ⊆ Q → P ≤ Q) →
    (∃ S : Finset V, ∀ P : AddSubgroup V,
      (∀ (b : B) (v : V), v ∈ P → ρ b v ∈ P) →
      (↑S : Set V) ⊆ P → P = ⊤) →
    (let a := f.toLinearMap
     let σ := localizedAction a ρ (fun b v => f.map_action' b v)
     ∃ S : Finset (Localized a), ∀ P : AddSubgroup (Localized a),
       (∀ (b : B) (v : Localized a), v ∈ P → σ b v ∈ P) →
       (↑S : Set (Localized a)) ⊆ P → P = ⊤) →
    CompatibleLocalizationStabilizationAt ρ f ∧
      ∀ n : ℕ, 0 < n → Stable (f.toLinearMap ^ n) →
        CompatibleStablePowerImageAt ρ f n

end Langlands.Renard.AlgebraActionLocalization

namespace Langlands.Renard

universe uR uB uV

/-- The two additive-to-scalar generation implications and the actual
complex localization consequence, with independent universes. -/
def AdditiveScalarFiniteLocalizationStatement : Prop :=
  Langlands.Algebra.AdditiveScalarStableGeneration.ModuleGenerationComparisonStatement.{uR, uB, uV} ∧
    Langlands.Algebra.AdditiveScalarStableGeneration.SubmoduleGenerationComparisonStatement.{uR, uB, uV} ∧
    AlgebraActionLocalization.AdditiveIdealFiniteLocalizationStatement.{uB, uV}

end Langlands.Renard
