import Langlands.Representation.Smooth.FixedVectors.LengthCriterionStatement
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Bases.Basic

/-!
# Refined common fixed generators

Internal targets for choosing common fixed generators inside a prescribed
neighborhood, either normal in a supplied compact open subgroup or in a
supplied subgroup neighborhood basis.
-/

set_option autoImplicit false

noncomputable section

open Topology

namespace Langlands

/-- Finite smooth generators can be fixed by an arbitrarily small compact open
subgroup contained and normal in the same supplied compact open subgroup. -/
def CommonCompactOpenNormalGeneratorsStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] (V : Type uV) [AddCommGroup V] [Module R V]
    (ρ : Representation R G V),
    IsSmooth ρ → Module.Finite (MonoidAlgebra R G) ρ.asModule →
      ∀ (K₀ : OpenSubgroup G), IsCompact (K₀ : Set G) →
        ∀ U ∈ 𝓝 (1 : G),
          ∃ (n : ℕ) (v : Fin n → V) (K : OpenSubgroup G),
            IsCompact (K : Set G) ∧ K ≤ K₀ ∧
            (K.toSubgroup.subgroupOf K₀.toSubgroup).Normal ∧
            (K : Set G) ⊆ U ∧
            Submodule.span (MonoidAlgebra R G)
              (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤ ∧
            (∀ i, v i ∈ fixedVectors ρ K.toSubgroup) ∧
            ∀ (L : Subgroup G), L ≤ K.toSubgroup →
              ∀ S : Subrepresentation ρ, fixedVectors ρ L ≤ S.toSubmodule → S = ⊤

/-- A supplied subgroup neighborhood basis contains an arbitrarily small member
fixing a finite generating family. The chosen subgroup retains membership in
that same basis. -/
def CommonBasisFixedGeneratorsStatement.{uR, uG, uV} : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
    (V : Type uV) [AddCommGroup V] [Module R V] (ρ : Representation R G V),
    IsSmooth ρ → Module.Finite (MonoidAlgebra R G) ρ.asModule →
      ∀ (B : Set (Subgroup G)),
        (𝓝 (1 : G)).HasBasis (fun K : Subgroup G => K ∈ B) (fun K => (K : Set G)) →
        ∀ U ∈ 𝓝 (1 : G),
          ∃ (n : ℕ) (v : Fin n → V) (K : Subgroup G),
            K ∈ B ∧ (K : Set G) ⊆ U ∧
            Submodule.span (MonoidAlgebra R G)
              (Set.range (fun i => ρ.asModuleEquiv.symm (v i))) = ⊤ ∧
            (∀ i, v i ∈ fixedVectors ρ K) ∧
            ∀ (L : Subgroup G), L ≤ K →
              ∀ S : Subrepresentation ρ, fixedVectors ρ L ≤ S.toSubmodule → S = ⊤

/-- The compact-open normal refinement and the supplied-basis selection, with
independent coefficient, group, and carrier universes. -/
def RefinedFixedGeneratorsStatement.{uR, uG, uV} : Prop :=
  CommonCompactOpenNormalGeneratorsStatement.{uR, uG, uV} ∧
    CommonBasisFixedGeneratorsStatement.{uR, uG, uV}

end Langlands
