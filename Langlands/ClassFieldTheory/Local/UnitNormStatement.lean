import Langlands.ClassFieldTheory.Local.Units
import Langlands.ClassFieldTheory.Local.Norms
import Langlands.HarmonicAnalysis.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

/-!
# Unit norms and unramified character quotients

These are proposition definitions on the published unit filtrations and
determinant norms. Equality of the absolute ramification indices is the
unramified condition for the compatible finite p-adic extension.
-/

namespace Langlands.LocalClassField

universe u v

/-- An unramified extension maps every actual unit-congruence group onto
the group with the same index, including the full unit group at index zero. -/
def UnramifiedUnitNorms : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    T.ramificationIndex = S.ramificationIndex →
      ∀ n : ℕ,
        (S.unitFiltration n).map (normUnits F.Carrier E.Carrier) = T.unitFiltration n

/-- In an unramified extension the full norm subgroup consists exactly of
elements whose normalized order is divisible by the extension degree. -/
def UnramifiedNormMembership : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    T.ramificationIndex = S.ramificationIndex →
      ∀ a : F.Carrierˣ,
        a ∈ normSubgroup F.Carrier E.Carrier ↔
          (Module.finrank F.Carrier E.Carrier : ℤ) ∣ T.ord (a : F.Carrier)

/-- The order modulo the degree induces the specified topological cyclic
norm quotient. Only the finite cyclic target receives its discrete topology. -/
def UnramifiedCyclicNormQuotient : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    T.ramificationIndex = S.ramificationIndex →
      letI := T.topology
      let d := Module.finrank F.Carrier E.Carrier
      letI : TopologicalSpace (Multiplicative (ZMod d)) := ⊥
      ∃ e : NormQuotient F.Carrier E.Carrier ≃ₜ* Multiplicative (ZMod d),
        ∀ a : F.Carrierˣ,
          e (normQuotientProjection F.Carrier E.Carrier a) =
            Multiplicative.ofAdd (T.ord (a : F.Carrier) : ZMod d)

/-- A continuous quasicharacter trivial on the unramified norm subgroup
is uniquely an integer-order character with a degree-th root of unity as
parameter. No finite-image or unitarity hypothesis is imposed on the input. -/
def UnramifiedNormCharacterCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    T.ramificationIndex = S.ramificationIndex →
      letI := T.topology
      ∀ χ : HarmonicAnalysis.Quasicharacter F.Carrier,
        (∀ b : E.Carrierˣ, χ (normUnits F.Carrier E.Carrier b) = 1) ↔
          ∃! z : ℂˣ,
            z ^ Module.finrank F.Carrier E.Carrier = 1 ∧
              ∀ a : F.Carrierˣ, χ a = z ^ T.ord (a : F.Carrier)

/-- For a finite abelian extension, the index of the norm subgroup inside
the valuation-unit group is the relative ramification index. Multiplying
by the base absolute index avoids a division convention. -/
def AbelianUnitNormIndex : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    ((normSubgroup F.Carrier E.Carrier).comap T.unitSubgroup.subtype).index *
      T.ramificationIndex = S.ramificationIndex

/-- Local unit-norm consequences, the unramified cyclic norm quotient,
and its complex quasicharacters, for every finite p-adic field. -/
def UnitNormTheorems : Prop :=
  UnramifiedUnitNorms.{u, v} ∧
    UnramifiedNormMembership.{u, v} ∧
      UnramifiedCyclicNormQuotient.{u, v} ∧
        UnramifiedNormCharacterCriterion.{u, v} ∧
          AbelianUnitNormIndex.{u, v}

end Langlands.LocalClassField
