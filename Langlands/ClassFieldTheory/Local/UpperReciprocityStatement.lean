import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
import Langlands.ClassFieldTheory.Local.Units
import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Langlands.HarmonicAnalysis.Conductor

/-!
# Higher unit images and upper ramification under local reciprocity

These proposition definitions use the actual Herbrand inverse and upper
groups. No ramification or conductor compatibility is assumed by the
normalized reciprocity relation.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- At every nonnegative integer, reciprocity takes the actual unit
congruence subgroup onto the upper-numbered ramification group. -/
def FiniteReciprocityHigherUnitImages : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          ∀ n : ℕ,
            (T.unitFiltration n).map (finiteFamilyOfHom r L).toMonoidHom =
              Ramification.Padic.upperRamificationGroup S F.Carrier n

/-- In a finite abelian extension, integral upper breaks extend the integer
unit-image formula to real nonnegative indices using the ceiling convention. -/
def FiniteReciprocityRealUnitImages : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          ∀ v : ℝ, 0 ≤ v →
            (T.unitFiltration ⌈v⌉₊).map (finiteFamilyOfHom r L).toMonoidHom =
              Ramification.Padic.upperRamificationGroup S F.Carrier v

/-- A unit level lies in the actual field norm image exactly when the
corresponding upper ramification group is trivial. This assertion is
unconditional on any supplied reciprocity map. -/
def FiniteAbelianNormUpperLevels : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (L : LocalFiniteAbelianExtension F)
    (S : (L.asPadicField (p := p)).TopologicalData),
    letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
      inferInstanceAs (Algebra F.Carrier L.field)
    letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
      inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
    ∀ n : ℕ,
      T.unitFiltration n ≤ normSubgroup F.Carrier L.field ↔
        Ramification.Padic.upperRamificationGroup S F.Carrier n = ⊥

/-- Triviality of a finite character on an upper group is measured by the
existing least principal-unit conductor, including the level-zero endpoint. -/
def FiniteCharacterUpperConductorLevels : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData)
          (χ : L.galoisGroup →ₜ* ℂˣ),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          ∀ v : ℝ, 0 ≤ v →
            (T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) ≤ ⌈v⌉₊ ↔
              ∀ σ ∈ Ramification.Padic.upperRamificationGroup S F.Carrier v,
                χ σ = 1)

/-- A positive conductor is one plus the last upper level on which the
character is nontrivial. The right-hand condition uses all real later levels;
it also handles tame ramification at break zero. -/
def FiniteCharacterLastUpperBreak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier,
      GeometricProfiniteReciprocityRelation F T r →
        ∀ (L : LocalFiniteAbelianExtension F)
          (S : (L.asPadicField (p := p)).TopologicalData)
          (χ : L.galoisGroup →ₜ* ℂˣ),
          letI : Algebra F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (Algebra F.Carrier L.field)
          letI : IsScalarTower (Padic p) F.Carrier (L.asPadicField (p := p)).Carrier :=
            inferInstanceAs (IsScalarTower (Padic p) F.Carrier L.field)
          ∀ n : ℕ,
            (T.multiplicativeConductor (χ.comp (finiteFamilyOfHom r L)) = n + 1 ↔
              (∃ σ ∈ Ramification.Padic.upperRamificationGroup S F.Carrier n,
                χ σ ≠ 1) ∧
              ∀ v : ℝ, (n : ℝ) < v →
                ∀ σ ∈ Ramification.Padic.upperRamificationGroup S F.Carrier v,
                  χ σ = 1)

/-- The finite upper-numbering part of local reciprocity, norm filtrations
and finite-character conductor breaks. -/
def FiniteUpperReciprocityTheorems : Prop :=
  FiniteReciprocityHigherUnitImages.{u} ∧
    FiniteReciprocityRealUnitImages.{u} ∧
      FiniteAbelianNormUpperLevels.{u} ∧
        FiniteCharacterUpperConductorLevels.{u} ∧
          FiniteCharacterLastUpperBreak.{u}

end Langlands.LocalClassField
